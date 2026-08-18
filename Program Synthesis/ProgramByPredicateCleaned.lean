module

public meta import ProgramByExample

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.PBP

public meta section

/-! # Programming by predicate

Machinery for synthesis from `∀ x₁ … xₙ, f a₁ … aₘ = b` predicate clauses,
driven by the `synthesize` tactic. Each predicate is instantiated with concrete
example inputs — themselves enumerated by Canonical, using its `count` option
on the binder types and the resulting ground equations become equational
constraints on the declaration under synthesis. The predicates
themselves are only sampled, not verified. See `ProgramByPredicate.md` for
the design. -/

/-! ## Term enumeration

We use Canonical with `count := k` to enumerate the first `k` distinct
inhabitants, which we use as example inputs for the quantified variables. -/

/-- Run Canonical on `type`, returning the first `count` inhabitants in
    search order. -/
def enumerate (type : Lean.Expr) (count : Nat) (timeout : UInt64 := 5) :
    MetaM (Array Lean.Expr) := do
  let config : Config := { count := USize.ofNat count, destruct := false, simp := false, recs := false }
  let typ ← toCanonical type #[] #[] config
  let result ← runCanonical { name := "enumerate", type := some typ } timeout config
  result.terms.mapM fun term => do instantiateMVars (← fromCanonical term type)

/-- Cartesian product of heterogeneous term lists; the last index varies fastest. -/
partial def allHeteroTuples (termLists : Array (Array Lean.Expr)) : Array (Array Lean.Expr) :=
  if termLists.isEmpty then #[]
  else if termLists.size == 1 then termLists[0]!.map (#[·])
  else
    let sub := allHeteroTuples (termLists.extract 1 termLists.size)
    termLists[0]!.flatMap fun t => sub.map (#[t] ++ ·)

def cartesianSize (termLists : Array (Array Lean.Expr)) : Nat :=
  termLists.foldl (fun acc ts => acc * ts.size) 1

/-- Smallest `m` with `m ^ dim ≥ k` (uniform enumeration bound per dimension). -/
partial def minTermCount (k dim : Nat) : Nat :=
  if k == 0 then 0
  else if dim == 0 then k
  else
    let rec go (m : Nat) : Nat := if m ^ dim ≥ k then m else go (m + 1)
    go 1

/-- Enumerate enough terms of each type to form at least `k` tuples, growing
    the per-type counts until the cartesian product is large enough (or no
    type yields further terms). -/
def gatherTerms (types : Array Lean.Expr) (k : Nat)
    (timeout : UInt64 := 5) : MetaM (Array (Array Lean.Expr)) := do
  if types.isEmpty then return #[]
  let dim := types.size
  if dim == 1 then
    return #[← enumerate types[0]! k timeout]
  let mut counts := Array.replicate dim (minTermCount k dim)
  let mut termLists ← types.mapIdxM fun i ty => enumerate ty counts[i]! timeout
  while cartesianSize termLists < k do
    let mut grown := false
    for i in [0:dim] do
      if termLists[i]!.size == counts[i]! then
        counts := counts.set! i (counts[i]! + 1)
        grown := true
    if !grown then break
    termLists ← types.mapIdxM fun i ty => enumerate ty counts[i]! timeout
  return termLists

/-- Enumerate the first `k` example assignments for heterogeneous quantified
    variables; each inner array is one assignment in binder order. An empty
    `types` yields the single empty assignment. -/
def enumerateInputs (types : Array Lean.Expr) (k : Nat)
    (timeout : UInt64 := 5) : MetaM (Array (Array Lean.Expr)) := do
  if k == 0 then return #[]
  if types.isEmpty then return #[#[]]
  let termLists ← gatherTerms types k timeout
  if termLists.any (·.isEmpty) then return #[]
  return (allHeteroTuples termLists).take k

/-! ## Predicate instantiation -/

/-- Split a predicate into the types of its leading `∀` binders and the body
    that remains, which still refers to the binders by loose bvars. -/
def binderTypesAndBody : Lean.Expr → Array Lean.Expr × Lean.Expr :=
  go #[]
where
  go (types : Array Lean.Expr) : Lean.Expr → Array Lean.Expr × Lean.Expr
  | .forallE _ binderType body _ => go (types.push binderType) body
  | body => (types, body)

/-- Convert `Nat` literals produced by reduction into constructor form, so the
    logged examples and the defeq re-checks match what the solver computes
    with. This form does not survive translation — the `whnf` in `toTerm`
    collapses the chains back into literals — so the spines that actually
    reach the solver are re-expanded afterwards, in `PBE.toProblem_`. -/
partial def natLitToCtor : Lean.Expr → Lean.Expr
  | .lit (.natVal n) => if n ≤ PBE.MAX_CTOR_NAT then rawRawNatLit n else .lit (.natVal n)
  | .app fn arg => .app (natLitToCtor fn) (natLitToCtor arg)
  | e => e

/-- Evaluate the ground parts of an instantiated example: a subterm that does
    not mention `f` and is either a whole side of the equation or a direct
    argument of `f` is reduced to normal form (so `pred (1 + 1) = 1` becomes
    `pred 2 = 1`), with `Nat` literals converted to constructor form.
    Subterms under other heads are left to the usual translation. -/
partial def reduceGround (f : Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
  if !e.containsFVar f.fvarId! then
    return natLitToCtor (← Meta.reduce e (skipTypes := true) (skipProofs := true))
  else
    e.withApp fun fn args => do
      if fn == f then
        return mkAppN fn (← args.mapM (reduceGround f))
      else
        return mkAppN fn (← args.mapM fun arg =>
          if arg.containsFVar f.fvarId! then reduceGround f arg else pure arg)

/-- Apply `reduceGround` to both sides of an instantiated example equation. -/
def reduceGroundEq (f e : Lean.Expr) : MetaM Lean.Expr := do
  let some (α, lhs, rhs) := e.eq? | return e
  return mkApp3 e.getAppFn α (← reduceGround f lhs) (← reduceGround f rhs)

/-- Drop instantiated examples that are syntactically trivial (`a = a`) or
    duplicates of an earlier example, up to symmetry of the equation — from
    `∀ n m, f n m = f m n` both `f 0 1 = f 1 0` and its mirror image are
    generated, and keeping both would orient a rewrite loop. -/
def dedupExamples (examples : Array Lean.Expr) : Array Lean.Expr := Id.run do
  let mut seen : Array (Lean.Expr × Lean.Expr) := #[]
  let mut out := #[]
  for e in examples do
    let some (_, lhs, rhs) := e.eq? | continue
    if lhs == rhs then
      continue
    if seen.any fun (l, r) => (l == lhs && r == rhs) || (l == rhs && r == lhs) then
      continue
    seen := seen.push (lhs, rhs)
    out := out.push e
  return out

/-! ## Existential clauses

A clause may carry an existential block after its universal prefix:
`∀ x₁ … xₙ, ∃ y : T, lhs = rhs`. It is skolemized: the `∃`-binder becomes a
fresh local `y : ∀ x₁ … xₙ, T` — a *skolem function* that is an unknown under
synthesis alongside `f` — and the body is instantiated with `y x₁ … xₙ`,
leaving an ordinary universally quantified equation that is sampled as usual
(`skolemizeClause`). The unknowns are then synthesized jointly as one term of
the CPS form of the tuple `T_f ×' T_y ×' …` — the same `dneg` transformation
`destruct` applies to structure goals — with each instantiated equation
rewritten to select its unknowns out of the tuple by continuation
(`wrapUnknowns`), so that β-reduction alone evaluates it once a candidate is
substituted. (`destruct`'s own `Exists` handling is of no use here: it takes
the witness of a *given* proof via `Exists.choose`, and no proof exists — the
witness is what is being synthesized.) -/

/-- Match `∃ y : α, body`, returning the binder name, its type, and the body
    (which refers to the binder by a loose bvar). `none` if the predicate
    argument is not a lambda. -/
def existsBody? : Lean.Expr → Option (Name × Lean.Expr × Lean.Expr)
  | .app (.app (.const ``Exists _) α) (.lam y _ body _) => some (y, α, body)
  | _ => none

/-- Skolemize the existential block of a clause `∀ xs, ∃ ys, body`: each
    `∃ y : T` becomes a skolem function of type `∀ xs, T`, and `y` is replaced
    by its application to the universal binders. Returns the skolem names and
    types together with a lambda taking the skolem values to the remaining
    universally quantified clause; a clause without an existential block is
    returned unchanged, with no skolems. -/
partial def skolemizeClause (clause : Lean.Expr) :
    MetaM (Array (Name × Lean.Expr) × Lean.Expr) := do
  if (existsBody? (binderTypesAndBody clause).2).isNone then
    return (#[], clause)
  forallTelescope clause fun xs body => go xs #[] body
where
  go (xs ws : Array Lean.Expr) (body : Lean.Expr) :
      MetaM (Array (Name × Lean.Expr) × Lean.Expr) := do
    if let some (y, α, rest) := existsBody? body then
      let skolemType ← mkForallFVars xs α
      if skolemType.hasFVar then
        throwError "the type of an existential variable must only depend on the \
          universally quantified variables of its own clause — it may not mention \
          local variables or an earlier existential variable{indentExpr α}"
      withLocalDeclD y skolemType fun w =>
        go xs (ws.push w) (rest.instantiate1 (mkAppN w xs))
    else if body.isForall then
      throwError "a `∀` after an `∃` is not supported — write the clause as \
        `∀ x₁ … xₙ, ∃ y₁ … yₘ, lhs = rhs`"
    else
      let names ← ws.mapM fun w => do
        pure (← w.fvarId!.getUserName, ← w.fvarId!.getType)
      return (names, ← mkLambdaFVars ws (← mkForallFVars xs body))

/-- Rewrite an instantiated example so that it constrains the CPS tuple local
    `g` instead of the unknown locals directly: a side mentioning an unknown
    becomes `g α (fun f y₁ … => side)`, selecting the side's value out of the
    tuple by continuation. -/
def wrapUnknowns (g : Lean.Expr) (unknowns : Array Lean.Expr) (ex : Lean.Expr) :
    MetaM Lean.Expr := do
  let some (α, lhs, rhs) := ex.eq?
    | throwError "example is not an equation:{indentExpr ex}"
  if (← whnf α).isForall then
    throwError "an existential clause must equate fully applied terms — \
      eta-expand the equation{indentExpr ex}"
  let wrap (side : Lean.Expr) : MetaM Lean.Expr := do
    if unknowns.any (fun u => side.containsFVar u.fvarId!) then
      return mkApp2 g α (← mkLambdaFVars unknowns side)
    else return side
  return mkApp3 ex.getAppFn α (← wrap lhs) (← wrap rhs)

/-- Extract component `i` of a synthesized CPS tuple `fun D k => k c₀ c₁ …`
    of the unknowns' `types`. Prefers syntactic extraction, which preserves any
    `simp only` attribution `.mdata` on the component; falls back to applying
    the candidate to a selecting continuation for exotic candidates. -/
def projectComponent (cand : Lean.Expr) (types : Array Lean.Expr) (i : Nat) :
    MetaM Lean.Expr := do
  let extracted ← lambdaBoundedTelescope cand 2 fun xs body => do
    if xs.size != 2 then return none
    let body := body.consumeMData
    if body.getAppFn == xs[1]! && body.getAppNumArgs == types.size then
      let arg := body.getAppArgs[i]!
      if !xs.any (fun x => arg.containsFVar x.fvarId!) then
        return some arg
    return none
  if let some e := extracted then return e
  let picker ← withLocalDeclsD (types.mapIdx fun j t =>
      (Name.mkSimple s!"c{j}", fun _ => pure t)) fun cs => mkLambdaFVars cs cs[i]!
  whnf (mkApp2 cand types[i]! picker)

/-! ## Candidate pinning -/

/-- Prepare `candidate` to survive outside the current elaboration context:
    Canonical does not translate universe levels, so the reconstruction carries
    unassigned level metavariables, which `check` pins by unification. Returns
    `none` if metavariables (or stray local variables) remain. -/
def pinCandidate? (candidate : Lean.Expr) : MetaM (Option Lean.Expr) := do
  try
    check candidate
    let c ← instantiateMVars candidate
    if c.hasExprMVar || c.hasLevelMVar || c.hasFVar then return none
    return some c
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    return none

end

end Canonical.PBP

module

public meta import ProgramByExample

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.PBP

public meta section

/-! # Programming by predicate

Machinery for synthesis from `∀ x₁ … xₙ, f a₁ … aₘ = b` predicate clauses,
driven by the `synthesize` tactic. Each predicate is instantiated with concrete
example inputs — themselves enumerated by Canonical, using its `count` option
on the product of the binder types — and the resulting ground equations become equational
constraints on the declaration under synthesis. The predicates
themselves are only sampled, not verified. See `ProgramByPredicate.md` for
the design. -/

/-! ## Term enumeration

We use Canonical with `count := k` to enumerate the first `k` distinct
inhabitants, which we use as example inputs for the quantified variables.
Several binders are enumerated as a single right-nested `Prod`, whose
search order already mixes the components by term size. -/

/-- Run Canonical on `type`, returning the first `count` inhabitants in
    search order. -/
def enumerate (type : Lean.Expr) (count : Nat) (timeout : UInt64 := 5) :
    MetaM (Array Lean.Expr) := do
  let config : Config := { count := USize.ofNat count, destruct := false, simp := false, recs := false }
  let typ ← toCanonical type #[] #[] config
  let result ← runCanonical { name := "enumerate", type := some typ } timeout config
  result.terms.mapM fun term => do instantiateMVars (← fromCanonical term type)

/-- Right-nested `Prod` of `types` (which must be nonempty). -/
def mkTupleType (types : Array Lean.Expr) : MetaM Lean.Expr := do
  types.pop.foldrM (init := types.back!) fun t acc => mkAppM ``Prod #[t, acc]

/-- Unpack a right-nested `Prod.mk` spine into `n` components. -/
partial def uncurryProd (e : Lean.Expr) (n : Nat) : MetaM (Array Lean.Expr) := do
  if n <= 1 then return #[e]
  let e ← whnf e
  let (fn, args) := e.getAppFnArgs
  if fn == ``Prod.mk && args.size == 4 then
    return #[args[2]!] ++ (← uncurryProd args[3]! (n - 1))
  throwError "enumerated tuple is not a pair:{indentExpr e}"

/-- Enumerate the first `k` example assignments for the quantified variables
    by inhabiting their (product) type; each inner array is one assignment
    in binder order. An empty `types` yields the single empty assignment. -/
def enumerateInputs (types : Array Lean.Expr) (k : Nat)
    (timeout : UInt64 := 5) : MetaM (Array (Array Lean.Expr)) := do
  if k == 0 then return #[]
  if types.isEmpty then return #[#[]]
  if types.size == 1 then
    return (← enumerate types[0]! k timeout).map (#[·])
  let tuples ← enumerate (← mkTupleType types) k timeout
  tuples.mapM fun t => uncurryProd t types.size

/-! ## Predicate instantiation -/

/-- Split a predicate into the types of its leading `∀` binders and the body
    that remains, which still refers to the binders by loose bvars. -/
def binderTypesAndBody : Lean.Expr → Array Lean.Expr × Lean.Expr :=
  go #[]
where
  go (types : Array Lean.Expr) : Lean.Expr → Array Lean.Expr × Lean.Expr
  | .forallE _ binderType body _ => go (types.push binderType) body
  | body => (types, body)

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

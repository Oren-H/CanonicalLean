module

public meta import ProgramByExample

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.PBP

public meta section

/-! # Programming by predicate

Machinery for synthesis from `∀ x₁ … xₙ, f a₁ … aₘ = b` predicate clauses,
driven by the `synthesize` tactic (`Synthesize.lean`, which replaced the
`#synthesize_pred` command). Each predicate is instantiated with concrete
example inputs — themselves enumerated by Canonical, using its `count` option
on the binder types — and the resulting ground equations become equational
constraints on the declaration under synthesis, exactly as for plain
input–output examples (see `ProgramByExample.lean`). The predicates
themselves are only sampled, not verified. See `ProgramByPredicate.md` for
the design. -/

/-! ## Term enumeration

Canonical is an exhaustive search procedure: given a type, it produces terms
of that type. With `count := k` it enumerates the first `k` distinct
inhabitants, which we use as example inputs for the quantified variables. -/

/-- If `e` is a concrete `Nat` value, return it. -/
def natValue? (e : Lean.Expr) : MetaM (Option Nat) := do
  match ← whnf e with
  | .lit (.natVal n) => return some n
  | .const ``Nat.zero _ => return some 0
  | _ => return none

/-- Sort enumerated terms deterministically: `Nat` values ascending, then
    everything else by approximate depth and rendering. -/
def sortTerms (terms : Array Lean.Expr) : MetaM (Array Lean.Expr) := do
  let keyed ← terms.mapM fun e => do
    let rank := match ← natValue? e with
      | some n => n
      | none => 1000000 + e.approxDepth.toNat
    pure (rank, toString (← ppExpr e), e)
  return (keyed.qsort fun x y => x.1 < y.1 || (x.1 == y.1 && x.2.1 < y.2.1)).map (·.2.2)

/-- Run Canonical on a fresh goal of type `type`, returning the first `count`
    terms it enumerates, in deterministic order. Drives the same pipeline as
    the `canonical` tactic (`getPremises → preprocess → toCanonical →
    runCanonical → postprocess`). -/
def enumerate (type : Lean.Expr) (count : Nat) (timeout : UInt64 := 5) :
    MetaM (Array Lean.Expr) := do
  let goal ← mkFreshExprMVar type
  let goalId := goal.mvarId!
  let config : Config := { count := USize.ofNat count }
  let terms ← goalId.withContext do
    let (premises, structs) ← getPremises goalId #[] config
    let (processedGoal, reconstruct) ← withArityUnfold config.monomorphize do
      preprocess goalId config structs
    let typ ← withArityUnfold config.monomorphize do processedGoal.withContext do
      toCanonical (← processedGoal.getType) premises (structs.push ``Pi) config
    let result ← runCanonical { name := "enumerate", type := some typ } timeout config
    let terms ← postprocess result processedGoal config reconstruct
    terms.mapM instantiateMVars
  sortTerms terms

/-- Memoizes `enumerate` results per `(type, count)` for the duration of one
    command, so that two binders of the same type see the same example terms
    (separate solver runs need not return the same enumeration). -/
abbrev EnumCache := IO.Ref (Array ((Lean.Expr × Nat) × Array Lean.Expr))

/-- `enumerate`, memoized in `cache`. -/
def enumerateCached (cache : EnumCache) (type : Lean.Expr) (count : Nat)
    (timeout : UInt64 := 5) : MetaM (Array Lean.Expr) := do
  if let some (_, terms) := (← cache.get).find? (fun (key, _) => key == (type, count)) then
    return terms
  let terms ← enumerate type count timeout
  cache.modify (·.push ((type, count), terms))
  return terms

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
def gatherTerms (cache : EnumCache) (types : Array Lean.Expr) (k : Nat)
    (timeout : UInt64 := 5) : MetaM (Array (Array Lean.Expr)) := do
  if types.isEmpty then return #[]
  let dim := types.size
  if dim == 1 then
    return #[← enumerateCached cache types[0]! k timeout]
  let mut counts := Array.replicate dim (minTermCount k dim)
  let mut termLists ← types.mapIdxM fun i ty => enumerateCached cache ty counts[i]! timeout
  while cartesianSize termLists < k do
    let mut grown := false
    for i in [0:dim] do
      if termLists[i]!.size == counts[i]! then
        counts := counts.set! i (counts[i]! + 1)
        grown := true
    if !grown then break
    termLists ← types.mapIdxM fun i ty => enumerateCached cache ty counts[i]! timeout
  return termLists

/-- Enumerate the first `k` example assignments for heterogeneous quantified
    variables; each inner array is one assignment in binder order. An empty
    `types` yields the single empty assignment. -/
def enumerateInputs (cache : EnumCache) (types : Array Lean.Expr) (k : Nat)
    (timeout : UInt64 := 5) : MetaM (Array (Array Lean.Expr)) := do
  if k == 0 then return #[]
  if types.isEmpty then return #[#[]]
  let termLists ← gatherTerms cache types k timeout
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

/-- `elimSpecial` only turns `Nat` literals ≤ 5 into constructor spines the
    solver can compute with; instantiated predicates readily produce larger
    values (e.g. `double 4 = 8`), so we convert up to this bound ourselves. -/
def MAX_CTOR_NAT := 64

/-- Convert `Nat` literals produced by reduction into constructor form. -/
partial def natLitToCtor : Lean.Expr → Lean.Expr
  | .lit (.natVal n) => if n ≤ MAX_CTOR_NAT then rawRawNatLit n else .lit (.natVal n)
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

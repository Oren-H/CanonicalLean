module

public meta import ProgramByExample
public meta import RecursorToMatch

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
input–output examples (see `ProgramByExample.lean`). Once a function is
found, `provePredicatesLetBound` attempts to *prove* each predicate about it;
found proofs become `theorem`s for the user to paste, and predicates that
could not be proved produce a warning. See `ProgramByPredicate.md` for the
design. -/

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

/-! ## Predicate verification

The instantiated equations only *sample* each predicate, so a function that
satisfies all of them need not satisfy the predicates themselves. After the
search succeeds, we therefore attempt to prove each predicate about the
synthesized function. The candidate is let-bound under the function's name
(`provePredicatesLetBound`): the binding's defining equation reaches the
solver as a single reduction rule to the raw term, each predicate is restated
about the binding, and the resulting proposition is handed to the ordinary
Canonical tactic pipeline. (The former `#synthesize_pred` command could do
better — elaborate the suggested `def` in a sandboxed copy of the command
state and prove against its match-form equation lemmas — but command
elaboration is not available from within a tactic.) -/

/-- Attempt to prove the proposition `prop` with Canonical, driving the same
    pipeline as the `canonical` tactic (`getPremises → preprocess →
    toCanonical → runCanonical → postprocess`); `consts` are extra constants
    made available to the search. Returns the first proof found. -/
def prove (name : String) (prop : Lean.Expr) (consts : Array Name)
    (timeout : UInt64) : MetaM (Option Lean.Expr) := do
  let goal ← mkFreshExprMVar prop
  let goalId := goal.mvarId!
  let config : Config := {}
  let proofs ← goalId.withContext do
    let (premises, structs) ← getPremises goalId consts config
    let (processedGoal, reconstruct) ← withArityUnfold config.monomorphize do
      preprocess goalId config structs
    let typ ← withArityUnfold config.monomorphize do processedGoal.withContext do
      toCanonical (← processedGoal.getType) premises (structs.push ``Pi) config
    let result ← runCanonical { name, type := some typ } timeout config
    let proofs ← postprocess result processedGoal config reconstruct
    proofs.mapM instantiateMVars
  return proofs[0]?

/-- If `stmt` — a possibly universally quantified equation — is true by
    definitional equality, return the `fun … ↦ Eq.refl _` proof. Such
    statements need no search, and the solver's reconstruction can embed
    propositional rewrites (e.g. `Nat.succ.injEq`) that do not re-elaborate
    as tactics even when the goal is definitionally trivial. -/
def rflProof? (stmt : Lean.Expr) : MetaM (Option Lean.Expr) := do
  forallTelescope stmt fun xs body => do
    let some (_, lhs, rhs) := body.eq? | return none
    unless ← withoutArityUnfold (isDefEq lhs rhs) do return none
    return some (← mkLambdaFVars xs (← mkEqRefl rhs))

/-- Check that the delaborated proof `stx` elaborates back to a complete proof
    of `stmt`. Reconstructed proofs may embed `simp only` attributions that
    only make sense as re-elaborated syntax, and delaboration need not round-
    trip in general, so a suggestion is only trustworthy if it passes this. -/
def elaboratesAgainst (stx : TSyntax `term) (stmt : Lean.Expr) : Term.TermElabM Bool := do
  try
    withoutModifyingState do Term.withoutErrToSorry do
      let proof ← Term.elabTermEnsuringType stx (some stmt)
      Term.synthesizeSyntheticMVarsNoPostponing
      let proof ← instantiateMVars proof
      return !proof.hasSorry && !proof.hasExprMVar
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    return false

/-- Delaborate `proof`, preferring the recursor→match rendering, keeping a
    rendering only if it re-elaborates against `stmt`; a suggestion that was
    trustworthy before the conversion stays trustworthy after it. -/
def delabProof (proof stmt : Lean.Expr) : Term.TermElabM (Option (TSyntax `term)) := do
  let stx? ← try some <$> R2M.delabR2M proof catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex else pure none
  if let some stx := stx? then
    if ← elaboratesAgainst stx stmt then return some stx
  let stx ← PrettyPrinter.delab proof
  if ← elaboratesAgainst stx stmt then return some stx
  return none

/-- Attempt to prove `stmt` — one predicate restated about the definition under
    test — first by `Eq.refl`, then with the solver. Returns the delaborated
    proof, or a warning explaining why none survived. -/
def proveOne (stmt : Lean.Expr) (thmName : Name) (consts : Array Name)
    (timeout : UInt64) :
    Term.TermElabM (Option (TSyntax `term) × Option MessageData) := do
  -- A definitionally true predicate needs no search: prove it with `Eq.refl`
  -- directly. Failing that, fall through to the solver.
  let rfl? ← try rflProof? stmt
    catch ex => if ex.isInterrupt || ex.isRuntime then throw ex else pure none
  if let some proof := rfl? then
    if let some stx ← delabProof proof stmt then
      return (some stx, none)
  let proof? ← try
      prove thmName.toString stmt consts timeout
    catch ex =>
      if ex.isInterrupt || ex.isRuntime then throw ex
      return (none, some m!"the attempt to prove this predicate about the \
        synthesized function failed:{indentD ex.toMessageData}")
  let some proof := proof?
    | return (none, some m!"found no proof that the synthesized function \
        satisfies this predicate; increase the timeout with \
        `synthesize {timeout.toNat * 2}` to search longer")
  if let some stx ← delabProof proof stmt then
    return (some stx, none)
  return (none, some m!"a proof that the synthesized function satisfies this \
    predicate was found, but it does not re-elaborate and was \
    discarded:{indentD (← PrettyPrinter.delab proof)}")

/-- Attempt to prove each predicate — `(t, stmt)` pairs the clause syntax with
    the statement about the definition under test. Returns the `theorem`
    commands for the proofs found and, for each predicate that resisted, its
    clause syntax paired with the warning. -/
def provePredicates (preds : Array (Term × Lean.Expr)) (consts : Array Name)
    (timeout : UInt64) (fname : Name) :
    Term.TermElabM (Array (TSyntax `command) × Array (Term × MessageData)) := do
  let mut thmCmds := #[]
  let mut warnings := #[]
  let mut i := 0
  for (t, stmt) in preds do
    i := i + 1
    let thmName := fname.appendAfter (if preds.size == 1 then "_spec" else s!"_spec_{i}")
    let (proofStx?, warning?) ← proveOne stmt thmName consts timeout
    if let some warning := warning? then
      warnings := warnings.push (t, warning)
    if let some proofStx := proofStx? then
      let thmNameId := mkIdent thmName
      thmCmds := thmCmds.push
        (← `(command| theorem $thmNameId:ident : $t:term := $proofStx:term))
  return (thmCmds, warnings)

/-- The warning for a predicate that resisted proof: the definition is then
    only guaranteed to satisfy the instantiated equations, not the predicate. -/
def predWarning (fname : Name) (w : MessageData) : MessageData :=
  m!"{w}\nthe definition `{fname}` is only guaranteed to satisfy the \
    instantiated example equations, not this predicate"

/-- Prove the predicates about `candidate` let-bound under `fname` in place of
    the opaque local `f` — the definition itself does not exist yet while the
    `synthesize` tactic elaborates its body. The binding's defining equation
    reaches the solver as a single reduction rule to the raw term, and found
    proofs delaborate referring to the function by name. Logs the warnings;
    returns the `theorem` commands. -/
def provePredicatesLetBound (fname : Name) (type candidate f : Lean.Expr)
    (preds : Array (Term × Lean.Expr)) (consts : Array Name) (timeout : UInt64) :
    Term.TermElabM (Array (TSyntax `command)) := do
  withLCtx ((← getLCtx).erase f.fvarId!) (← getLocalInstances) do
    withLetDecl fname type candidate fun fc => do
      let preds := preds.map fun (t, e) => (t, e.replaceFVar f fc)
      let (thmCmds, warnings) ← provePredicates preds consts timeout fname
      for (t, warning) in warnings do
        logWarningAt t (predWarning fname warning)
      return thmCmds

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

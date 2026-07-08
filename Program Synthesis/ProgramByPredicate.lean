module

public meta import ProgramByExample

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.PBP

public meta section

/-! # Programming by predicate

`#synthesize_pred f : T` followed by `| ∀ x₁ … xₙ, f a₁ … aₘ = b` predicate
clauses asks Canonical for a function of type `T` that satisfies every
predicate. Each predicate is instantiated with concrete example inputs —
themselves enumerated by Canonical, using its `count` option on the binder
types — and the resulting ground equations become equational constraints on
the declaration under synthesis, exactly as in `#synthesize` (see
`ProgramByExample.lean`). Once a function is found, the command attempts to
*prove* each predicate about it — about the suggested definition itself,
recursors already rendered as pattern matching, so the solver works with its
match-form equations rather than the raw recursor term; found proofs are
suggested as `theorem`s alongside the `def`, and predicates that could not be
proved produce a warning. See `ProgramByPredicate.md` for the design. -/

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
synthesized function. The recursor→match conversion happens *before* these
proof attempts: the suggested `def` — recursors already rendered as pattern
matching by `R2M.mkDefCommand` — is elaborated in a sandboxed copy of the
command state, each predicate is restated about the new constant, and the
resulting proposition is handed to the ordinary Canonical tactic pipeline.
The solver then sees the function through the definition's match-form
equation lemmas (`f n 0 = n`, `f n (k+1) = (f n k).succ`, …) instead of a
single reduction rule to the raw recursor term, which it is better at proving
with. If the suggested definition cannot be elaborated (or the candidate
cannot leave its elaboration context), the candidate is let-bound under the
function's name and the proofs run against that binding, as before. -/

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
    (timeout : UInt64) (fname : Name) :
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
        `#synthesize_pred {timeout.toNat * 2} {fname} : …` to search longer")
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
    let (proofStx?, warning?) ← proveOne stmt thmName consts timeout fname
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
    the opaque local `f` — the fallback when the suggested definition itself is
    not available to prove against. The binding's defining equation reaches the
    solver as a single reduction rule to the raw term, and found proofs
    delaborate referring to the function by name. Logs the warnings; returns
    the `theorem` commands. -/
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

/-- Emit the suggestion: the `def` alone if nothing was proved, otherwise the
    `def` followed by the proved `theorem`s as a single multi-command string. -/
def emitSuggestion (ref : Syntax) (defCmd : TSyntax `command)
    (thmCmds : Array (TSyntax `command)) : Term.TermElabM Unit := do
  if thmCmds.isEmpty then
    TryThis.addSuggestion ref defCmd
  else
    let text := "\n".intercalate (← (#[defCmd] ++ thmCmds).toList.mapM fun cmd =>
      return (← PrettyPrinter.ppCommand cmd).pretty)
    TryThis.addSuggestion ref { suggestion := .string text }

/-- The number of error messages in `log`, reported or not. Comparing counts
    before and after a nested `elabCommand` detects whether it errored. -/
def errorCount (log : MessageLog) : Nat :=
  log.reportedPlusUnreported.foldl
    (fun n msg => if msg.severity matches .error then n + 1 else n) 0

/-! ## The command -/

/-- Extra constants made available to the search, as in `canonical [foo, bar]`. -/
syntax pbpPremises := " [" withoutPosition(term,*,?) "]"

/-- Sets the number of example instantiations generated per predicate (default 3). -/
syntax pbpExamples := " (" &"examples" " := " num ")"

/-- A single predicate clause: `| ∀ x₁ … xₙ, f a₁ … aₘ = b`. A clause without
    binders is an ordinary input–output example, as in `#synthesize`. -/
syntax pbpPredicate := "| " term

/-- `#synthesize_pred f : T` followed by `| ∀ x₁ … xₙ, f a₁ … aₘ = b` clauses
    searches for a function of type `T` satisfying all of the predicates, and
    suggests it as a definition. Each predicate is instantiated with concrete
    inputs enumerated by Canonical for the quantified variables, and the
    resulting example equations constrain the search exactly as in
    `#synthesize`. Once a function is found, the command attempts to prove
    each predicate about it (with the same timeout per predicate) — about the
    suggested definition itself, recursors already rendered as pattern
    matching, elaborated in a sandboxed command state: proofs
    found are suggested as `theorem f_spec…` declarations alongside the
    `def`, and every predicate that could not be proved produces a warning —
    the function then only provably satisfies the instantiated equations. An
    optional numeral sets the timeout in seconds (`#synthesize_pred 30 f :
    …`), `(examples := n)` sets the number of instantiations per predicate,
    and an optional premise list provides extra constants to the search
    (`#synthesize_pred [Nat.add] g : …`). -/
elab (name := synthesizePredCmd) "#synthesize_pred " timeout?:(num)? examples?:(pbpExamples)?
    premises?:(pbpPremises)? fnameId:ident " : " sig:term preds:pbpPredicate* : command => do
  let ref ← getRef
  let fname := fnameId.getId
  let timeout : UInt64 := if let some t := timeout? then UInt64.ofNat t.getNat else 5
  let predTerms : Array Term ← preds.mapM fun predStx => do
    let `(pbpPredicate| | $t:term) := predStx | throwUnsupportedSyntax
    pure t

  -- Phase 1, in the term elaborator: elaborate and validate the input,
  -- instantiate the predicates with enumerated example equations, search, and
  -- build each candidate's `def` suggestion (recursors rendered as pattern
  -- matching by `R2M.mkDefCommand`). Candidates that can leave this
  -- elaboration context are deferred to phase 2 below, which proves the
  -- predicates about the suggested definition itself.
  let (deferred, consts) ← Command.runTermElabM fun _ => do
    let consts ← if let some prems := premises? then
        match prems with
        | `(pbpPremises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
        | _ => throwUnsupportedSyntax
      else pure #[]
    let k ← if let some exStx := examples? then
        match exStx with
        | `(pbpExamples| (examples := $n)) => pure n.getNat
        | _ => throwUnsupportedSyntax
      else pure 3
    if k == 0 then
      throwError "the number of examples per predicate must be positive"
    let config : Config := { destruct := false }

    let type ← Term.elabType sig
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    if type.hasMVar || type.hasLevelMVar then
      throwErrorAt sig "the signature contains unresolved metavariables{indentExpr type}"

    withLocalDeclD fname type fun f => do
      -- Elaborate and validate the predicate clauses.
      let predicates ← predTerms.mapM fun (t : Term) => do
        let e ← Term.elabTermEnsuringType t (some (mkSort .zero))
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasMVar then
          throwErrorAt t "the predicate contains unresolved metavariables{indentExpr e}"
        let (binderTypes, body) := binderTypesAndBody e
        for binderType in binderTypes do
          if binderType.hasLooseBVars then
            throwErrorAt t "the type of a quantified variable may not depend on other \
              quantified variables{indentExpr binderType}"
          if binderType.hasFVar then
            throwErrorAt t "the type of a quantified variable must be closed — it may not \
              mention `{fname}` or other local variables{indentExpr binderType}"
        let some (_, lhs, _) := body.eq?
          | throwErrorAt t "a predicate must be a universally quantified equation \
              `∀ x₁ … xₙ, {fname} a₁ … aₘ = b`"
        unless lhs.getAppFn == f do
          throwErrorAt t "the left-hand side of a predicate must be an application of `{fname}`"
        pure (t, e, binderTypes, body)
      if predicates.isEmpty then
        throwError "provide at least one predicate: `| ∀ x₁ … xₙ, {fname} a₁ … aₘ = b`"

      -- Instantiate each predicate with enumerated example inputs. The
      -- enumeration runs in an empty local context so that neither `{fname}`
      -- nor section variables can occur in the example inputs.
      let cache : EnumCache ← IO.mkRef #[]
      let mut examples : Array Lean.Expr := #[]
      for (t, _, binderTypes, body) in predicates do
        let inputs ← withLCtx {} #[] do enumerateInputs cache binderTypes k
        if inputs.isEmpty then
          throwErrorAt t "could not enumerate example inputs for the quantified variables"
        for vals in inputs do
          examples := examples.push (← reduceGroundEq f (body.instantiateRev vals))
      examples := dedupExamples examples
      if examples.isEmpty then
        throwError "all instantiated examples are trivial equations; increase \
          `(examples := n)` or add predicates"
      logInfo m!"instantiated {examples.size} example equation(s):{indentD
        (MessageData.joinSep (examples.toList.map (m!"{·}")) m!"\n")}"

      -- From here on, the pipeline is that of `#synthesize`.
      let decl ← withArityUnfold config.monomorphize do
        PBE.toProblem fname.toString f type examples consts config

      let result ← runCanonical decl timeout config

      let terms ← withArityUnfold config.monomorphize do
        result.terms.mapM (fromCanonical · type)

      if terms.isEmpty then
        throwError "No function found. Increase the timeout with `#synthesize_pred \
          {timeout.toNat * 2} {fname} : …`, add predicates, increase `(examples := n)`, \
          or supply premises with `#synthesize_pred [name, …] {fname} : …`"

      withOptions applyOptions do
        let mut deferred : Array ((TSyntax `command) × Lean.Expr) := #[]
        for candidate in terms do
          for ex in examples do
            unless ← PBE.satisfiesExample f candidate ex do
              logWarning m!"the synthesized term{indentExpr candidate}\ndoes not satisfy \
                the instantiated example `{ex}`"
          let defCmd ← R2M.mkDefCommand fnameId sig f candidate type
          match ← pinCandidate? candidate with
          | some pinned =>
            deferred := deferred.push (defCmd, pinned)
          | none =>
            -- The candidate cannot leave this elaboration context; prove the
            -- predicates about it let-bound under the function's name here.
            let thmCmds ← provePredicatesLetBound fname type candidate f
              (predicates.map fun (t, e, _, _) => (t, e)) consts timeout
            emitSuggestion ref defCmd thmCmds
        return (deferred, consts)

  -- Phase 2, per candidate: elaborate the suggested definition in a sandboxed
  -- copy of the command state, so the predicates are proved about the function
  -- *as suggested* — the solver sees its match-form equation lemmas rather
  -- than a reduction rule to the raw recursor term — then roll the state back
  -- and report. Found proofs delaborate referring to the function by name,
  -- which, once the suggestion is applied, resolves to the pasted `def`.
  for (defCmd, candidate) in deferred do
    let saved ← get
    let proved? ←
      try
        Command.elabCommand defCmd
        if errorCount (← get).messages > errorCount saved.messages then
          pure none
        else
          some <$> Command.runTermElabM fun _ => withOptions applyOptions do
            let declName ← resolveGlobalConstNoOverload fnameId
            let some info := (← getEnv).find? declName
              | throwError "the suggested definition was not elaborated"
            if info.value?.any (·.hasSorry) then
              throwError "the suggested definition elaborated with errors"
            let preds ← predTerms.mapM fun (t : Term) => do
              let stmt ← Term.elabTermEnsuringType t (some (mkSort .zero))
              Term.synthesizeSyntheticMVarsNoPostponing
              pure (t, ← instantiateMVars stmt)
            let (thmCmds, warnings) ← provePredicates preds consts timeout fname
            -- The sandbox is about to be rolled back: render the warnings
            -- while their context still exists.
            let warnings ← warnings.mapM fun (t, w) =>
              return (t, ← (← addMessageContext w).format)
            pure (thmCmds, warnings)
      catch ex =>
        if ex.isInterrupt || ex.isRuntime then
          set saved
          throw ex
        pure none
    set saved
    match proved? with
    | some (thmCmds, warnings) =>
      for (t, warning) in warnings do
        logWarningAt t (predWarning fname m!"{warning}")
      Command.liftTermElabM <| emitSuggestion ref defCmd thmCmds
    | none =>
      -- The suggested definition did not elaborate here (e.g. a name clash):
      -- fall back to proving the predicates about the let-bound raw term.
      Command.runTermElabM fun _ => withOptions applyOptions do
        let type ← Term.elabType sig
        Term.synthesizeSyntheticMVarsNoPostponing
        let type ← instantiateMVars type
        withLocalDeclD fname type fun f => do
          let preds ← predTerms.mapM fun (t : Term) => do
            let stmt ← Term.elabTermEnsuringType t (some (mkSort .zero))
            Term.synthesizeSyntheticMVarsNoPostponing
            pure (t, ← instantiateMVars stmt)
          let thmCmds ← provePredicatesLetBound fname type candidate f preds consts timeout
          emitSuggestion ref defCmd thmCmds

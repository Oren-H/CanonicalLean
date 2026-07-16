module

public meta import ProgramByPredicate
public meta import Canonical.Refine

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.Synth

public meta section

/-! # The `synthesize` tactic

Program synthesis as a tactic, inside the very definition being written:

```
def add : Nat → Nat → Nat := by
  synthesize
  | ∀ n m : Nat, add n m = add m n
  | ∀ n : Nat, add n 0 = n
  | add 1 1 = 2
```

Each clause is a (possibly) universally quantified equation about the function
under definition — `add` in the clauses refers to the auxiliary local constant
Lean introduces while elaborating the `def`, so the clauses read exactly like
the specifications they are. A clause without binders is an ordinary
input–output example; quantified clauses are instantiated with example inputs
enumerated by Canonical, as in the former `#synthesize_pred` command (this
tactic replaces both `#synthesize` and `#synthesize_pred`; the machinery lives
in `ProgramByExample.lean` and `ProgramByPredicate.lean`).

The instantiated equations become equational constraints on the declaration
under synthesis (`PBE.toProblem`), and Canonical searches for a function of
the goal type satisfying them. Like `canonical`, the tactic then admits the
goal and offers each function found as a `Try this: exact …` suggestion.
The instantiated equations only *sample* quantified clauses: each candidate
is re-checked against them by definitional equality (a failure produces a
warning), but the clauses themselves are not verified — a function
satisfying every sample need not satisfy the predicates. -/

/-- The elaborator wraps applications of the function under definition in
    `_recApp` metadata (bookkeeping for the recursion compiler, which never
    sees the clauses); strip it so that the clauses reach the enumeration and
    translation machinery as plain applications of the auxiliary local. -/
partial def eraseRecAppMData (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    if let .mdata d b := sub then
      if d.isRecApp then some (eraseRecAppMData b) else none
    else none

/-- Extra constants made available to the search, as in `canonical [foo, bar]`. -/
syntax synthPremises := " [" withoutPosition(term,*,?) "]"

/-- Opens the interactive refinement UI on the synthesis problem, as in
    `canonical +refine`. -/
syntax synthRefine := " +" &"refine"

/-- Dumps the synthesis problem to `debug.json` instead of searching, as in
    `canonical +debug`. The dump is replayable by the Rust CLI entrypoint. -/
syntax synthDebug := atomic(" +" &"debug")

/-- Sets the number of example instantiations generated per clause (default 3). -/
syntax synthExamples := " (" &"examples" " := " num ")"

/-- A single specification clause: `| ∀ x₁ … xₙ, f a₁ … aₘ = b`. A clause
    without binders is an ordinary input–output example. -/
syntax synthClause := "| " term

/-- `synthesize`, in the body of `def f : T := by synthesize`, followed by
    `| ∀ x₁ … xₙ, f a₁ … aₘ = b` clauses, searches for a function of type `T`
    satisfying all of the clauses and suggests it as `exact …`. In the clauses
    `f` refers to the definition's own name. Each quantified clause is
    instantiated with concrete inputs enumerated by Canonical; a clause
    without binders is an ordinary input–output example. The instantiated
    equations constrain the search as in the former `#synthesize` command,
    and each function found is re-checked against them (a failure produces a
    warning) — the quantified clauses themselves are only sampled, not
    verified. Once a function is found, the tactic admits the goal and
    suggests it via `Try this:`. An optional numeral sets the timeout in
    seconds (`synthesize 30`), `(examples := n)` sets the number of
    instantiations per clause, an optional premise list provides extra
    constants to the search (`synthesize [Nat.add]`), and `+refine` opens the
    interactive refinement UI on the synthesis problem instead of searching,
    as in `canonical +refine`. -/
elab (name := synthesizeTac) "synthesize " timeout?:(num)? debug?:(synthDebug)?
    refine?:(synthRefine)? examples?:(synthExamples)? premises?:(synthPremises)?
    clauses:synthClause* : tactic => do
  let ref ← getRef
  let goal ← getMainGoal
  goal.withContext do
    let consts ← if let some prems := premises? then
        match prems with
        | `(synthPremises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
        | _ => throwUnsupportedSyntax
      else pure #[]
    let k ← if let some exStx := examples? then
        match exStx with
        | `(synthExamples| (examples := $n)) => pure n.getNat
        | _ => throwUnsupportedSyntax
      else pure 3
    if k == 0 then
      throwError "the number of examples per clause must be positive"
    let timeout : UInt64 := if let some t := timeout? then UInt64.ofNat t.getNat else 5
    let config : Config := { destruct := false, refine := refine?.isSome,
                             debug := debug?.isSome }

    let type ← instantiateMVars (← goal.getType)
    if type.hasMVar || type.hasLevelMVar then
      throwError "the goal type contains unresolved metavariables{indentExpr type}"

    let clauseTerms : Array Term ← clauses.mapM fun c => do
      let `(synthClause| | $t:term) := c | throwUnsupportedSyntax
      pure t
    if clauseTerms.isEmpty then
      throwError "provide at least one clause: `| ∀ x₁ … xₙ, f a₁ … aₘ = b`"

    -- Elaborate the clauses.
    let elaborated : Array (Term × Lean.Expr) ← clauseTerms.mapM fun (t : Term) => do
      let e ← Term.elabTermEnsuringType t (some (mkSort .zero))
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasMVar then
        throwErrorAt t "the clause contains unresolved metavariables{indentExpr e}"
      pure (t, eraseRecAppMData e)

    -- The function under synthesis is the head of the clauses' left-hand
    -- sides: the auxiliary local constant standing for the definition being
    -- elaborated. It plays the role the fresh local `f` played in the former
    -- commands — `toProblem` renames it to the declaration name, and the
    -- local-context fold excludes auxiliary declarations from the premises.
    let f ← do
      let (t, e) := elaborated[0]!
      let (_, body) := PBP.binderTypesAndBody e
      let some (_, lhs, _) := body.eq?
        | throwErrorAt t "a clause must be a universally quantified equation \
            `∀ x₁ … xₙ, f a₁ … aₘ = b` about the function being defined"
      let head := lhs.getAppFn
      let isAux ← if let .fvar fvarId := head then
          pure (← fvarId.getDecl).isAuxDecl
        else pure false
      unless isAux do
        throwErrorAt t "the left-hand side of a clause must be an application of the \
          function being defined — use `synthesize` in the body of a definition, \
          `def f : T := by synthesize …`, with clauses about `f`"
      pure head
    let fname ← f.fvarId!.getUserName

    unless ← isDefEq (← f.fvarId!.getType) type do
      throwError "`{fname}` has type{indentExpr (← f.fvarId!.getType)}\nbut the goal is\
        {indentExpr type}\nmove the definition's binders into its type, so that the goal \
        is the full signature of `{fname}`"

    -- Validate the clauses.
    let predicates ← elaborated.mapM fun (t, e) => do
      let (binderTypes, body) := PBP.binderTypesAndBody e
      for binderType in binderTypes do
        if binderType.hasLooseBVars then
          throwErrorAt t "the type of a quantified variable may not depend on other \
            quantified variables{indentExpr binderType}"
        if binderType.hasFVar then
          throwErrorAt t "the type of a quantified variable must be closed — it may not \
            mention `{fname}` or other local variables{indentExpr binderType}"
      let some (_, lhs, _) := body.eq?
        | throwErrorAt t "a clause must be a universally quantified equation \
            `∀ x₁ … xₙ, {fname} a₁ … aₘ = b`"
      unless lhs.getAppFn == f do
        throwErrorAt t "the left-hand side of a clause must be an application of `{fname}`"
      pure (t, e, binderTypes, body)

    -- Instantiate each clause with enumerated example inputs. The enumeration
    -- runs in an empty local context so that neither `{fname}` nor other local
    -- variables can occur in the example inputs.
    let cache : PBP.EnumCache ← IO.mkRef #[]
    let mut examples : Array Lean.Expr := #[]
    for (t, _, binderTypes, body) in predicates do
      let inputs ← withLCtx {} #[] do PBP.enumerateInputs cache binderTypes k
      if inputs.isEmpty then
        throwErrorAt t "could not enumerate example inputs for the quantified variables"
      for vals in inputs do
        examples := examples.push (← PBP.reduceGroundEq f (body.instantiateRev vals))
    examples := PBP.dedupExamples examples
    -- A numeral above `MAX_CTOR_NAT` stays an opaque literal the solver cannot
    -- compute with (`natLitToCtor` leaves it alone), so an example containing
    -- one is unsatisfiable and would poison the whole search.
    let (kept, dropped) := examples.partition fun ex =>
      (ex.find? fun sub => sub matches .lit (.natVal _)).isNone
    for ex in dropped do
      logWarning m!"ignoring the example `{ex}`: it contains a numeral larger than \
        {PBE.MAX_CTOR_NAT}, which the search cannot compute with"
    examples := kept
    if examples.isEmpty then
      if !dropped.isEmpty then
        throwError "every instantiated example contains a numeral larger than \
          {PBE.MAX_CTOR_NAT}, which the search cannot compute with"
      throwError "all instantiated examples are trivial equations; increase \
        `(examples := n)` or add clauses"
    logInfo m!"instantiated {examples.size} example equation(s):{indentD
      (MessageData.joinSep (examples.toList.map (m!"{·}")) m!"\n")}"

    -- From here on, the pipeline is that of the former `#synthesize`.
    let decl ← withArityUnfold config.monomorphize do
      PBE.toProblem fname.toString f type examples consts config

    if config.debug then
      Elab.admitGoal goal
      save_problem decl "debug.json"
      return

    -- Refinement UI, as in `canonical +refine`. No preprocessing was applied,
    -- so the processed goal is the goal itself; reconstruction only pins the
    -- candidate's level metavariables, as in the search path below.
    if config.refine then
      let _ ← Canonical.refine decl
      let (width, indent, column, range) ← widthIndentColumnRange
      let x : Server.WithRpcRef RpcData ← Server.WithRpcRef.mk {
        mctx := ← getMCtx, mainGoal := goal, config,
        reconstruct := fun e => return (← PBP.pinCandidate? e).getD e,
        width, indent, column, processedGoal := goal
      }
      Elab.admitGoal goal
      Widget.savePanelWidgetInfo (hash refineWidget.javascript) ref (props := do
        let rpcData ← Server.RpcEncodable.rpcEncode x
        return Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)])
      return

    let result ← runCanonical decl timeout config

    let terms ← withArityUnfold config.monomorphize do
      result.terms.mapM (fromCanonical · type)

    if terms.isEmpty then
      throwError "No function found. Increase the timeout with `synthesize \
        {timeout.toNat * 2}`, add clauses, increase `(examples := n)`, or supply \
        premises with `synthesize [name, …]`"

    withOptions applyOptions do
      for candidate in terms do
        for ex in examples do
          unless ← PBE.satisfiesExample f candidate ex do
            logWarning m!"the synthesized term{indentExpr candidate}\ndoes not satisfy \
              the instantiated example `{ex}`"
        let candidate := (← PBP.pinCandidate? candidate).getD candidate
        TryThis.addExactSuggestion ref candidate
      Elab.admitGoal goal

end

end Canonical.Synth

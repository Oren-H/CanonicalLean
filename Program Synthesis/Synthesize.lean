module

public meta import ProgramByPredicate

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
Because the equations only *sample* the clauses, the tactic also attempts to
*prove* each clause about the function (let-bound under its name, with the
same timeout per clause): the proofs found are logged as ready-to-paste
`theorem f_spec…` declarations, and every clause that resists produces a
warning — the function is then only guaranteed to satisfy the instantiated
examples. When proofs are found the suggestion is the raw term the proofs
were checked against; otherwise recursor applications are rendered as
`match`/`let rec` syntax. -/

/-- The elaborator wraps applications of the function under definition in
    `_recApp` metadata (bookkeeping for the recursion compiler, which never
    sees the clauses); strip it so that the clauses reach the enumeration and
    translation machinery as plain applications of the auxiliary local. -/
partial def eraseRecAppMData (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    if let .mdata d b := sub then
      if d.isRecApp then some (eraseRecAppMData b) else none
    else none

/-- Add a `Try this: exact …` suggestion for the synthesized `t : type`, with
    recursor applications rendered as `match`/`let rec` syntax when the
    rendering re-elaborates to the same function (`let rec` renderings are
    accepted as-is, exactly as in `R2M.mkDefCommand`); any failure falls back
    to the raw recursor display. -/
def addExactSuggestionR2M (ref : Syntax) (t type : Lean.Expr) : TacticM Unit := do
  try
    let body ← R2M.delabR2M t
    if ← R2M.roundTrips body t type then
      TryThis.addSuggestion ref (← `(tactic| exact $body))
      return
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
  TryThis.addExactSuggestion ref t

/-- Extra constants made available to the search, as in `canonical [foo, bar]`. -/
syntax synthPremises := " [" withoutPosition(term,*,?) "]"

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
    equations constrain the search as in the former `#synthesize` command.
    Once a function is found, the tactic admits the goal, suggests the
    function via `Try this:` (rendered with `match`/`let rec` syntax when no
    spec proofs accompany it, raw otherwise, so that pasted proofs elaborate
    against the pasted definition), and attempts to prove each clause about
    it (with the same timeout per clause): proofs found are logged as
    `theorem f_spec…` declarations to paste after the definition, and every
    clause that could not be proved produces a warning — the function then
    only provably satisfies the instantiated examples. An optional numeral sets
    the timeout in seconds (`synthesize 30`), `(examples := n)` sets the
    number of instantiations per clause, and an optional premise list
    provides extra constants to the search (`synthesize [Nat.add]`). -/
elab (name := synthesizeTac) "synthesize " timeout?:(num)? examples?:(synthExamples)?
    premises?:(synthPremises)? clauses:synthClause* : tactic => do
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
    let config : Config := { destruct := false }

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
    if examples.isEmpty then
      throwError "all instantiated examples are trivial equations; increase \
        `(examples := n)` or add clauses"
    logInfo m!"instantiated {examples.size} example equation(s):{indentD
      (MessageData.joinSep (examples.toList.map (m!"{·}")) m!"\n")}"

    -- From here on, the pipeline is that of the former `#synthesize`.
    let decl ← withArityUnfold config.monomorphize do
      PBE.toProblem fname.toString f type examples consts config

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
        -- The equations only sample the clauses: attempt to prove each clause
        -- about the candidate, let-bound under the function's name. Proofs
        -- delaborate referring to the function by name, which, once the
        -- suggestion below is applied, resolves to the definition itself.
        let thmCmds ← PBP.provePredicatesLetBound fname type candidate f
          (predicates.map fun (t, e, _, _) => (t, e)) consts timeout
        if thmCmds.isEmpty then
          addExactSuggestionR2M ref candidate type
        else
          -- The proofs were checked against the candidate itself, which the
          -- pasted definition must therefore unfold to: suggest the raw term.
          -- A `match`/`let rec` rendering compiles through `brecOn` and
          -- auxiliary matchers, against which proofs that inline the raw
          -- recursors in their motives need not re-elaborate.
          TryThis.addExactSuggestion ref candidate
          let text := "\n\n".intercalate (← thmCmds.toList.mapM fun cmd =>
            return (← PrettyPrinter.ppCommand cmd).pretty)
          logInfo m!"the synthesized function provably satisfies \
            {thmCmds.size}/{predicates.size} clause(s); paste after the \
            definition:\n\n{text}"
      Elab.admitGoal goal

end

end Canonical.Synth

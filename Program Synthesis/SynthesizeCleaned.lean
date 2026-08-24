module

public meta import ProgramByPredicateCleaned
public meta import Canonical.Refine
public meta import Canonical.Destruct.Basic

open Lean Parser Tactic Meta Elab Tactic Core Monomorphize

namespace Canonical.Synth

public meta section

/-! # The `synthesize` tactic (cleaned)

Uses `ProgramByPredicateCleaned.lean` and does not reduce, convert, or
deduplicate instantiated examples before translation. The original
`Synthesize.lean` is unchanged.

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
in `ProgramByExample.lean` and `ProgramByPredicateCleaned.lean`).

The instantiated equations become equational constraints on the declaration
under synthesis (`PBE.toProblem`), and Canonical searches for a function of
the goal type satisfying them. Like `canonical`, the tactic then admits the
goal and offers each function found as a `Try this: exact …` suggestion.
The instantiated equations only *sample* quantified clauses: each candidate
is re-checked against them by definitional equality (a failure produces a
warning), but the clauses themselves are not verified — a function
satisfying every sample need not satisfy the predicates.

A clause may also carry an existential block, `∀ x₁ … xₙ, ∃ y : T, …`: the
`∃`-binder is skolemized into a fresh skolem function `y : ∀ x₁ … xₙ, T`
synthesized alongside the declaration (see `ProgramByPredicateCleaned.lean`), and
the found witnesses are reported as info messages. -/

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

/-- A single specification clause: `| ∀ x₁ … xₙ, ∃ y₁ … yₘ, f a₁ … aₘ = b`
    (the existential block is optional). A clause without binders is an
    ordinary input–output example. -/
syntax synthClause := "| " term

/-- `synthesize`, in the body of `def f : T := by synthesize`, followed by
    `| ∀ x₁ … xₙ, f a₁ … aₘ = b` clauses, searches for a function of type `T`
    satisfying all of the clauses and suggests it as `exact …`. In the clauses
    `f` refers to the definition's own name. Each quantified clause is
    instantiated with concrete inputs enumerated by Canonical; a clause
    without binders is an ordinary input–output example. A clause may carry an
    existential block, `∀ x₁ … xₙ, ∃ y : T', f a₁ … aₘ = b`: the `∃`-binder is
    skolemized into a skolem function `y : ∀ x₁ … xₙ, T'` that is synthesized
    together with `f`, and the found witnesses are reported. The instantiated
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
elab (name := synthesizeCleanedTac) "synthesize " timeout?:(num)? debug?:(synthDebug)?
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

    -- Skolemize the existential block of each clause: `∃ y : T` becomes a
    -- fresh local `y : ∀ x₁ … xₙ, T` — a skolem function that is an unknown
    -- under synthesis alongside the declaration — and `y` is applied to the
    -- universal binders in the body (`PBP.skolemizeClause`). Clauses without
    -- `∃` pass through unchanged.
    let skolemized ← elaborated.mapM fun (t, e) => withRef t do
      pure (t, ← PBP.skolemizeClause e)
    let lctx ← getLCtx
    let skolemInfos := Id.run do
      let mut used : NameSet := {}
      let mut infos : Array (Name × Lean.Expr) := #[]
      for (_, ws, _) in skolemized do
        for (y, ty) in ws do
          let mut name := lctx.getUnusedName y
          let mut i := 1
          while used.contains name do
            name := (lctx.getUnusedName y).appendIndexAfter i
            i := i + 1
          used := used.insert name
          infos := infos.push (name, ty)
      return infos
    withLocalDeclsD (skolemInfos.map fun (name, ty) => (name, fun _ => pure ty))
        fun skolems => do
      -- Reattach each clause's skolem functions.
      let clauses := Id.run do
        let mut offset := 0
        let mut out : Array (Term × Lean.Expr) := #[]
        for (t, ws, fn) in skolemized do
          out := out.push (t, fn.beta (skolems.extract offset (offset + ws.size)))
          offset := offset + ws.size
        return out

      -- The function under synthesis is the head of the clauses' left-hand
      -- sides: the auxiliary local constant standing for the definition being
      -- elaborated. It plays the role the fresh local `f` played in the former
      -- commands — `toProblem` renames it to the declaration name, and the
      -- local-context fold excludes auxiliary declarations from the premises.
      let f ← do
        let (t, e) := clauses[0]!
        let (_, body) := PBP.binderTypesAndBody e
        let some (_, lhs, _) := body.eq?
          | throwErrorAt t "a clause must be a universally quantified equation \
              `∀ x₁ … xₙ, ∃ y₁ … yₘ, f a₁ … aₘ = b` about the function being defined"
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
      let predicates ← clauses.mapM fun (t, e) => do
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
              `∀ x₁ … xₙ, ∃ y₁ … yₘ, {fname} a₁ … aₘ = b`"
        unless lhs.getAppFn == f do
          throwErrorAt t "the left-hand side of a clause must be an application of `{fname}`"
        pure (t, e, binderTypes, body)

      -- Instantiate each clause with enumerated example inputs. The enumeration
      -- runs in an empty local context so that neither `{fname}` nor other local
      -- variables can occur in the example inputs. Ground reduction, numeral
      -- expansion, and duplicate/trivial filtering are left to translation
      -- (`toTerm`/`whnf` and `PBE.toProblem_`).
      let mut examples : Array Lean.Expr := #[]
      for (t, _, binderTypes, body) in predicates do
        let inputs ← withLCtx {} #[] do PBP.enumerateInputs binderTypes k
        if inputs.isEmpty then
          throwErrorAt t "could not enumerate example inputs for the quantified variables"
        for vals in inputs do
          examples := examples.push (body.instantiateRev vals)
      -- A numeral above `MAX_CTOR_NAT` stays an opaque literal the solver cannot
      -- compute with (`toProblem_` leaves it alone), so an example containing
      -- one is unsatisfiable and would poison the whole search.
      let (kept, dropped) := examples.partition fun ex =>
        (ex.find? fun sub =>
          if let .lit (.natVal n) := sub then n > PBE.MAX_CTOR_NAT else false).isNone
      for ex in dropped do
        logWarning m!"ignoring the example `{ex}`: it contains a numeral larger than \
          {PBE.MAX_CTOR_NAT}, which the search cannot compute with"
      examples := kept
      if examples.isEmpty then
        throwError "every instantiated example contains a numeral larger than \
          {PBE.MAX_CTOR_NAT}, which the search cannot compute with"
      logInfo m!"instantiated {examples.size} example equation(s):{indentD
        (MessageData.joinSep (examples.toList.map (m!"{·}")) m!"\n")}"

      if skolems.isEmpty then
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
              unless ← PBE.satisfiesExample #[f] #[candidate] ex do
                logWarning m!"the synthesized term{indentExpr candidate}\ndoes not satisfy \
                  the instantiated example `{ex}`"
            let candidate := (← PBP.pinCandidate? candidate).getD candidate
            TryThis.addExactSuggestion ref candidate
          Elab.admitGoal goal
      else
        -- The declaration and the skolem functions are synthesized jointly, as
        -- one term of the CPS form of the tuple `T ×' T_y₁ ×' …` — the same
        -- `dneg` transformation `destruct` applies to structure goals. Each
        -- instantiated example is rewritten to select its unknowns out of the
        -- tuple by continuation (`PBP.wrapUnknowns`), which β-reduction alone
        -- evaluates once a candidate is substituted.
        if type.hasFVar then
          throwError "the goal type must be closed when a clause contains `∃` — it \
            may not mention local variables{indentExpr type}"
        let unknowns := #[f] ++ skolems
        let compTypes := #[type] ++ skolemInfos.map (·.2)
        let chainType ← compTypes.pop.foldrM (init := compTypes.back!) fun t acc =>
          mkAppM ``PProd #[t, acc]
        let some (cpsGoal, _) ← withLCtx {} #[] do
            Destruct.destructCanonical (← mkFreshExprMVar chainType).mvarId! #[]
          | throwError "internal error: the tuple goal for the skolem functions \
              did not destruct"
        let cpsType ← instantiateMVars (← cpsGoal.getType)
        -- `destruct` recurses into the component types and would also unpack
        -- structure types (`Prod`, `Fin`, `Subtype`, …) occurring in them,
        -- breaking the correspondence with the wrapped examples; insist on
        -- exactly one continuation binder per unknown.
        let shapeOk ← forallBoundedTelescope cpsType (some 2) fun ds body => do
          if ds.size != 2 || body != ds[0]! then return false
          forallBoundedTelescope (← inferType ds[1]!) (some (compTypes.size + 1))
              fun ks kbody => do
            if ks.size != compTypes.size || kbody != ds[0]! then return false
            for (kk, t) in ks.zip compTypes do
              unless ← isDefEq (← inferType kk) t do return false
            return true
        unless shapeOk do
          throwError "the signature of `{fname}` or the type of an existential \
            variable contains structure types that the tuple transformation would \
            unpack; this is not supported with `∃` clauses"
        withLocalDeclD ((← getLCtx).getUnusedName `g) cpsType fun g => do
          let wrapped ← examples.mapM fun ex => PBP.wrapUnknowns g unknowns ex
          let decl ← withArityUnfold config.monomorphize do
            PBE.toProblem fname.toString g cpsType wrapped consts config
              (excluded := skolems)

          if config.debug then
            Elab.admitGoal goal
            save_problem decl "debug.json"
            return

          -- Refinement UI on the tuple problem; the reconstruction projects the
          -- declaration's component out of the CPS tuple.
          if config.refine then
            let _ ← Canonical.refine decl
            let (width, indent, column, range) ← widthIndentColumnRange
            let x : Server.WithRpcRef RpcData ← Server.WithRpcRef.mk {
              mctx := ← getMCtx, mainGoal := goal, config,
              reconstruct := fun e => do
                let e ← PBP.projectComponent e compTypes 0
                return (← PBP.pinCandidate? e).getD e,
              width, indent, column, processedGoal := cpsGoal
            }
            Elab.admitGoal goal
            Widget.savePanelWidgetInfo (hash refineWidget.javascript) ref (props := do
              let rpcData ← Server.RpcEncodable.rpcEncode x
              return Json.mkObj [("rpcData", rpcData), ("range", ToJson.toJson range)])
            return

          let result ← runCanonical decl timeout config

          let tuples ← withArityUnfold config.monomorphize do
            result.terms.mapM (fromCanonical · cpsType)

          if tuples.isEmpty then
            throwError "No function found. Increase the timeout with `synthesize \
              {timeout.toNat * 2}`, add clauses, increase `(examples := n)`, or supply \
              premises with `synthesize [name, …]`"

          withOptions applyOptions do
            for tuple in tuples do
              let components ← compTypes.mapIdxM fun i _ =>
                PBP.projectComponent tuple compTypes i
              for ex in examples do
                unless ← PBE.satisfiesExample unknowns components ex do
                  logWarning m!"the synthesized term{indentExpr components[0]!}\ndoes not \
                    satisfy the instantiated example `{ex}`"
              for i in [1:components.size] do
                let w := (← PBP.pinCandidate? components[i]!).getD components[i]!
                logInfo m!"{skolems[i-1]!} := {w}"
              let candidate := (← PBP.pinCandidate? components[0]!).getD components[0]!
              TryThis.addExactSuggestion ref candidate
            Elab.admitGoal goal

end

end Canonical.Synth

module

public meta import Lean

open Lean Meta PrettyPrinter Delaborator SubExpr

namespace Canonical.R2M

public meta section

/-! # Recursor applications as `match` syntax

Canonical returns β-normal η-long terms whose head symbols are often recursors.
For display in the Program Synthesis commands, eligible recursor applications are
rendered as `match` statements instead. The conversion is a pretty-printing
concern only: it is implemented as an `app`-delaborator gated behind the
`canonical.recToMatch` option, which only the Program Synthesis display code
enables (the `canonical` tactic is unaffected). Any ineligible or unexpected
shape makes the delaborator fail, falling back to the builtin application
delaborator — today's raw recursor display — for that node only.
See `RecursorToMatch.md` for the design. -/

/-- The option enabling the recursor→match delaborator. Deliberately not
    registered: it is an internal toggle set programmatically by `withR2M`,
    not a user-facing `set_option`. -/
def r2mOption : Name := `canonical.recToMatch

def getR2M (o : Options) : Bool := o.getBool r2mOption false

/-- Run `x` with the recursor→match delaborator enabled. -/
def withR2M [MonadWithOptions m] (x : m α) : m α :=
  withOptions (·.setBool r2mOption true) x

/-- `PrettyPrinter.delab` with recursor applications rendered as `match` syntax. -/
def delabR2M (e : Expr) : MetaM Term := withR2M do PrettyPrinter.delab e

/-- `delabR2M` for a constructor pattern: field notation is disabled because
    e.g. `k.succ` is not valid pattern syntax. -/
def delabPatternM (e : Expr) : MetaM Term :=
  withOptions (pp.fieldNotation.set · false) (delabR2M e)

/-- A fully-applied application of a supported recursor: a single non-indexed
    inductive with one motive. -/
structure RecApp where
  rv : RecursorVal
  /-- Universe levels the recursor is applied at. -/
  levels : List Level
  /-- Levels for the constructors: the recursor's levels minus the leading
      motive level, when the inductive is large-eliminating. -/
  ctorLevels : List Level
  params : Array Expr
  motive : Expr
  /-- The minor premises, in constructor (`rv.rules`) order. -/
  minors : Array Expr
  major : Expr
  /-- Arguments applied beyond the major premise (the motive returns a function type). -/
  extras : Array Expr
  /-- For each minor premise, the field index each inductive hypothesis recurses on.
      In a minor premise the fields come first, then one hypothesis per recursive field. -/
  ihFields : Array (Array Nat)

/-- The constructor of minor `i` applied to the recursor's parameters and `fields`,
    for delaborating into the match pattern. -/
def RecApp.ctorApp (ra : RecApp) (i : Nat) (fields : Array Expr) : Expr :=
  mkAppN (mkConst (ra.rv.rules[i]!).ctor ra.ctorLevels) (ra.params ++ fields)

/-- Decompose `e` into a supported recursor application, or `none` if any
    eligibility check fails (not a `.rec`, indexed or mutual/nested inductive,
    multiple motives, under-applied, reflexive inductive hypotheses, …). -/
def analyzeRecApp? (e : Expr) : MetaM (Option RecApp) := do
  let .const c us := e.getAppFn | return none
  let some (.recInfo rv) := (← getEnv).find? c | return none
  unless rv.numMotives == 1 && rv.numIndices == 0 && rv.all.length == 1 do return none
  unless us.length == rv.levelParams.length do return none
  let args := e.getAppArgs
  unless args.size ≥ rv.getMajorIdx + 1 do return none
  -- The recursor's levels are the motive level (for large elimination) followed
  -- by the inductive's own levels.
  let numIndLevels := (← getConstInfoInduct rv.all[0]!).levelParams.length
  unless numIndLevels ≤ us.length && us.length - numIndLevels ≤ 1 do return none
  let ctorLevels := us.drop (us.length - numIndLevels)
  -- Read the field/hypothesis structure of each minor premise off the recursor's
  -- own type, where the motive is a bound variable: each hypothesis binder must
  -- have type `motive fld` for one of the field binders (a reflexive inductive
  -- has `∀ a, motive (fld a)` hypotheses, which head replacement cannot express).
  let recType := rv.type.instantiateLevelParams rv.levelParams us
  let ihFields? ← forallBoundedTelescope recType (some (rv.numParams + 1)) fun ps body =>
    forallBoundedTelescope body (some rv.numMinors) fun minorVars _ => do
      let some motiveVar := ps[rv.numParams]? | return none
      let mut result : Array (Array Nat) := #[]
      for i in [0:rv.numMinors] do
        let some minorVar := minorVars[i]? | return none
        let some rule := rv.rules[i]? | return none
        let idxs? ← forallTelescope (← minorVar.fvarId!.getType) fun bs _ => do
          if bs.size < rule.nfields then return none
          let flds := bs.extract 0 rule.nfields
          let mut idxs : Array Nat := #[]
          for ih in bs.extract rule.nfields bs.size do
            let .app fn fld := (← ih.fvarId!.getType) | return none
            unless fn == motiveVar do return none
            let some j := flds.idxOf? fld | return none
            idxs := idxs.push j
          return some idxs
        let some idxs := idxs? | return none
        result := result.push idxs
      return some result
  let some ihFields := ihFields? | return none
  return some {
    rv, levels := us, ctorLevels
    params := args.extract 0 rv.numParams
    motive := args[rv.numParams]!
    minors := args.extract (rv.numParams + 1) (rv.numParams + 1 + rv.numMinors)
    major := args[rv.getMajorIdx]!
    extras := args.extract (rv.getMajorIdx + 1) args.size
    ihFields
  }

/-- Enter exactly `num` leading λ-binders of `e`, introducing each as a local
    variable with a name freshened against the current context, so that
    delaborated output cannot shadow or capture variables bound further out.
    η-long terms from Canonical always carry these binders syntactically;
    anything else (including an `.mdata`-wrapped attribution) throws, which
    callers turn into a fallback to the raw display. -/
def withFreshBinders [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]
    (e : Expr) (num : Nat) (k : Array Expr → Expr → n α) : n α :=
  go num e #[]
where
  go : Nat → Expr → Array Expr → n α
  | 0, e, acc => k acc e
  | num + 1, e, acc => do
    let .lam bn bt body bi := e
      | liftM (throwError "expected a λ-binder in{indentExpr e}" : MetaM α)
    let bn := bn.eraseMacroScopes
    let bn := (← liftM (getLCtx : MetaM _)).getUnusedName (if bn.isAnonymous then `a else bn)
    withLocalDecl bn bi bt fun fv => go num (body.instantiate1 fv) (acc.push fv)

/-- Enter minor `i` of `ra` with `nExtras` residual binders beyond the fields and
    inductive hypotheses, replacing each hypothesis (recursing on field `fld`)
    with `recCall fld` in the body. Continues with the fields, the residual
    binders, and the substituted body. -/
def withMinorAlt [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]
    (ra : RecApp) (i : Nat) (nExtras : Nat) (recCall : Expr → Expr)
    (k : (fields zs : Array Expr) → (body : Expr) → n α) : n α := do
  let nf := (ra.rv.rules[i]!).nfields
  let nih := ra.ihFields[i]!.size
  withFreshBinders ra.minors[i]! (nf + nih + nExtras) fun bs body => do
    let flds := bs.extract 0 nf
    let mut b := body
    for j in [0:nih] do
      b := b.replaceFVar bs[nf + j]! (recCall flds[ra.ihFields[i]![j]!]!)
    k flds (bs.extract (nf + nih) bs.size) b

/-- Whether any minor premise actually uses one of its inductive hypotheses.
    Recursors whose hypotheses are all unused are case analyses and render as
    plain `match` statements. -/
def isRecursiveApp (ra : RecApp) : MetaM Bool := do
  for i in [0:ra.minors.size] do
    let nf := (ra.rv.rules[i]!).nfields
    let nih := ra.ihFields[i]!.size
    let recursive ← withFreshBinders ra.minors[i]! (nf + nih) fun bs body =>
      pure ((bs.extract nf (nf + nih)).any fun ih => body.containsFVar ih.fvarId!)
    if recursive then return true
  return false

/-- Delaborate `e` at the current position (the standard subterm-swap; position
    duplication only affects hover info, which suggestions do not use). -/
def delabSub (e : Expr) : Delab :=
  withTheReader SubExpr (fun ctx => { ctx with expr := e }) delab

/-- Delaborate a constructor pattern. Field notation is disabled because e.g.
    `k.succ` is not valid pattern syntax. -/
def delabPattern (e : Expr) : Delab :=
  withOptions (pp.fieldNotation.set · false) (delabSub e)

/-- Render a non-recursive recursor application as a `match` statement. Residual
    arguments applied beyond the major premise are β-pushed into the branches. -/
def delabCases (ra : RecApp) : Delab := do
  let discr ← withNaryArg ra.rv.getMajorIdx delab
  let mut patss : Array (Array Term) := #[]
  let mut rhss : Array Term := #[]
  for i in [0:ra.minors.size] do
    let (pat, rhs) ← withMinorAlt ra i ra.extras.size (fun fld => fld) fun flds zs body => do
      let pat ← delabPattern (ra.ctorApp i flds)
      let rhs ← delabSub (body.replaceFVars zs ra.extras)
      return (pat, rhs)
    patss := patss.push #[pat]
    rhss := rhss.push rhs
  let discrs := #[← `(Parser.Term.matchDiscr| $discr:term)]
  `(match $[$discrs:matchDiscr],* with $[| $patss,* => $rhss]*)

/-- Render a recursive recursor application as
    `let rec go : (x : I ps) → motive x := fun x => match x with …; go major extras`.
    Inductive hypotheses become calls to `go`, which recurses structurally on its
    argument, so the pasted definition elaborates. Residual arguments beyond the
    major premise stay applied to the call, with the matching binders left as
    lambdas in the branches. -/
def delabLetRec (ra : RecApp) : Delab := do
  let majorTy ← inferType ra.major
  let goName := (← getLCtx).getUnusedName `go
  let goTy ← withLocalDeclD `x majorTy fun x =>
    mkForallFVars #[x] (mkApp ra.motive x).headBeta
  withLocalDeclD goName goTy fun go => do
    let xName := (← getLCtx).getUnusedName `x
    withLocalDeclD xName majorTy fun xv => do
      let mut patss : Array (Array Term) := #[]
      let mut rhss : Array Term := #[]
      for i in [0:ra.minors.size] do
        let (pat, rhs) ← withMinorAlt ra i 0 (mkApp go) fun flds _zs body => do
          let pat ← delabPattern (ra.ctorApp i flds)
          let rhs ← delabSub body
          return (pat, rhs)
        patss := patss.push #[pat]
        rhss := rhss.push rhs
      let discrs := #[← `(Parser.Term.matchDiscr| $(← delabSub xv):term)]
      let matchStx ← `(match $[$discrs:matchDiscr],* with $[| $patss,* => $rhss]*)
      let callStx ← delabSub (mkAppN (mkApp go ra.major) ra.extras)
      let goId := mkIdent goName
      let xId := mkIdent xName
      `(let rec $goId:ident : $(← delabSub goTy) := fun $xId:ident => $matchStx;
        $callStx)

/-- Render eligible recursor applications as `match` syntax, when the
    `canonical.recToMatch` option is set. Anything unsupported fails over to the
    builtin application delaborator, i.e. the raw recursor display. -/
@[delab app]
def delabRecToMatch : Delab := whenPPOption getR2M do
  let some ra ← analyzeRecApp? (← getExpr) | failure
  try
    if ra.minors.isEmpty then
      -- `False.rec`, `Empty.rec`
      let discr ← withNaryArg ra.rv.getMajorIdx delab
      `(nomatch $discr)
    else if ← isRecursiveApp ra then
      delabLetRec ra
    else
      delabCases ra
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex else failure

/-! ## The `def` suggestion builder -/

/-- The number of leading λ-binders. -/
def numLambdas : Expr → Nat
  | .lam _ _ b _ => numLambdas b + 1
  | _ => 0

/-- Render a synthesized body `t` whose head is a recursive elimination of one
    of its own argument binders as definition-level equations, in the style of

    ```
    def add : Nat → Nat → Nat
      | n, Nat.zero => n
      | n, Nat.succ k => (add n k).succ
    ```

    Each equation is the ι-reduction of the recursor at one constructor, with the
    inductive hypotheses renamed to recursive calls of `f` (the local variable
    standing for the function under synthesis, whose user name is the definition's
    name). Returns `none` when the shape does not fit (then the body is rendered
    `:=`-style instead): the major premise must be one of the binders, any
    residual arguments must be exactly the trailing binders in order, and the
    parameters and motive may not depend on the binders. -/
def mkEquationDef? (fnameId : Ident) (sig : Term) (f t : Expr) :
    MetaM (Option (TSyntax `command)) := do
  let k := numLambdas t
  if k == 0 then return none
  withFreshBinders t k fun xs body => do
    let some ra ← analyzeRecApp? body | return none
    if ra.minors.isEmpty then return none
    unless ← isRecursiveApp ra do return none
    let m := ra.extras.size
    unless m ≤ k && ra.extras == xs.extract (k - m) k do return none
    let prefixArgs := xs.extract 0 (k - m)
    let some j := prefixArgs.idxOf? ra.major | return none
    if ra.params.any (fun p => xs.any fun x => p.containsFVar x.fvarId!) then return none
    if xs.any (fun x => ra.motive.containsFVar x.fvarId!) then return none
    let mut patss : Array (Array Term) := #[]
    let mut rhss : Array Term := #[]
    for i in [0:ra.minors.size] do
      let recCall := fun fld => mkAppN f (prefixArgs.set! j fld)
      let (pats, rhs) ← withMinorAlt ra i m recCall fun flds zs body => do
        -- In this equation, the major is the constructor value and the residual
        -- binders stand for the trailing arguments, so occurrences of the outer
        -- binders at those positions are rewritten accordingly.
        let ctorVal := ra.ctorApp i flds
        let body := (body.replaceFVar ra.major ctorVal).replaceFVars (xs.extract (k - m) k) zs
        let mut pats : Array Term := #[]
        for i' in [0:k] do
          pats := pats.push <| ← if i' == j then
              delabPatternM ctorVal
            else
              patVar (if i' < k - m then xs[i']! else zs[i' - (k - m)]!) body
        return (pats, ← delabR2M body)
      patss := patss.push pats
      rhss := rhss.push rhs
    some <$> `(command| def $fnameId:ident : $sig:term $[| $patss,* => $rhss]*)
where
  /-- The variable pattern for `x`: its name, or `_` if the right-hand side does
      not mention it (avoiding unused-variable warnings in the pasted code). -/
  patVar (x : Expr) (rhs : Expr) : MetaM Term := do
    if rhs.containsFVar x.fvarId! then
      return mkIdent (← x.fvarId!.getUserName)
    else
      `(_)

/-- Whether the delaborated `stx` elaborates back to a term of `type`
    definitionally equal to `orig`; if not, the conversion is discarded.
    The comparison uses the kernel, which — unlike `Meta.isDefEq` — sees through
    the auxiliary matcher applications that `match` elaborates to. `let rec`
    cannot be elaborated outside a definition, so those conversions are accepted
    as-is: they are correct by construction and covered by the build-time paste
    tests in `RecursorToMatch/Examples.lean`. -/
def roundTrips (stx : Term) (orig type : Expr) : Elab.TermElabM Bool := do
  if (stx.raw.find? (·.isOfKind ``Parser.Term.letrec)).isSome then return true
  try
    withoutModifyingState do Elab.Term.withoutErrToSorry do
      -- Canonical does not translate universe levels, so `orig` may carry
      -- unassigned level metavariables; checking pins them by unification.
      check orig
      let orig ← instantiateMVars orig
      if orig.hasExprMVar || orig.hasLevelMVar then return false
      let e ← Elab.Term.elabTermEnsuringType stx (some type)
      Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasSorry || e.hasExprMVar || e.hasLevelMVar then return false
      return Kernel.isDefEqGuarded (← getEnv) (← getLCtx) e orig
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    return false

/-- Build the `def` suggestion for a synthesized body `t : type`. `f` is the
    local variable standing for the function under synthesis. A top-level
    recursive elimination becomes definition-level equations; otherwise the
    body is rendered `:=`-style with recursor applications as `match` syntax,
    kept only if it re-elaborates to the same function; any failure falls back
    to today's raw display. -/
def mkDefCommand (fnameId : Ident) (sig : Term) (f t type : Expr) :
    Elab.TermElabM (TSyntax `command) := do
  try
    if let some cmd ← mkEquationDef? fnameId sig f t then
      return cmd
    let body ← delabR2M t
    if ← roundTrips body t type then
      return ← `(command| def $fnameId:ident : $sig:term := $body:term)
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
  let body ← PrettyPrinter.delab t
  `(command| def $fnameId:ident : $sig:term := $body:term)

end

end Canonical.R2M

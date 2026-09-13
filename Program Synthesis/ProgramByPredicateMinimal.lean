module

public meta import ProgramByExample
public meta import Canonical.Destruct.Basic
public meta import Canonical.Tactic
import Lean.Elab.Tactic.Config

open Lean Meta Elab Tactic

namespace Canonical.Predicate

public meta section

/-! # Programming by predicate

`def f : T := by synthesize | clause …` searches for a function of type `T` satisfying the
clauses: first-order formulas about `f` built from `∀` and `∃` (nested in any order), `∧`, and
equations. The hypothesis “a program satisfying the clauses exists” is Skolemized by `destruct`:
each `∃` becomes a Skolem function of the enclosing universals, `∧` is split, and the
universally quantified equations that remain are sampled at inputs enumerated by Canonical.
The ground equations then constrain a joint search for `f` and the Skolem functions, packed as
a CPS tuple `∀ D, (T → T_y → … → D) → D`, with each equation side selecting its unknowns out of
the tuple by continuation. Only the samples are checked, not the clauses themselves. -/

structure Config where
  /-- Sample instantiations per universally quantified equation. -/
  examples : Nat := 3

declare_config_elab elabConfig Config

/-- The first `count` inhabitants of the closed type `type`, in search order. -/
def enumerate (type : Lean.Expr) (count : Nat) (timeout : UInt64 := 5) : MetaM (Array Lean.Expr) := withLCtx {} #[] do
  let config : Canonical.Config := { count := USize.ofNat count, destruct := false }
  let result ← runCanonical { name := "enumerate", type := some (← toCanonical type #[] #[] config) } timeout config
  result.terms.mapM fun t => do instantiateMVars (← fromCanonical t type)

/-- The `n` components of a right-nested `PSigma.mk` spine. -/
partial def components : Lean.Expr → Nat → Array Lean.Expr
  | t, n + 2 => match t.getAppFnArgs with
    | (``PSigma.mk, #[_, _, a, b]) => #[a] ++ components b (n + 1)
    | _ => #[t]
  | t, _ => #[t]

syntax clause := "| " term

/-- `synthesize`, in the body of `def f : T := by synthesize …`, followed by `| clause` lines
    about `f`, searches for a function of type `T` satisfying the clauses and suggests it as
    `exact …`. Clauses are first-order formulas built from `∀`, `∃`, `∧`, and equations; each
    universally quantified equation is sampled at `(examples := n)` (default 3) inputs enumerated
    by Canonical, and existential witnesses are synthesized alongside `f` and reported. An
    optional numeral sets the timeout in seconds, and `[name, …]` supplies premises. -/
elab "synthesize " timeout?:(num)? config:Parser.Tactic.optConfig premises?:(Canonical.premises)? clauses:clause* : tactic => withMainContext do
  let some f ← (← getLCtx).findDeclM? (fun d => pure (if d.isAuxDecl then some d.toExpr else none))
    | throwError "`synthesize` must be used in the body of a definition"
  let type ← getMainTarget
  unless ← isDefEq (← inferType f) type do
    throwError "move the binders of `{f}` to the right of the colon, so that the goal is its signature"
  let { examples } ← elabConfig config
  let timeout := (timeout?.map fun t => UInt64.ofNat t.getNat).getD 5
  let consts ← if let some consts := premises? then
      match consts with
      | `(Canonical.premises| [$args,*]) => args.getElems.raw.mapM resolveGlobalConstNoOverload
      | _ => throwUnsupportedSyntax
    else pure #[]
  let clauses ← clauses.mapM fun c => match c with
    | `(clause| | $t) => Tactic.elabTermEnsuringType t (some (mkSort .zero))
    | _ => throwUnsupportedSyntax
  -- Skolemize “a program satisfying the clauses exists” with `destruct` (`Exists` and `∧` only,
  -- so that structure types in the signature stay intact): the pieces are the unknowns and the
  -- universally quantified equations.
  let spec ← mkAppM ``Exists #[← mkLambdaFVars #[f] (mkAndN clauses.toList)]
  if spec.hasFVar then throwError "the clauses may only mention `{f}` and closed terms"
  withArityUnfold true do withLCtx {} #[] do withLocalDeclD `h spec fun _ => do
  let (fvars, m) := (← Destruct.destructTactic (← mkFreshExprMVar (mkConst ``False)).mvarId! #[``And]).2[0]!
  m.withContext do
  let fvars := fvars.map Lean.Expr.fvar
  let unknowns ← fvars.filterM fun x => return !(← isProof x)
  -- Sample each equation at enumerated inhabitants of the dependent tuple of its binders.
  let samples ← (← fvars.filterM (isProof ·)).flatMapM fun h => do forallTelescope (← inferType h) fun xs body => do
    if xs.isEmpty then return #[body]
    let tuple ← xs.pop.foldrM (init := ← inferType xs.back!) fun x t => do mkAppM ``PSigma #[← mkLambdaFVars #[x] t]
    let inputs ← enumerate tuple examples
    if inputs.isEmpty then throwError "could not enumerate inputs for{indentExpr (← inferType h)}"
    return inputs.map fun t => body.replaceFVars xs (components t xs.size)
  -- The unknowns are synthesized jointly as a CPS tuple, the shape `destruct` gives structure goals.
  let u ← getLevel type
  let cps ← withLocalDeclD `D (mkApp (mkConst ``STAR [.succ u]) (.sort u)) fun D => do
    mkForallFVars #[D] (mkForall `k .default (← mkForallFVars unknowns D) D)
  withLocalDeclD `g cps fun g => do
  let wrap (side : Lean.Expr) : MetaM Lean.Expr := do
    if unknowns.any (side.containsFVar ·.fvarId!) then
      return mkApp2 g (← inferType side) (← mkLambdaFVars unknowns side)
    else return side
  let equations ← samples.mapM fun s => do
    let some (_, lhs, rhs) := s.eq? | throwError "a clause must be an equation:{indentExpr s}"
    mkEq (← wrap lhs) (← wrap rhs)
  let config : Canonical.Config := { destruct := false }
  let name := ((← Term.getDeclName?).map toString).getD "f"
  let decl ← PBE.toProblem name g cps equations consts config (excluded := fvars)
  let values ← (← runCanonical decl timeout config).terms.mapM fun t => do
    let t ← fromCanonical t cps
    unknowns.mapM fun x => do Core.betaReduce (mkApp2 t (← inferType x) (← mkLambdaFVars unknowns x))
  for vs in values do for (x, v) in (unknowns.zip vs)[1:] do logInfo m!"{x} := {v}"
  present (values.map (·[0]!)) (← getMainGoal) premises? timeout?

end

end Canonical.Predicate

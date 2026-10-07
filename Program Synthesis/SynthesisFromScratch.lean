import Lean
import Canonical.Destruct.Basic

open Lean Elab Tactic Meta

/-- Drops every local declaration after the last auxiliary declaration, then builds a
metavariable of that declaration's type in the truncated context. -/
elab "alter_context" : tactic => withMainContext do
  -- Walks the lctx backwards until it finds an aux decl
  let some aux := (← getLCtx).findDeclRev? fun d => if d.isAuxDecl then some d else none
    | throwError "no auxiliary declaration in the local context"
  -- pops everything after the aux decl
  let mut lctx ← getLCtx
  while aux.index + 1 < lctx.numIndices do
    lctx := lctx.pop
  -- builds a mvar of the aux decl's type and truncated lctx
  let mvar ← mkFreshExprMVarAt lctx (← getLocalInstances) aux.type
  (← getMainGoal).modifyDecl fun decl => { decl with lctx }
  logInfo m!"{← ppGoal mvar.mvarId!}"
  -- destructs that mvar
  let (goal, _reconstruct) ← mvar.mvarId!.withContext do
    match ← Destruct.destructCanonical mvar.mvarId! #[] with
    | some result => pure result
    | none => pure (mvar.mvarId!, pure)
  -- some logs
  logInfo m!"{← ppGoal goal}"
  for decl in lctx do
    logInfo m!"{decl.userName}"

--def synthesize (inputTypes : List Type) (outputType : Type) (examples : List (List Type × outputType)) : MetaM Expr := sorry

def f (n : Nat) : Nat :=
  let rec g (m : Nat) : Nat := by
    alter_context
    exact n
  n

def h (n : Nat) : Nat :=
  let rec k (p : Nat × Nat) : Nat := by
    alter_context
    exact n
  n

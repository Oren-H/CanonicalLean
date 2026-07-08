import RecursorToMatch
import ProgramByExample

/-! Tests for the recursor→match conversion. The `#r2m_term` command elaborates
a term, delaborates it with the conversion enabled, and logs the result; each
test pins the exact output with `#guard_msgs`. -/

open Lean Elab Command in
elab "#r2m_term " t:term : command =>
  runTermElabM fun _ => do
    let e ← Term.elabTerm t none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let stx ← Canonical.R2M.delabR2M e
    logInfo (← PrettyPrinter.ppTerm stx)

open Lean Elab Command Meta in
elab "#r2m_def " id:ident " : " sig:term " := " t:term : command =>
  runTermElabM fun _ => do
    let type ← Term.elabType sig
    Term.synthesizeSyntheticMVarsNoPostponing
    let type ← instantiateMVars type
    withLocalDeclD id.getId type fun f => do
      let e ← Term.elabTermEnsuringType t type
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      let cmd ← Canonical.R2M.mkDefCommand id sig f e type
      logInfo (← PrettyPrinter.ppCommand cmd)

/-! ## Non-recursive eliminations (inline `match`) -/

-- Case analysis on `Nat`; the inductive hypothesis is unused.
/--
info: fun n =>
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
-/
#guard_msgs in
#r2m_term fun n => Nat.rec (motive := fun _ => Nat) Nat.zero (fun k _ih => k) n

-- Case analysis on `Bool`.
/--
info: fun b =>
  match b with
  | false => true
  | true => false
-/
#guard_msgs in
#r2m_term fun b => Bool.rec (motive := fun _ => Bool) Bool.true Bool.false b

-- Parameters and implicit constructor arguments (`List`).
/--
info: fun l d =>
  match l with
  | [] => d
  | a :: _as => a
-/
#guard_msgs in
#r2m_term fun (l : List Nat) (d : Nat) => List.rec (motive := fun _ => Nat) d (fun a _as _ih => a) l

-- A functional motive: the argument applied beyond the major premise is
-- β-pushed into the branches.
/--
info: fun b x y =>
  match b with
  | false => x
  | true => y
-/
#guard_msgs in
#r2m_term fun (b : Bool) (x y : Nat) =>
  Bool.rec (motive := fun _ => Nat → Nat) (fun _ => x) (fun z => z) b y

-- An empty inductive becomes `nomatch`.
/-- info: fun α h => nomatch h -/
#guard_msgs in
#r2m_term fun (α : Type) (h : False) => False.rec (motive := fun _ => α) h

-- A recursor nested inside another term still converts.
/--
info: fun n =>
  (match n with
    | Nat.zero => Nat.zero
    | Nat.succ k => k).succ
-/
#guard_msgs in
#r2m_term fun n => Nat.succ (Nat.rec (motive := fun _ => Nat) Nat.zero (fun k _ih => k) n)

/-! ## Ineligible shapes fall back to the raw display -/

-- `Eq.rec` eliminates an indexed family: unchanged.
/-- info: fun a b h => h ▸ rfl -/
#guard_msgs in
#r2m_term fun (a b : Nat) (h : a = b) => Eq.rec (motive := fun x _ => x = a) rfl h

/-! ## Recursive eliminations (`let rec`) -/

-- Addition by recursion on the first argument. (The linter warning would be
-- about the unused binder `k` in the test *input*, not about the output.)
/--
info: fun n m =>
  let rec go : Nat → Nat := fun x =>
    match x with
    | Nat.zero => m
    | Nat.succ k => (go k).succ;
  go n
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_term fun n m => Nat.rec (motive := fun _ => Nat) m (fun k ih => Nat.succ ih) n

-- A functional motive: the residual argument stays applied to the `go` call,
-- and the inductive hypothesis picks its arguments up by application.
/--
info: fun n m =>
  let rec go : Nat → Nat → Nat := fun x =>
    match x with
    | Nat.zero => fun m' => m'
    | Nat.succ k => fun m' => (go k m').succ;
  go n m
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_term fun n m =>
  Nat.rec (motive := fun _ => Nat → Nat) (fun m' => m') (fun k ih m' => Nat.succ (ih m')) n m

-- `List.length`, with the recursive elimination nested inside another term.
/--
info: fun l =>
  (let rec go : List Nat → Nat := fun x =>
      match x with
      | [] => Nat.zero
      | _a :: _as => (go _as).succ;
    go l).succ
-/
#guard_msgs in
#r2m_term fun (l : List Nat) =>
  Nat.succ (List.rec (motive := fun _ => Nat) Nat.zero (fun _a _as ih => Nat.succ ih) l)

/-! ## `def` suggestions -/

-- Recursion on the second argument becomes definition-level equations.
/--
info: def add : Nat → Nat → Nat
  | n, Nat.zero => n
  | n, Nat.succ k => (add n k).succ
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_def add : Nat → Nat → Nat :=
  fun n m => Nat.rec (motive := fun _ => Nat) n (fun k ih => Nat.succ ih) m

-- A functional motive: recursion on the first argument, with the second
-- argument bound by the minor premises' residual binders.
/--
info: def addc : Nat → Nat → Nat
  | Nat.zero, m' => m'
  | Nat.succ k, m' => (addc k m').succ
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_def addc : Nat → Nat → Nat :=
  fun n m => Nat.rec (motive := fun _ => Nat → Nat) (fun m' => m') (fun k ih m' => Nat.succ (ih m')) n m

-- A minor premise referencing an outer binder at a residual-argument position:
-- the occurrence is rewritten to that equation's own pattern variable.
/--
info: def cases0 : Nat → Nat → Nat
  | Nat.zero, m' => m'
  | Nat.succ k, m' => cases0 k m'
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_def cases0 : Nat → Nat → Nat :=
  fun n m => Nat.rec (motive := fun _ => Nat → Nat) (fun m' => m) (fun k ih m' => ih m') n m

-- Recursion over `List`.
/--
info: def mapSucc : List Nat → List Nat
  | [] => []
  | a :: as => a.succ :: mapSucc as
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_def mapSucc : List Nat → List Nat :=
  fun l => List.rec (motive := fun _ => List Nat) List.nil (fun a as ih => List.cons (Nat.succ a) ih) l

-- A non-recursive body stays `:=`-style, with the elimination as inline `match`.
/--
info: def pred : Nat → Nat := fun n =>
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
-/
#guard_msgs in
#r2m_def pred : Nat → Nat :=
  fun n => Nat.rec (motive := fun _ => Nat) Nat.zero (fun k _ih => k) n

-- The recursive elimination is nested under another application, where
-- equations cannot reach: it is rendered as `let rec` in a `:=`-style body.
/--
info: def double : Nat → Nat := fun n =>
  (let rec go : Nat → Nat := fun x =>
      match x with
      | Nat.zero => Nat.zero
      | Nat.succ k => (go k).succ.succ;
    go n).succ
-/
#guard_msgs in
set_option linter.unusedVariables false in
#r2m_def double : Nat → Nat :=
  fun n => Nat.rec (motive := fun _ => Nat) Nat.zero (fun k ih => Nat.succ (Nat.succ ih)) n |>.succ

/-! ## The suggested text elaborates and computes when pasted -/

def add' : Nat → Nat → Nat := fun n m =>
  let rec go : Nat → Nat := fun x =>
    match x with
    | Nat.zero => m
    | Nat.succ k => (go k).succ;
  go n

example : add' 3 4 = 7 := rfl

def lengthSucc' : List Nat → Nat := fun l =>
  (let rec go : List Nat → Nat := fun x =>
      match x with
      | [] => Nat.zero
      | _a :: _as => (go _as).succ;
    go l).succ

example : lengthSucc' [5, 6, 7] = 4 := rfl

def add2 : Nat → Nat → Nat
  | n, Nat.zero => n
  | n, Nat.succ k => (add2 n k).succ

example : add2 3 4 = 7 := rfl

def addc2 : Nat → Nat → Nat
  | Nat.zero, m' => m'
  | Nat.succ k, m' => (addc2 k m').succ

example : addc2 3 4 = 7 := rfl

def mapSucc2 : List Nat → List Nat
  | [] => []
  | a :: as => a.succ :: mapSucc2 as

example : mapSucc2 [1, 2] = [2, 3] := rfl

-- A full `#synthesize_pred`-style suggestion: the spec theorems' `Eq.refl`
-- proofs still typecheck against the match-converted definition.
def pred2 : Nat → Nat := fun a ↦
  match a with
  | Nat.zero => a
  | Nat.succ n => n

theorem pred2_spec_1 : pred2 0 = 0 := Eq.refl 0

theorem pred2_spec_2 : ∀ n : Nat, pred2 (n + 1) = n := fun n ↦ Eq.refl n

/-! ## End to end: a real `#synthesize` search runs through the converter.
The found term (and hence the exact suggestion text) varies from run to run,
so the message is not pinned; elaborating the command is the test. A typical
suggestion is
```
def add3 : Nat → Nat → Nat
  | Nat.zero, a_1 => a_1
  | Nat.succ n, a_1 => (add3 n a_1).succ
``` -/

#synthesize add3 : Nat → Nat → Nat
  | add3 0 0 = 0
  | add3 0 1 = 1
  | add3 1 1 = 2

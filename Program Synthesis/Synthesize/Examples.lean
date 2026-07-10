import Synthesize
import Canonical
/-! Smoke tests for the `synthesize` tactic. Elaborating this file runs real
searches; a "No function found" outcome is an elaboration error and fails the
build. Like `canonical`, the tactic admits the goal — the definitions below
elaborate with `sorryAx` bodies — and offers each function found as a
`Try this: exact …` suggestion; the pasted outputs at the bottom of the file
are the regression tests for the suggestion text itself. -/

/-! ## Input–output examples (the former `#synthesize`) -/

-- Addition, from three input–output examples (the problem built by hand in
-- the Rust repo's `lean/Test.lean`).
def f : Nat → Nat → Nat := by
  synthesize
  | f 0 0 = 0
  | f 0 1 = 1
  | f 1 1 = 2

-- The predecessor function, requiring case analysis.
def pred : Nat → Nat := by
  synthesize
  | pred 0 = 0
  | pred 1 = 0
  | pred 2 = 1
  | pred 3 = 2

-- With a premise list: the search may use `Nat.add`, and finds `fun a ↦ a + a`.
def double : Nat → Nat := by
  synthesize 10 [Nat.add]
  | double 0 = 0
  | double 1 = 2
  | double 2 = 4

/-! ## Quantified clauses (the former `#synthesize_pred`) -/

-- First projection, from a single universally quantified clause over two
-- variables. The instantiated equations are `proj 0 0 = 0`, `proj 0 1 = 0`,
-- `proj 1 0 = 1`; the search finds `fun a b ↦ a`.
def proj : Nat → Nat → Nat := by
  synthesize
  | ∀ n m : Nat, proj n m = n

-- A clause without binders is an ordinary input–output example; the
-- quantified clause instantiates to `pred' 1 = 0`, `pred' 2 = 1`,
-- `pred' 3 = 2` (the ground argument `n + 1` is evaluated).
def pred' : Nat → Nat := by
  synthesize
  | pred' 0 = 0
  | ∀ n : Nat, pred' (n + 1) = n

-- With a premise list: the instantiated equations are `double' 0 = 0`,
-- `double' 1 = 2`, `double' 2 = 4`; the search may use `Nat.add`.
def double' : Nat → Nat := by
  synthesize 10 [Nat.add]
  | ∀ n : Nat, double' n = n + n

-- Both sides of a clause may mention the function. From four instantiations
-- of commutativity only `add 0 1 = add 1 0` survives — `add 0 0 = add 0 0`
-- and `add 1 1 = add 1 1` are trivial and the mirror image of the survivor
-- is a duplicate. A warning for a clause the proof search cannot verify
-- (e.g. commutativity of a non-commutative candidate) is expected here.
def add : Nat → Nat → Nat := by
  synthesize 60
  | ∀ n m : Nat, add n m = add m n
  | ∀ n : Nat, add n 0 = n
  | add 1 1 = 2

/-! ## Pasted outputs

Applying a suggestion replaces `synthesize …` with `exact …` inside the `by`
block, and the proved spec theorems are logged for pasting after the
definition. The declarations below are outputs of earlier runs and must keep
elaborating. -/

-- A `let rec`/`match` rendering elaborates in `exact` position.
def add2 : Nat → Nat → Nat := by
  exact fun a b =>
    let rec go : Nat → Nat := fun x =>
      match x with
      | Nat.zero => a
      | Nat.succ n => (go n).succ
    go b

example : add2 3 4 = 7 := rfl
example : add2 3 0 = 3 := rfl

-- A raw-recursor suggestion together with its logged `theorem` proofs.
def comm2 : Nat → Nat → Nat := by
  exact fun a a_1 ↦ Nat.rec (motive := fun t ↦ Nat) a (fun n n_ih ↦ n_ih.succ) a_1
theorem comm2_spec_1 : ∀ n m : Nat, comm2 n m = comm2 m n := fun n m ↦
  Nat.rec (motive := fun t ↦
    Nat.rec (motive := fun t ↦ Nat) t (fun n n_ih ↦ n_ih.succ) m =
      Nat.rec (motive := fun t ↦ Nat) m (fun n n_ih ↦ n_ih.succ) t)
    (Nat.rec (motive := fun t ↦ Nat.rec (motive := fun t ↦ Nat) Nat.zero (fun n n_ih ↦ n_ih.succ) t = t)
      (Eq.refl Nat.zero) (fun n n_ih ↦ by simp only [Nat.succ.injEq] <;> exact n_ih) m)
    (fun n n_ih ↦
      Eq.rec (motive := fun a t ↦ Nat.rec (motive := fun t ↦ Nat) n.succ (fun n n_ih ↦ n_ih.succ) m = a)
        (Nat.rec (motive := fun t ↦
          Nat.rec (motive := fun t ↦ Nat) n.succ (fun n n_ih ↦ n_ih.succ) t =
            (Nat.rec (motive := fun t ↦ Nat) n (fun n n_ih ↦ n_ih.succ) t).succ)
          (by simp only [Nat.succ.injEq] <;> exact Eq.refl n)
          (fun n_1 n_ih ↦ by simp only [Nat.succ.injEq] <;> exact n_ih) m)
        (by simp only [Nat.succ.injEq] <;> exact n_ih))
    n
theorem comm2_spec_2 : ∀ n : Nat, comm2 n 0 = n := fun n ↦ Eq.refl n
theorem comm2_spec_3 : comm2 1 1 = 2 :=
  Eq.refl 2

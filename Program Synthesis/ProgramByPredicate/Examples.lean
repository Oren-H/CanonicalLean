import ProgramByPredicate
import Canonical
/-! Smoke tests for `#synthesize_pred`. Elaborating this file runs real searches;
a "No function found" outcome is an elaboration error and fails the build. -/

-- First projection, from a single universally quantified predicate over two
-- variables. The instantiated equations are `proj 0 0 = 0`, `proj 0 1 = 0`,
-- `proj 1 0 = 1`; the search finds `fun a b ↦ a`.
#synthesize_pred proj : Nat → Nat → Nat
  | ∀ n m : Nat, proj n m = n

-- The predecessor function. A clause without binders is an ordinary
-- input–output example; the predicate instantiates to `pred 1 = 0`,
-- `pred 2 = 1`, `pred 3 = 2` (the ground argument `n + 1` is evaluated).
#synthesize_pred pred : Nat → Nat
  | pred 0 = 0
  | ∀ n : Nat, pred (n + 1) = n

-- With a premise list: the instantiated equations are `double 0 = 0`,
-- `double 1 = 2`, `double 2 = 4`; the search may use `Nat.add`, and finds
-- `fun a ↦ a + a`.
#synthesize_pred 10 [Nat.add] double : Nat → Nat
  | ∀ n : Nat, double n = n + n

-- Both sides of a predicate may mention the function. From four
-- instantiations of commutativity only `comm 0 1 = comm 1 0` survives —
-- `comm 0 0 = comm 0 0` and `comm 1 1 = comm 1 1` are trivial and the mirror
-- image of the survivor is a duplicate.
#synthesize_pred 60 comm : Nat → Nat → Nat
  | ∀ n m : Nat, comm n m = comm m n
  | ∀ n : Nat, comm n 0 = n
  | comm 1 1 = 2

def comm2 : Nat → Nat → Nat := fun a a_1 ↦ Nat.rec (motive := fun t ↦ Nat) a (fun n n_ih ↦ n_ih.succ) a_1
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

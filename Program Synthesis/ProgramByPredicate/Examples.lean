import ProgramByPredicate

/-! Smoke tests for `#synthesize_pred`. Elaborating this file runs real searches;
a "No function found" outcome is an elaboration error and fails the build.
After synthesis, each command attempts to prove its predicates about the found
function; proved predicates appear as `theorem`s in the suggestion, unproved
ones produce a warning (the `comm` test below is expected to warn). -/

-- First projection, from a single universally quantified predicate over two
-- variables. The instantiated equations are `proj 0 0 = 0`, `proj 0 1 = 0`,
-- `proj 1 0 = 1`; the search finds `fun a b ↦ a`, and the predicate is proved
-- as `proj_spec` (by `rfl`, after β-reduction).
#synthesize_pred proj : Nat → Nat → Nat
  | ∀ n m : Nat, proj n m = n

-- The predecessor function. A clause without binders is an ordinary
-- input–output example; the predicate instantiates to `pred 1 = 0`,
-- `pred 2 = 1`, `pred 3 = 2` (the ground argument `n + 1` is evaluated).
-- Both clauses are proved (`pred_spec_1`, `pred_spec_2`) — the recursor in
-- the found function ι-reduces on `n + 1`.
#synthesize_pred pred : Nat → Nat
  | pred 0 = 0
  | ∀ n : Nat, pred (n + 1) = n

-- With a premise list: the instantiated equations are `double 0 = 0`,
-- `double 1 = 2`, `double 2 = 4`; the search may use `Nat.add`, and finds
-- `fun a ↦ a + a`, with the predicate proved as `double_spec`.
#synthesize_pred 10 [Nat.add] double : Nat → Nat
  | ∀ n : Nat, double n = n + n

-- Both sides of a predicate may mention the function. From four
-- instantiations of commutativity only `comm 0 1 = comm 1 0` survives —
-- `comm 0 0 = comm 0 0` and `comm 1 1 = comm 1 1` are trivial and the mirror
-- image of the survivor is a duplicate. The found function satisfies the
-- sampled equations but is *not* commutative, so the verification step
-- cannot prove the first predicate and warns (expected!); the second is
-- proved by induction as `comm_spec_2`.
#synthesize_pred (examples := 4) comm : Nat → Nat → Nat
  | ∀ n m : Nat, comm n m = comm m n
  | ∀ n : Nat, comm n 0 = n

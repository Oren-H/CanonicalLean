import Synthesize
import Canonical
/-! Smoke tests for the `synthesize` tactic. Elaborating this file runs real
searches; a "No function found" outcome is an elaboration error and fails the
build. Like `canonical`, the tactic admits the goal — the definitions below
elaborate with `sorryAx` bodies — and offers each function found as a
`Try this: exact …` suggestion, recursors rendered as `match`/`let rec`; the
pasted outputs at the bottom of the file are the regression tests for the
suggestion text itself. -/

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
-- is a duplicate. The quantified clauses are only sampled: the synthesized
-- function satisfies the instantiated equations, not necessarily the
-- predicates themselves.
def add : Nat → Nat → Nat := by
  synthesize 60
  | ∀ n m : Nat, add n m = add m n
  | ∀ n : Nat, add n 0 = n
  | add 1 1 = 2

/-! ## Pasted outputs

Applying a suggestion replaces `synthesize …` with `exact …` inside the `by`
block. The declarations below are outputs of earlier runs and must keep
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

-- An inline-`match` rendering (non-recursive elimination).
def pred2 : Nat → Nat := by
  exact fun a =>
    match a with
    | Nat.zero => a
    | Nat.succ n => n

example : pred2 0 = 0 := rfl
example : pred2 3 = 2 := rfl

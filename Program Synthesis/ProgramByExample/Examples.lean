import ProgramByExample

/-! Smoke tests for `#synthesize`. Elaborating this file runs real searches;
a "No function found" outcome is an elaboration error and fails the build. -/

-- Addition, from three input–output examples (the problem built by hand in the
-- Rust repo's `lean/Test.lean`).
#synthesize f : Nat → Nat → Nat
  | f 0 0 = 0
  | f 0 1 = 1
  | f 1 1 = 2

-- The predecessor function, requiring case analysis.
#synthesize pred : Nat → Nat
  | pred 0 = 0
  | pred 1 = 0
  | pred 2 = 1
  | pred 3 = 2

-- With a premise list: the search may use `Nat.add`, and finds `fun a ↦ a + a`.
#synthesize 10 [Nat.add] double : Nat → Nat
  | double 0 = 0
  | double 1 = 2
  | double 2 = 4

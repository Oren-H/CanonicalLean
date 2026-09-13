import ProgramByPredicateMinimal
import Canonical
/-! Smoke tests for the minimal `synthesize`. Elaborating this file runs real searches; a
"No proof found" outcome fails the build. Each definition is admitted (like `canonical`) and the
function found is offered as a `Try this: exact …` suggestion, with Skolem witnesses reported. -/

/-! ## Input–output examples -/

def f : Nat → Nat → Nat := by
  synthesize
  | f 0 0 = 0
  | f 0 1 = 1
  | f 1 0 = 1
  | f 2 2 = 4
  | f 2 3 = 5
  | f 3 9 = 12
  | f 9 3 = 12
  | f 10 10 = 20

def pred : Nat → Nat := by
  synthesize
  | pred 0 = 0
  | pred 1 = 0
  | pred 2 = 1
  | pred 3 = 2

def double : Nat → Nat := by
  synthesize 10 [Nat.add]
  | double 0 = 0
  | double 1 = 2
  | double 2 = 4

/-! ## Universally quantified clauses (sampled) -/

def proj : Nat → Nat → Nat := by
  synthesize
  | ∀ n m : Nat, proj n m = n

def pred' : Nat → Nat := by
  synthesize
  | pred' 0 = 0
  | ∀ n : Nat, pred' (n + 1) = n

def double' : Nat → Nat := by
  synthesize 10 [Nat.add]
  | ∀ n : Nat, double' n = n + n

def add : Nat → Nat → Nat := by
  synthesize 60
  | ∀ n m : Nat, add n m = add m n
  | ∀ n : Nat, add n 0 = n
  | add 1 1 = 2

def mul : Nat → Nat → Nat := by
  synthesize
  | mul 0 0 = 0
  | mul 0 1 = 0
  | mul 2 2 = 4
  | mul 2 1 = 2

/-! ## Existential clauses: witnesses are Skolem functions of the enclosing universals -/

def zero' : Nat → Nat → Nat := by
  synthesize
  | ∀ x : Nat, ∃ y : Nat, zero' x y = 0

def inv : Nat → Nat := by
  synthesize
  | ∀ x : Nat, ∃ y : Nat, inv y = x

def one' : Nat → Nat := by
  synthesize
  | ∃ y : Nat, one' y = 1
  | one' 0 = 0

/-! ## Quantifiers nested in any order, and conjunctions -/

-- `∃` before `∀`: a Skolem constant `c`.
def fst' : Nat → Nat → Nat := by
  synthesize
  | ∃ c : Nat, ∀ x : Nat, fst' x c = x

-- `∀∃∀∃` with `∧`: `y` depends on `x`, `w` on `x` and `z`.
def id' : Nat → Nat := by
  synthesize
  | ∀ x : Nat, ∃ y : Nat, ∀ z : Nat, ∃ w : Nat, id' y = x ∧ id' z = w

-- A conjunction under a universal is split into two sampled equations.
def add' : Nat → Nat → Nat := by
  synthesize 60
  | ∀ n : Nat, add' n 0 = n ∧ add' 0 n = n
  | add' 1 1 = 2

-- A premise is a dependent binder: inputs are sampled together with a proof of it, so only
-- values Canonical can prove `≠ 0` instantiate the equation.
def pred'' : Nat → Nat := by
  synthesize
  | ∀ x : Nat, x ≠ 0 → pred'' x + 1 = x

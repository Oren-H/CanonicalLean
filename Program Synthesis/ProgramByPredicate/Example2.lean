import Synthesize
import Canonical

inductive Pos where
  | one  : Pos          -- the leading 1 bit — value 1
  | bit0 : Pos → Pos    -- p ↦ 2p
  | bit1 : Pos → Pos    -- p ↦ 2p + 1

inductive Bin where
  | zero : Bin          -- value 0
  | pos  : Pos → Bin     -- positive value

/-- Bits of a positive binary number, MSB first (e.g. `bit1 (bit0 one)` → `"101"`). -/
def Pos.toBits : Pos → String
  | .one => "1"
  | .bit0 p => p.toBits ++ "0"
  | .bit1 p => p.toBits ++ "1"

instance : Repr Pos where
  reprPrec p _ := s!"{p.toBits}"

instance : Repr Bin where
  reprPrec
    | .zero, _ => "0"
    | .pos p, _ => repr p

/-- Interpret the decimal digits of `n` as a binary bit string.
    e.g. `110` ↦ bits `110` (= 6), `101` ↦ bits `101` (= 5). -/
def Nat.toPosBits (n : Nat) : Pos :=
  if n ≤ 1 then .one
  else
    let d := n % 10
    let rest := n / 10
    if d = 0 then .bit0 rest.toPosBits else .bit1 rest.toPosBits

def Nat.toBinBits : Nat → Bin
  | 0 => .zero
  | n => .pos n.toPosBits

instance {n : Nat} : OfNat Bin n where
  ofNat := n.toBinBits

instance {n : Nat} : OfNat Pos n.succ where
  ofNat := n.succ.toPosBits

def add : Bin → Bin → Bin := by
  synthesize 30
  | ∀ a b : Bin, add a b = add b a
  | ∀ a : Bin, add a Bin.zero = a
  | add (Bin.pos (Pos.one)) (Bin.pos (Pos.bit0 (Pos.one))) = Bin.pos (Pos.bit1 Pos.one)

def add2 : Bin → Bin → Bin := fun a a_1 ↦
  match a with
  | Bin.zero => a_1
  | Bin.pos a_2 =>
    Bin.pos
      (match a_1 with
      | Bin.zero => a_2
      | Bin.pos a_3 => a_2.bit1)

#eval add2 110 101






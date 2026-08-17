import Canonical
import Lean

example : Nat := by canonical

example : Nat := by canonical -recs

example {α : Sort u} : False → α := by canonical

example {α : Sort u} : False → α := by canonical -recs [False.rec]

/--
error: No proof found. Supply constant symbols with `canonical [name, ...]`
-/
#guard_msgs in
example {α : Sort u} : False → α := by canonical -recs

import BusyBeaver.ZFC.ArithmeticControlBisim

set_option autoImplicit false

/-!
# Packed external tables

Large external tables (catalogue rows, bisimulation certificates) are stored as
one natural-number literal with fixed-width bit slots. The kernel evaluates
slot extraction with its built-in arbitrary-precision division and remainder,
so a lookup is a few big-number operations on literal data, and no structure
literal of thousands of entries has to be elaborated.

A row occupies 36 bits (opcode 3, register 4, two successors 13 bits each); a
certificate entry 96 bits (two controls 13 bits each, two offset vectors of
nine 2-bit fields, two successor indices 12 bits each). The table as a list is
`List.ofFn` of the slots, so its relation to the lookup function is definitional
(`rowsOf_some`, `certOf_some`); nothing is evaluated by the kernel for it.
-/

namespace SetTheory.BusyBeaver.ZFC.PackedTables

open ArithmeticControlBisim

/-- Slot `i` of width `w`. -/
def slot (n i w : Nat) : Nat := n / 2 ^ (w * i) % 2 ^ w

def decodeRow (x : Nat) : Row :=
  ⟨x % 8, ⟨x / 8 % 16 % 9, Nat.mod_lt _ (by decide)⟩, x / 128 % 8192, x / 1048576 % 8192⟩

/-- The row list of a packed table with `count` rows. -/
def table (n count : Nat) : List Row := List.ofFn fun i : Fin count => decodeRow (slot n i 36)

/-- Row lookup by control number (control `c` is row `c - 1`). -/
def rowsOf (n count c : Nat) : Option Row :=
  if c = 0 ∨ count < c then none else some (decodeRow (slot n (c - 1) 36))

theorem rowsOf_some (n count c : Nat) (row : Row) (h : rowsOf n count c = some row) :
    c ≠ 0 ∧ getElem? (table n count) (c - 1) = some row := by
  unfold rowsOf at h
  split_ifs at h with hc
  refine ⟨fun h0 => hc (.inl h0), ?_⟩
  have hlt : c - 1 < count := by omega
  simp only [table, List.getElem?_ofFn, hlt]
  simpa using h

theorem table_length (n count : Nat) : (table n count).length = count := by simp [table]

def decodeVec (x : Nat) : Vec :=
  [x % 4, x / 4 % 4, x / 16 % 4, x / 64 % 4, x / 256 % 4, x / 1024 % 4, x / 4096 % 4,
    x / 16384 % 4, x / 65536 % 4]

def decodeEntry (x : Nat) : Entry :=
  ⟨x % 8192, x / 8192 % 8192, decodeVec (x / 2 ^ 26 % 2 ^ 18), decodeVec (x / 2 ^ 44 % 2 ^ 18),
    x / 2 ^ 62 % 4096, x / 2 ^ 74 % 4096⟩

/-- Certificate lookup by entry index. -/
def certOf (n count i : Nat) : Option Entry :=
  if i < count then some (decodeEntry (slot n i 96)) else none

end SetTheory.BusyBeaver.ZFC.PackedTables

import DiophantineConsistency.WangTiles942TableData
import DiophantineConsistency.ArithmeticMachineGraph215

/-! The literal 942-tile Wang table inside every model of IΣ1.

The four colour functions are fixed numeral lookups (the
`ArithmeticMachineGraph215` pattern) over lists derived from the actual
`WangTiles942.tile`, not a second copy of the table. Every local table fact
used by the soundness argument is a single-tile property of the standard
table, checked once in ℕ by `decide +kernel` and transported to an arbitrary
model: an element below 942 is a numeral, and the lookups commute with the
numeral cast. The transition rows are bound to the internal machine lookup
`ArithmeticMachineGraph215.actionLookup` through `literal_lookup_actual` and
the authenticated action cache. No tiling or halting statement is made here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace DiophantineConsistency.ArithmeticWangTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open WangTiles942
open ArithmeticMachinePerm252 ArithmeticMachineGraphPerm252

/-! ## Standard data -/

/-- The actual tile with index `m`, and the all-zero tuple outside the table. -/
def tileN (m : ℕ) : Tile := if h : m < 942 then tile ⟨m, h⟩ else ⟨0, 0, 0, 0⟩

/-- Head colour of a state code: code0 is halt (machine state215). -/
def hcN (st b : ℕ) : ℕ := if st = 0 then 432 + b else 2 * st + b

/-- The state code carried by a receiver rail colour (rails are ranks in the
sorted direction target list, offset6 rightwards and205 leftwards). -/
def rcvCode (d : Bool) (c : ℕ) : ℕ :=
  if (targetList d).getD (c - (if d then 6 else 205)) 215 < 215 then
    (targetList d).getD (c - (if d then 6 else 205)) 215 + 1 else 0

/-- The positive action code of transition input `j` from the cached actions,
in the `actionNumber` format of the internal machine lookup. -/
def actCode (j : ℕ) : ℕ :=
  1 + 4 * (if (actionNat j).2.2 < 215 then (actionNat j).2.2 + 1 else 0) +
    2 * (actionNat j).2.1.toNat + (actionNat j).1.toNat

theorem actCode_spec (j : ℕ) : ∃ c d w : ℕ, c ≤ 215 ∧ d ≤ 1 ∧ w ≤ 1 ∧
    actCode j = 1 + 4 * c + 2 * d + w := by
  refine ⟨_, _, _, ?_, Bool.toNat_le _, Bool.toNat_le _, rfl⟩
  split <;> omega

/-- Local geometry of every tile: seams, initialization tiles, plain inputs,
finishes and resets. -/
def GoodA (t : Tile) : Prop :=
  (t.north = 437 ↔ t.south = 437) ∧
  (t.north = 437 → t.west ≤ 4 ∧ t.east ≤ 2) ∧
  (t.north = 434 → t.west = 2 ∧ t.east = 2 ∧ t.south = 0) ∧
  (t.east = 2 → t.north = 434 ∨ t.north = 437) ∧
  (t.west = 3 → t.north = 436 ∧ t.east = 4 ∧ t.south = 4) ∧
  (t.north = 436 → t.east = 4) ∧
  (t.west = 4 → (t.north = 436 ∧ t.south = 0) ∨ t.north = 437) ∧
  (t.north ≤ 1 → (t.west = 0 ∨ (6 ≤ t.west ∧ t.west < 205)) ∧
     (t.east = 0 ∨ (205 ≤ t.east ∧ t.east < 250))) ∧
  (t.north ≤ 1 → t.west = 0 → t.east = 0 → t.south = t.north ∨ t.south = 438) ∧
  (t.north = 438 → t.west = 1 ∧ t.east = 1) ∧
  (t.west = 1 → t.north = 438 ∨ t.north = 437) ∧
  (t.east = 1 → t.north = 438 ∨ t.north = 437)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance : DecidablePred GoodA := fun t => by unfold GoodA; infer_instance

/-- Receivers: a plain input with an incoming rail takes the rail's head. -/
def GoodB (t : Tile) : Prop :=
  (t.north ≤ 1 → t.west ≠ 0 → t.south = hcN (rcvCode true t.west) t.north) ∧
  (t.north ≤ 1 → t.east ≠ 0 → t.south = hcN (rcvCode false t.east) t.north)

instance : DecidablePred GoodB := fun t => by unfold GoodB; infer_instance

/-- Transitions: north `j+2` carries the cached action of input `j`. -/
def GoodC (t : Tile) : Prop :=
  2 ≤ t.north → t.north < 432 →
    (actCode (t.north - 2) - 1) % 2 = t.south ∧
    ((actCode (t.north - 2) - 1) / 2 % 2 = 1 →
      t.west = 0 ∧ 6 ≤ t.east ∧ rcvCode true t.east = (actCode (t.north - 2) - 1) / 4) ∧
    ((actCode (t.north - 2) - 1) / 2 % 2 = 0 →
      t.east = 0 ∧ 205 ≤ t.west ∧ rcvCode false t.west = (actCode (t.north - 2) - 1) / 4)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance : DecidablePred GoodC := fun t => by unfold GoodC; infer_instance

end DiophantineConsistency.ArithmeticWangTable

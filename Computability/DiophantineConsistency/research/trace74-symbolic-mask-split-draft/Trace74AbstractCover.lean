import Mathlib.Data.Nat.Basic
set_option autoImplicit false
namespace Trace74AbstractCover
/-- Strict defect domination supplies the missing successor in the cover. -/
theorem of_identity (beta low defect high power : ℕ)
    (hb : beta+1=power) (hl : low+defect+1=power) (hd : defect<high) :
    beta+1≤low+high := by
  calc
    beta+1=power := hb
    _=low+defect+1 := hl.symm
    _=low+(defect+1) := by rw [Nat.add_assoc]
    _≤low+high := Nat.add_le_add_left (Nat.succ_le_of_lt hd) low
#print axioms Trace74AbstractCover.of_identity
end Trace74AbstractCover

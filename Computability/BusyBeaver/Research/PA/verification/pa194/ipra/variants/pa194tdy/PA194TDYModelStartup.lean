import PA194TDYRows
import PA194TDYStartupComplete

set_option autoImplicit false

namespace PA194TDYModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact TDY blank run reaches the shared source seed at clock 57,594. -/
theorem modeledStartup :
    ConPA.Machine.run (V := V) PA194TDYData.table (57594 : V) =
      ⟪(24 : V),(1 : V),(152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := PA194IndexedNumerals.indexedRun_correct (V := V) PA194TDYData.rows
    PA194TDYData.rowCount PA194TDYRows.directions 57594
  rw [← PA194TDYNumerical.blank 57594, PA194TDYStartup.startup, ConPA.Machine.packedCode_cast] at h
  simpa only [Nat.cast_ofNat, Nat.cast_one] using h

#print axioms modeledStartup
end PA194TDYModelStartup

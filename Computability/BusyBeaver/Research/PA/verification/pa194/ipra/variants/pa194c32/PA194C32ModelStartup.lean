import PA194C32Rows
import PA194C32StartupComplete

set_option autoImplicit false

namespace PA194C32ModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact C32 blank run reaches the shared source seed at clock 56,250. -/
theorem modeledStartup :
    ConPA.Machine.run (V := V) PA194C32Data.table (56250 : V) =
      ⟪(24 : V),(1 : V),(152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := PA194IndexedNumerals.indexedRun_correct (V := V) PA194C32Data.rows
    PA194C32Data.rowCount PA194C32Rows.directions 56250
  rw [← PA194C32Numerical.blank 56250, PA194C32Startup.startup, ConPA.Machine.packedCode_cast] at h
  simpa only [Nat.cast_ofNat, Nat.cast_one] using h

#print axioms modeledStartup
end PA194C32ModelStartup

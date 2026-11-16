import PA194P5Rows
import PA194P5StartupComplete

set_option autoImplicit false

namespace PA194P5ModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The exact P5 blank run reaches the shared source seed at clock 56,158. -/
theorem modeledStartup :
    ConPA.Machine.run (V := V) PA194P5Data.table (56158 : V) =
      ⟪(24 : V),(1 : V),(152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := PA194IndexedNumerals.indexedRun_correct (V := V) PA194P5Data.rows
    PA194P5Data.rowCount PA194P5Rows.directions 56158
  rw [← PA194P5Numerical.blank 56158, PA194P5Startup.startup, ConPA.Machine.packedCode_cast] at h
  simpa only [Nat.cast_ofNat, Nat.cast_one] using h

#print axioms modeledStartup
end PA194P5ModelStartup

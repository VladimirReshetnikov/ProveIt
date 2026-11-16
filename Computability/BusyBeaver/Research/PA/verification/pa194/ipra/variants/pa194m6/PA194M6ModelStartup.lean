import PA194M6Rows
import PA194M6Startup

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PA194M6ModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals PA194M6Data

/-- The exact M6 blank run reaches the primary packed seed in every IΣ₁ model. -/
theorem modeledStartup {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ConPA.Machine.run (V := V) table (58320 : V) =
      ⟪(24 : V), (1 : V), (152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := indexedRun_correct (V := V) rows PA194M6Rows.rowCount PA194M6Rows.directions 58320
  rw [← PA194M6Numerical.blank 58320, PA194M6Startup.startup, ConPA.Machine.packedCode_cast] at h
  simpa [table] using h

#print axioms modeledStartup
end PA194M6ModelStartup

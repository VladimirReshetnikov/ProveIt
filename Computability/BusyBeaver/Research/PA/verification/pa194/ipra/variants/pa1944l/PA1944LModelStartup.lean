import PA1944LPhysical
import PA1944LStartupComplete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PA1944LModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals PA1944LData

theorem directions : BinaryDirections rows := by
  unfold BinaryDirections
  decide +kernel

/-- The exact LC blank run reaches the primary packed seed in every IΣ₁ model. -/
theorem modeledStartup {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ConPA.Machine.run (V := V) table (58320 : V) =
      ⟪(24 : V), (1 : V), (152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := indexedRun_correct (V := V) rows PA1944LPhysical.rowCount directions 58320
  rw [← PA1944LNumerical.blank 58320, PA1944LStartup.startup, ConPA.Machine.packedCode_cast] at h
  simpa [table] using h

#print axioms modeledStartup
end PA1944LModelStartup

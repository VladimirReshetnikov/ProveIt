import PA194LCPhysical
import PA194LCStartupComplete

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace PA194LCModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals PA194LCData

theorem directions : BinaryDirections rows := by
  unfold BinaryDirections
  decide +kernel

/-- The exact LC blank run reaches the primary packed seed in every IΣ₁ model. -/
theorem modeledStartup {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ConPA.Machine.run (V := V) table (58154 : V) =
      ⟪(24 : V), (1 : V), (152919395647067130113387679226998336721518593 : V)⟫ := by
  have h := indexedRun_correct (V := V) rows PA194LCPhysical.rowCount directions 58154
  rw [← PA194LCNumerical.blank 58154, PA194LCStartup.startup, ConPA.Machine.packedCode_cast] at h
  simpa [table] using h

#print axioms modeledStartup
end PA194LCModelStartup

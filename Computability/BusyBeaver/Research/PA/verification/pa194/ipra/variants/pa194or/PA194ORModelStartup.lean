import PA194ORPhysical
import PA194ORStartupComplete
import PA194StartupData

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSectionVars false

namespace PA194ORModelStartup
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194IndexedNumerals
open PA194ORData

theorem directions : BinaryDirections rows := by
  unfold BinaryDirections
  decide +kernel

theorem seed_bits :
    PA194Bounded.bits PA194StartupData.seedFrame.r = 152919395647067130113387679226998336721518593 := by
  decide +kernel

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The literal OR blank orbit reaches the same full tape as the primary
    source initial frame in every model of IΣ₁. -/
theorem modeledStartup :
    ConPA.Machine.run (V := V) table (58170 : V) =
      ⟪(24 : V),(1 : V),(PA194Bounded.bits PA194StartupData.seedFrame.r : V)⟫ := by
  have h := indexedRun_correct (V := V) rows PA194ORPhysical.rowCount directions 58170
  rw [← PA194ORNumerical.blank 58170, PA194ORStartup.startup, ConPA.Machine.packedCode_cast] at h
  rw [seed_bits]
  simpa [table] using h

#print axioms modeledStartup
end models
end PA194ORModelStartup

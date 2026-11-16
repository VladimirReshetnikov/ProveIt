import PA194LCRoot
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 8000000
namespace PA194LCPhysicalFacts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime
section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem encodeControl (label : Nat → Nat) (gap : V) (box : BoxSt → V) (s : SConf) :
    π₁ (encode label gap box s) = (label s.1 : V) := by
  rcases s with ⟨q,onLeft,l,r⟩
  cases onLeft <;> simp [encode,scanFrame]

theorem root_control (gap : V) (box : BoxSt → V) (i extra : Nat) (effect : Eff) :
    π₁ (PA194LCPhysical.root gap box i extra effect) = (24 : V) := by
  rw [PA194LCPhysical.root,PA194SourceContracts.root,encodeControl]
  change (PA194LCData.denseControl 84 : V) = (24 : V)
  rw [PA194LCPhysical.rootControl]
  rfl

theorem halt_absorbs (y : V) (h : π₁ y = (194 : V)) : step PA194LCData.table y = y := by
  have he : y = PA194BModelSteps.config 194 (π₁ (π₂ y)) (π₂ (π₂ y)) := by
    unfold PA194BModelSteps.config
    change π₁ y = ((194 : Nat) : V) at h
    rw [← h,pair_unpair,pair_unpair]
  conv_lhs => rw [he]
  rw [PA194LCData.table, PA194BModelSteps.halted PA194LCData.rows PA194LCPhysical.rowCount, ← he]

#print axioms root_control
#print axioms halt_absorbs
end models
end PA194LCPhysicalFacts

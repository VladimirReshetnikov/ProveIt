import DiophantineConsistency.AdaptiveZ43Model
import DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 3000000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ43FixedPort
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveScaledNorms2011

theorem beta_ge_two : 2 ≤ CurrentMasks2011.beta := by
  have hr : 3 ≤ CurrentMasks2011.radix := by decide
  have hp : CurrentMasks2011.radix ≤ CurrentMasks2011.radix ^ 2011 :=
    le_self_pow₀ (by omega : 1 ≤ CurrentMasks2011.radix) (by decide : 2011 ≠ 0)
  unfold CurrentMasks2011.beta
  omega

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem fixed_port_bound : (2:V) ≤ (currentPorts 0:V) := by
  have h : (2:V) ≤ (CurrentMasks2011.beta:V) := by exact_mod_cast beta_ge_two
  simpa only [currentPorts,Matrix.cons_val_zero] using h
#print axioms beta_ge_two
#print axioms fixed_port_bound
end DiophantineConsistency.AdaptiveZ43FixedPort

import DiophantineConsistency.ForeignOriginOverlap
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace ForeignPhaseMask
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticMaskConstants CompactHighPopulation CompactSymbolicPorts
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shifted_mask_zero : dig 67 (highNat:V) 5488=0 := by
  have h := dig_ofDigits (V:=V) 67 highDigits digit_lt 5488
  have hd : highDigits.getD 5488 0=0 := by decide +kernel
  rw [hd] at h
  exact h
#print axioms ForeignPhaseMask.shifted_mask_zero
end ForeignPhaseMask

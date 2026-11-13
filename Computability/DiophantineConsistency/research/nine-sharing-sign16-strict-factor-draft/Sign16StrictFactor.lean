import DiophantineConsistency.Sign16MoreSharedValues

/-! SOURCE-ONLY cancellation ingredient for the strict maintained norm. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16StrictFactor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem strict_of_factors (D f i c S : V) (hD : 0 < D)
    (hS : S = i * D * c * c) (hrow : D * (f*f) = S*S + D) :
    f*f = 1 + D * (i*c*c) * (i*c*c) := by
  apply mul_left_cancel₀ (ne_of_gt hD)
  calc
    _ = S*S + D := hrow
    _ = _ := by rw [hS]; ring
end DiophantineConsistency.Sign16StrictFactor
#print axioms DiophantineConsistency.Sign16StrictFactor.strict_of_factors

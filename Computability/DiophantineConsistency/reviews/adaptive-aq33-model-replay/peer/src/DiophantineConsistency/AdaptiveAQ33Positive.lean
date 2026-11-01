import DiophantineConsistency.AdaptiveAQ33Facts
import DiophantineConsistency.AdaptiveZ46Orientation
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ33Positive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveAQ33Context AdaptiveAQ33Facts AdaptiveAQ33Bound ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_w_positive (p : Fin 4 → ℕ) (v : Fin 34 → V)
    (hv : ∀ i, 0 < v i) (hz : InternalZero (AdaptiveAQ34Literal.literal (fun j => (p j:ℤ))) v) :
    v 19 < v 18 := by
  obtain ⟨hnorm,hroot⟩ := facts p v hz
  obtain ⟨t,hzt,htnorm⟩ := scaled_quotient (v 13) (v 22)
    (1+v 17*(v 17+(v 9+v 10))) (hv 13) hnorm
  by_contra hn
  have hle : v 18 ≤ v 19 := le_of_not_gt hn
  let u := v 19-v 18
  have hu : v 19 = v 18+u := by rw [add_comm,tsub_add_cancel_of_le hle]
  have hr : v 22 = v 13*(v 17+(v 9+v 10)+v 8) +
      (v 7*(v 0*(p 0:V))+u*(v 13*(v 9+v 10)+((1+v 0*(p 0:V))*v 28))) := by
    apply add_right_cancel (b := (v 13*(v 9+v 10))*v 18+v 18*((1+v 0*(p 0:V))*v 28))
    calc
      _ = v 22+(v 13*(v 9+v 10))*v 18+v 18*((1+v 0*(p 0:V))*v 28) := by ring
      _ = v 13*(v 17+(v 9+v 10)+v 8)+v 7*(v 0*(p 0:V))+(v 13*(v 9+v 10))*v 19+v 19*((1+v 0*(p 0:V))*v 28) := hroot
      _ = _ := by rw [hu]; ring
  have htroot : v 13*t = v 13*(v 17+(v 9+v 10)+v 8) +
      (v 7*(v 0*(p 0:V))+u*(v 13*(v 9+v 10)+((1+v 0*(p 0:V))*v 28))) := by rw [← hzt]; exact hr
  exact impossible_nonpositive (v 13) (v 17) (v 9+v 10) (v 8) t
    (v 7*(v 0*(p 0:V))+u*(v 13*(v 9+v 10)+((1+v 0*(p 0:V))*v 28))) (hv 13) (hv 17) (add_pos (hv 9) (hv 10)) htnorm htroot
#print axioms signed_w_positive
end DiophantineConsistency.AdaptiveAQ33Positive

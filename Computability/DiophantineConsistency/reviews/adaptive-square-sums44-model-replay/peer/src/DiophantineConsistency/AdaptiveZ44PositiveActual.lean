import DiophantineConsistency.AdaptiveZ44Facts
import DiophantineConsistency.AdaptiveZ46Orientation
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveZ44PositiveActual
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveZ46Context AdaptiveZ44Facts AdaptiveZ44Positivity ArithmeticAdaptiveQuotients2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem signed_w_positive (p : Fin 4 → ℕ) (v : Fin 46 → V)
    (hv : ∀ i, 0 < v i) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    v 19 < v 18 := by
  obtain ⟨hnorm,hgamma,hroot⟩ := facts p v hz
  obtain ⟨t,hzt,htnorm⟩ := scaled_quotient (v 14) (v 24)
    (1+v 17*(v 17+(v 9+v 10))) (hv 14) hnorm
  by_contra hn
  have hle : v 18 ≤ v 19 := le_of_not_gt hn
  let u := v 19-v 18
  have hu : v 19 = v 18+u := by rw [add_comm,tsub_add_cancel_of_le hle]
  have hgam : v 45 = v 44 + (v 9+v 10)*u := by
    have eq : (v 44+(v 9+v 10)*u)+(v 9+v 10)*v 18 =
        v 45+(v 9+v 10)*v 18 := calc
      _ = v 44+(v 9+v 10)*(v 18+u) := by ring
      _ = v 45+(v 9+v 10)*v 18 := by rw [← hu]; exact hgamma
    exact (add_right_cancel eq).symm
  have hr : v 24 = v 14*(v 17+(v 9+v 10)+v 8) +
      (v 7*(v 0*(p 0:V))+u*(v 14*(v 9+v 10)+v 20)) := by
    apply add_right_cancel (b := v 14*v 44+v 18*v 20)
    calc
      _ = v 24+v 14*v 44+v 18*v 20 := by ring
      _ = v 14*(v 17+(v 9+v 10)+v 8)+v 7*(v 0*(p 0:V))+v 14*v 45+v 19*v 20 := hroot
      _ = _ := by rw [hgam,hu]; ring
  have htroot : v 14*t = v 14*(v 17+(v 9+v 10)+v 8) +
      (v 7*(v 0*(p 0:V))+u*(v 14*(v 9+v 10)+v 20)) := by rw [← hzt]; exact hr
  exact impossible_nonpositive (v 14) (v 17) (v 9+v 10) (v 8) t
    (v 7*(v 0*(p 0:V))+u*(v 14*(v 9+v 10)+v 20)) (hv 14) (hv 17) (add_pos (hv 9) (hv 10)) htnorm htroot
theorem signed_skew_positive (p : Fin 4 → ℕ) (v : Fin 46 → V)
    (hv : ∀ i, 0 < v i) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    v 45 < v 44 := by
  have hw := signed_w_positive p v hv hz
  have hgamma := (facts p v hz).2.1
  let u := v 18-v 19
  have hu : 0 < u := tsub_pos_iff_lt.mpr hw
  have hwu : v 18 = v 19+u := by rw [add_comm,tsub_add_cancel_of_le (le_of_lt hw)]
  have hgam : v 44 = v 45 + (v 9+v 10)*u := by
    have eq : (v 44+(v 9+v 10)*v 19) =
        (v 45+(v 9+v 10)*u)+(v 9+v 10)*v 19 := calc
      _ = v 45+(v 9+v 10)*v 18 := hgamma
      _ = _ := by rw [hwu]; ring
    exact add_right_cancel eq
  rw [hgam]
  exact lt_add_of_pos_right _ (mul_pos (add_pos (hv 9) (hv 10)) hu)

#print axioms signed_skew_positive
#print axioms signed_w_positive
end DiophantineConsistency.AdaptiveZ44PositiveActual

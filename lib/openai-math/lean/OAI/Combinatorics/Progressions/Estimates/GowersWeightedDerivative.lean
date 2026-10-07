import OAI.Combinatorics.Progressions.Estimates.BooleanCubeProduct

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]

def derivativeSupport (Q : Finset H) (h : H) : Finset H :=
  Q.filter (fun x ↦ x + h ∈ Q)

omit [Fintype H] in
theorem multiplicativeDerivative_restrictTo (Q : Finset H) (f : H → ℂ) (h : H) :
    multiplicativeDerivative (restrictTo Q f) h =
      restrictTo (derivativeSupport Q h) (multiplicativeDerivative f h) := by
  funext x
  by_cases hx : x ∈ Q <;> by_cases hxh : x + h ∈ Q <;>
    simp [multiplicativeDerivative, restrictTo, derivativeSupport, hx, hxh]

theorem groupCubeCount_succ (j : ℕ) (Q : Finset H) :
    groupCubeCount (j + 1) Q = ∑ h, groupCubeCount j (derivativeSupport Q h) := by
  have hd (h : H) : multiplicativeDerivative (restrictTo Q (fun _ ↦ 1)) h =
      restrictTo (derivativeSupport Q h) (fun _ ↦ 1) := by
    rw [multiplicativeDerivative_restrictTo]
    congr 1
    funext x
    simp [multiplicativeDerivative]
  have hm : (gowersMoment (j + 1) (restrictTo Q (fun _ ↦ 1))).re =
      𝔼 h, (gowersMoment j (restrictTo (derivativeSupport Q h) (fun _ ↦ 1))).re := by
    rw [gowersMoment, expect_re]
    simp only [hd]
  simp only [gowersMoment_indicator_re, Fintype.expect_eq_sum_div_card] at hm
  rw [← Finset.sum_div, div_div, ← pow_succ] at hm
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he := (div_left_inj' (pow_ne_zero (j + 2) hH)).mp hm
  exact_mod_cast he

theorem sum_cubeCount_weights (j : ℕ) {Q : Finset H} (hQ : Q.Nonempty) :
    (∑ h, (groupCubeCount j (derivativeSupport Q h) : ℝ) /
      groupCubeCount (j + 1) Q) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, ← groupCubeCount_succ]
  exact div_self (by exact_mod_cast (groupCubeCount_pos (j + 1) hQ).ne')

theorem restrictedGowersNorm_derivative_mul_count (j : ℕ) (Q : Finset H) (f : H → ℂ) :
    (groupCubeCount (j + 2) Q : ℝ) * restrictedGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h, (groupCubeCount (j + 1) (derivativeSupport Q h) : ℝ) *
        restrictedGowersNorm (j + 1) (derivativeSupport Q h)
          (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  have hm : ((groupCubeCount (j + 2) Q : ℝ) / (Fintype.card H : ℝ) ^ (j + 3)) *
        restrictedGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      𝔼 h, ((groupCubeCount (j + 1) (derivativeSupport Q h) : ℝ) /
        (Fintype.card H : ℝ) ^ (j + 2)) *
        restrictedGowersNorm (j + 1) (derivativeSupport Q h)
          (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
    rw [← gowersNorm_restrict_cubeCount, gowersNorm_derivative]
    simp only [multiplicativeDerivative_restrictTo, gowersNorm_restrict_cubeCount]
  rw [Fintype.expect_eq_sum_div_card] at hm
  simp only [div_mul_eq_mul_div] at hm
  rw [← Finset.sum_div, div_div, ← pow_succ] at hm
  have hH : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (div_left_inj' (pow_ne_zero (j + 3) hH)).mp hm

theorem restrictedGowersNorm_derivative (j : ℕ) {Q : Finset H} (hQ : Q.Nonempty)
    (f : H → ℂ) :
    restrictedGowersNorm (j + 2) Q f ^ (2 ^ (j + 2)) =
      ∑ h, ((groupCubeCount (j + 1) (derivativeSupport Q h) : ℝ) /
        groupCubeCount (j + 2) Q) *
        restrictedGowersNorm (j + 1) (derivativeSupport Q h)
          (multiplicativeDerivative f h) ^ (2 ^ (j + 1)) := by
  have hC : (groupCubeCount (j + 2) Q : ℝ) ≠ 0 := by
    exact_mod_cast (groupCubeCount_pos (j + 2) hQ).ne'
  calc
    _ = ((groupCubeCount (j + 2) Q : ℝ) *
        restrictedGowersNorm (j + 2) Q f ^ (2 ^ (j + 2))) /
        groupCubeCount (j + 2) Q := by field_simp
    _ = _ := by
      rw [restrictedGowersNorm_derivative_mul_count, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

end Erdos3

end

end OAI

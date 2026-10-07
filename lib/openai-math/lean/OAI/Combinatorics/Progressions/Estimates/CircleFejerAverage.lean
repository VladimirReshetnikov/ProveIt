import OAI.Combinatorics.Progressions.Linear.CircleFejerKernel

namespace OAI

section

namespace Erdos3.CircleFourier

open MeasureTheory
open scoped BigOperators

theorem abs_lt_of_mem_fejerFrequencies {N : ℕ} {h : ℤ} (hh : h ∈ fejerFrequencies N) :
    |h| < (N : ℤ) := by
  classical
  obtain ⟨⟨i, j⟩, _, rfl⟩ := Finset.mem_image.mp hh
  unfold fejerPairFrequency
  rw [abs_lt]
  constructor <;> omega

theorem card_fejerFrequencies_le (N : ℕ) : (fejerFrequencies N).card ≤ N ^ 2 := by
  classical
  exact (Finset.card_image_le).trans_eq (by simp [pow_two])

theorem circle_integrable_of_continuous {E : Type*} [NormedAddCommGroup E]
    {f : Circle → E} (hf : Continuous f) : Integrable f circleHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

noncomputable def fejerFirstMoment (N : ℕ) : ℝ :=
  ∫ x : Circle, ‖x‖ * fejerPolynomial N x ∂circleHaar

theorem fejerFirstMoment_nonneg (N : ℕ) : 0 ≤ fejerFirstMoment N :=
  integral_nonneg (fun x => mul_nonneg (norm_nonneg x) (fejerPolynomial_nonneg N x))

theorem fejerFirstMoment_le {N : ℕ} (hN : 0 < N) {η : ℝ} (hη : 0 < η) :
    fejerFirstMoment N ≤ η + 1 / (8 * N * η ^ 2) := by
  have hpoint (x : Circle) : ‖x‖ * fejerPolynomial N x ≤
      η * fejerPolynomial N x + 1 / (8 * N * η ^ 2) := by
    by_cases hx : ‖x‖ < η
    · have h := mul_le_mul_of_nonneg_right hx.le (fejerPolynomial_nonneg N x)
      exact h.trans (le_add_of_nonneg_right (by positivity))
    · have htail := fejerPolynomial_le_of_distance hN hη (le_of_not_gt hx)
      have hnorm : ‖x‖ ≤ 1 / 2 := integerDistance_le_half x
      have hprod := mul_le_mul hnorm htail (fejerPolynomial_nonneg N x) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have heq : (1 / 2 : ℝ) * (1 / (4 * N * η ^ 2)) = 1 / (8 * N * η ^ 2) := by ring
      rw [heq] at hprod
      exact hprod.trans (le_add_of_nonneg_left (mul_nonneg hη.le (fejerPolynomial_nonneg N x)))
  have hi : Integrable (fun x : Circle => ‖x‖ * fejerPolynomial N x) circleHaar :=
    circle_integrable_of_continuous (continuous_norm.mul (continuous_fejerPolynomial N))
  have hj : Integrable (fun x : Circle => η * fejerPolynomial N x + 1 / (8 * N * η ^ 2)) circleHaar :=
    circle_integrable_of_continuous ((continuous_const.mul (continuous_fejerPolynomial N)).add continuous_const)
  calc
    fejerFirstMoment N ≤ ∫ x : Circle,
        η * fejerPolynomial N x + 1 / (8 * N * η ^ 2) ∂circleHaar := integral_mono hi hj hpoint
    _ = η + 1 / (8 * N * η ^ 2) := by
      have hk : Integrable (fun x : Circle => η * fejerPolynomial N x) circleHaar :=
        circle_integrable_of_continuous (continuous_const.mul (continuous_fejerPolynomial N))
      rw [integral_add hk (integrable_const _),
        integral_const_mul, integral_fejerPolynomial hN]
      simp

end Erdos3.CircleFourier

end

section

namespace Erdos3.CircleFourier

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

noncomputable def fejerAverage (N : ℕ) (f : Circle → E) : E :=
  ∫ t : Circle, fejerPolynomial N t • f t ∂circleHaar

theorem fejerAverage_const {N : ℕ} (hN : 0 < N) (c : E) :
    fejerAverage N (fun _ => c) = c := by
  rw [fejerAverage, integral_smul_const, integral_fejerPolynomial hN, one_smul]

theorem fejerAverage_sub_const {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) (c : E) :
    fejerAverage N f - c = fejerAverage N (fun t => f t - c) := by
  unfold fejerAverage
  simp only [smul_sub]
  have hi : Integrable (fun t : Circle => fejerPolynomial N t • f t) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul hf)
  have hc : Integrable (fun t : Circle => fejerPolynomial N t • c) circleHaar :=
    circle_integrable_of_continuous ((continuous_fejerPolynomial N).smul continuous_const)
  rw [integral_sub hi hc,
    integral_smul_const, integral_fejerPolynomial hN, one_smul]

theorem norm_fejerAverage_sub_le {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) {L : ℝ} (_hL : 0 ≤ L)
    (hbound : ∀ t, ‖f t - f 0‖ ≤ L * ‖t‖) :
    ‖fejerAverage N f - f 0‖ ≤ L * fejerFirstMoment N := by
  rw [fejerAverage_sub_const hN hf (f 0)]
  calc
    ‖fejerAverage N (fun t => f t - f 0)‖ ≤
        ∫ t : Circle, ‖fejerPolynomial N t • (f t - f 0)‖ ∂circleHaar :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : Circle, L * (‖t‖ * fejerPolynomial N t) ∂circleHaar := by
      apply integral_mono
      · exact circle_integrable_of_continuous
          (((continuous_fejerPolynomial N).smul (hf.sub continuous_const)).norm)
      · exact circle_integrable_of_continuous
          (continuous_const.mul (continuous_norm.mul (continuous_fejerPolynomial N)))
      · intro t
        dsimp only
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (fejerPolynomial_nonneg N t)]
        nlinarith [mul_le_mul_of_nonneg_left (hbound t) (fejerPolynomial_nonneg N t)]
    _ = L * fejerFirstMoment N := integral_const_mul L _

theorem norm_fejerAverage_sub_le_explicit {N : ℕ} (hN : 0 < N) {f : Circle → E}
    (hf : Continuous f) {L η : ℝ} (hL : 0 ≤ L) (hη : 0 < η)
    (hbound : ∀ t, ‖f t - f 0‖ ≤ L * ‖t‖) :
    ‖fejerAverage N f - f 0‖ ≤ L * (η + 1 / (8 * N * η ^ 2)) :=
  (norm_fejerAverage_sub_le hN hf hL hbound).trans
    (mul_le_mul_of_nonneg_left (fejerFirstMoment_le hN hη) hL)

end Erdos3.CircleFourier

end

end OAI

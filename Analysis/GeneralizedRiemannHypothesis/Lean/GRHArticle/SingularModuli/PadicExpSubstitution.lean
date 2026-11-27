import GRHArticle.SingularModuli.PadicConvergence
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# The forward p-adic exponential substitution

The coefficient series used in the local root-count lemma represents the
original sparse expression after substituting x = a exp(bY). The radius
estimate below uses the same factorial majorant as the convergence proof.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators NNReal ENNReal Topology

variable {p : ℕ} [Fact (Nat.Prime p)]

/-- The lower bound p^(-1/(p-1)) for the exponential radius. -/
noncomputable def padicExpRadiusLower (p : ℕ) [Fact (Nat.Prime p)] : ℝ≥0 :=
  ⟨(factorialGrowthBound p)⁻¹, inv_nonneg.mpr (factorialGrowthBound_pos p).le⟩

theorem padicExpRadiusLower_le_radius :
    (padicExpRadiusLower p : ℝ≥0∞) ≤ (NormedSpace.expSeries ℂ_[p] ℂ_[p]).radius := by
  refine (NormedSpace.expSeries ℂ_[p] ℂ_[p]).le_radius_of_bound (r := padicExpRadiusLower p) 1 ?_
  intro k
  rw [NormedSpace.expSeries_eq_ofScalars, FormalMultilinearSeries.ofScalars_norm]
  change ‖(k.factorial : ℂ_[p])⁻¹‖ * ((factorialGrowthBound p)⁻¹) ^ k ≤ 1
  calc
    _ ≤ factorialGrowthBound p ^ k * ((factorialGrowthBound p)⁻¹) ^ k :=
      mul_le_mul_of_nonneg_right (norm_inv_factorial_le (p := p) k)
        (pow_nonneg (inv_nonneg.mpr (factorialGrowthBound_pos p).le) k)
    _ = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (factorialGrowthBound_pos p).ne', one_pow]

theorem mem_exp_ball_of_geometric_ratio_lt_one {x : ℂ_[p]}
    (hx : ‖x‖ * factorialGrowthBound p < 1) :
    x ∈ Metric.eball (0 : ℂ_[p]) (NormedSpace.expSeries ℂ_[p] ℂ_[p]).radius := by
  rw [mem_eball_zero_iff]
  refine lt_of_lt_of_le ?_ (padicExpRadiusLower_le_radius (p := p))
  change (↑‖x‖₊ : ℝ≥0∞) < (padicExpRadiusLower p : ℝ≥0∞)
  rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe]
  change ‖x‖ < (factorialGrowthBound p)⁻¹
  rw [← one_div]
  exact (lt_div_iff₀ (factorialGrowthBound_pos p)).mpr hx

private theorem norm_padicComplex_natCast_le_one (n : ℕ) : ‖(n : ℂ_[p])‖ ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    exact (IsUltrametricDist.norm_add_le_max (n : ℂ_[p]) 1).trans
      (max_le ih (by simp))

private theorem geometric_ratio_natCast_mul_lt_one {x : ℂ_[p]}
    (hx : ‖x‖ * factorialGrowthBound p < 1) (n : ℕ) :
    ‖(n : ℂ_[p]) * x‖ * factorialGrowthBound p < 1 := by
  have hnorm : ‖(n : ℂ_[p]) * x‖ ≤ ‖x‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg x) (norm_padicComplex_natCast_le_one n)
  exact (mul_le_mul_of_nonneg_right hnorm (factorialGrowthBound_pos p).le).trans_lt hx

theorem exp_natCast_mul_of_geometric_ratio_lt_one (x : ℂ_[p])
    (hx : ‖x‖ * factorialGrowthBound p < 1) (n : ℕ) :
    NormedSpace.exp ((n : ℂ_[p]) * x) = NormedSpace.exp x ^ n := by
  induction n with
  | zero => simp [NormedSpace.exp_zero]
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, pow_succ, ← ih]
    exact NormedSpace.exp_add_of_mem_ball
      (mem_exp_ball_of_geometric_ratio_lt_one (geometric_ratio_natCast_mul_lt_one hx n))
      (mem_exp_ball_of_geometric_ratio_lt_one hx)

theorem exp_substitution_eq_tsum {t : ℕ}
    (n : Fin t → ℕ) (c : Fin t → ℂ_[p]) (a b y : ℂ_[p])
    (hb : ‖b‖ * factorialGrowthBound p < 1) (hy : ‖y‖ ≤ 1) :
    (∑ i, c i * (a * NormedSpace.exp (b * y)) ^ n i) =
      ∑' k, exponentialCoefficient n c a b k * y ^ k := by
  have hnorm : ‖b * y‖ ≤ ‖b‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg b) hy
  have hby := (mul_le_mul_of_nonneg_right hnorm (factorialGrowthBound_pos p).le).trans_lt hb
  let x : Fin t → ℂ_[p] := fun i => (n i : ℂ_[p]) * (b * y)
  let d : Fin t → ℂ_[p] := fun i => c i * a ^ n i
  have hs (i : Fin t) : Summable (fun k => x i ^ k / (k.factorial : ℂ_[p])) :=
    NormedSpace.expSeries_div_summable_of_mem_ball ℂ_[p] (x i)
      (mem_exp_ball_of_geometric_ratio_lt_one (geometric_ratio_natCast_mul_lt_one hby (n i)))
  calc
    _ = ∑ i, d i * NormedSpace.exp (x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_pow, ← exp_natCast_mul_of_geometric_ratio_lt_one (b * y) hby (n i)]
      simp only [d, x, mul_assoc]
    _ = ∑ i, ∑' k, d i * (x i ^ k / (k.factorial : ℂ_[p])) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [NormedSpace.exp_eq_tsum_div, (hs i).tsum_mul_left]
    _ = _ := by
      rw [← Summable.tsum_finsetSum (fun i _ => (hs i).mul_left (d i))]
      apply tsum_congr
      intro k
      simp only [exponentialCoefficient, moment, d, x, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [mul_pow, div_eq_mul_inv]
      ring

end GRHArticle.SingularModuli

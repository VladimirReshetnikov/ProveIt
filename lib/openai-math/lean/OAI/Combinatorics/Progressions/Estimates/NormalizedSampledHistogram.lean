import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import OAI.Combinatorics.Progressions.Lattices.CompactLatticeApproximation
import OAI.Combinatorics.Progressions.Probability.NormalizedDensityL1

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem sampledWeightSum_bounds (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hI : 0 < ∫ x, ψ x) (hlarge : 2 * ((2 * R + 2) * (L : ℝ)) / (∫ x, ψ x) ≤ S) :
    (∫ x, ψ x) * S / 2 ≤ sampledWeightSum ψ a S R ∧
      sampledWeightSum ψ a S R ≤ 3 * (∫ x, ψ x) * S / 2 := by
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlarge' := (div_le_iff₀ hI).mp hlarge
  have hs : (2 * R + 2) * (L : ℝ) / S ≤ (∫ x, ψ x) / 2 :=
    (div_le_iff₀ hSp).mpr (by nlinarith)
  have he := (sampledWeightSum_error ψ hLip (a := a) hR hS hsupport).trans hs
  obtain ⟨hl, hu⟩ := abs_le.mp he
  have hl' : (∫ x, ψ x) / 2 ≤ sampledWeightSum ψ a S R / S := by linarith
  have hu' : sampledWeightSum ψ a S R / S ≤ 3 * (∫ x, ψ x) / 2 := by linarith
  constructor
  · have hh := (le_div_iff₀ hSp).mp hl'
    nlinarith
  · have hh := (div_le_iff₀ hSp).mp hu'
    nlinarith

theorem sampledWeightSum_pos (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hI : 0 < ∫ x, ψ x) (hlarge : 2 * ((2 * R + 2) * (L : ℝ)) / (∫ x, ψ x) ≤ S) :
    0 < sampledWeightSum ψ a S R :=
  lt_of_lt_of_le (by positivity) (sampledWeightSum_bounds ψ hLip (a := a) hR hS hsupport hI hlarge).1

theorem sampledWeightSum_scale_ratio (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hI : 0 < ∫ x, ψ x) (hlarge : 2 * ((2 * R + 2) * (L : ℝ)) / (∫ x, ψ x) ≤ S) :
    S / sampledWeightSum ψ a S R ≤ 2 / (∫ x, ψ x) := by
  apply (div_le_div_iff₀ (sampledWeightSum_pos ψ hLip hR hS hsupport hI hlarge) hI).mpr
  have hb := (sampledWeightSum_bounds ψ hLip (a := a) hR hS hsupport hI hlarge).1
  nlinarith

theorem compactProfile_integral_pos (ψ : ℝ → ℝ) (hcont : Continuous ψ)
    {R : ℝ} (hsupport : ∀ x, R < |x| → ψ x = 0) (hψ : ∀ x, 0 ≤ ψ x)
    {x : ℝ} (hx : ψ x ≠ 0) : 0 < ∫ y, ψ y :=
  integral_pos_of_integrable_nonneg_nonzero hcont
    (compactInterval_integrable ψ hcont R hsupport) hψ hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def sampledWeightMass (ψ : ℝ → ℝ) (a S R : ℝ) (k : ℤ) : ℝ :=
  sampledWeight ψ a S k / sampledWeightSum ψ a S R

noncomputable def sampledWeightInterpolant (ψ : ℝ → ℝ) (a S R K u : ℝ) : ℝ :=
  K * ψ ((K * u - a) / S) / sampledWeightSum ψ a S R

theorem sampledWeightMass_sum (ψ : ℝ → ℝ) (a S R : ℝ)
    (hZ : sampledWeightSum ψ a S R ≠ 0) :
    (∑ k ∈ sampledWeightIndices a S R, sampledWeightMass ψ a S R k) = 1 := by
  simp only [sampledWeightMass, ← Finset.sum_div]
  exact div_self hZ

theorem sampledWeightMass_nonneg (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x) (a S R : ℝ)
    (k : ℤ) : 0 ≤ sampledWeightMass ψ a S R k :=
  div_nonneg (hψ _) (sampledWeightSum_nonneg ψ hψ a S R)

theorem sampledWeightInterpolant_at_lattice (ψ : ℝ → ℝ) (a S R : ℝ)
    {K : ℝ} (hK : K ≠ 0) (k : ℤ) :
    sampledWeightInterpolant ψ a S R K ((k : ℝ) / K) = K * sampledWeightMass ψ a S R k := by
  simp only [sampledWeightInterpolant, sampledWeightMass, sampledWeight,
    mul_div_cancel₀ _ hK, mul_div_assoc]

theorem sampledWeightInterpolant_contDiff (ψ : ℝ → ℝ) {n : ℕ∞ω} (hψ : ContDiff ℝ n ψ)
    (a S R K : ℝ) : ContDiff ℝ n (sampledWeightInterpolant ψ a S R K) := by
  have ha : ContDiff ℝ n (fun u : ℝ => (K * u - a) / S) :=
    ((contDiff_const.mul contDiff_id).sub contDiff_const).div_const S
  exact (contDiff_const.mul (hψ.comp ha)).div_const _

theorem iteratedDeriv_affine (n : ℕ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ n ψ) (A B u : ℝ) :
    iteratedDeriv n (fun x => ψ (A * x + B)) u = A ^ n * iteratedDeriv n ψ (A * u + B) := by
  have hshift : ContDiff ℝ n (fun x : ℝ => ψ (x + B)) := hψ.comp (contDiff_id.add contDiff_const)
  have he := congrFun (iteratedDeriv_comp_const_mul hshift A) u
  simpa only [iteratedDeriv_comp_add_const] using he

theorem sampledWeightInterpolant_deriv (n : ℕ) (ψ : ℝ → ℝ) (hψ : ContDiff ℝ n ψ)
    (a S R K u : ℝ) :
    iteratedDeriv n (sampledWeightInterpolant ψ a S R K) u =
      (K / sampledWeightSum ψ a S R) * (K / S) ^ n * iteratedDeriv n ψ ((K * u - a) / S) := by
  have he : sampledWeightInterpolant ψ a S R K =
      fun x => (K / sampledWeightSum ψ a S R) * ψ ((K / S) * x + (-a / S)) := by
    funext x
    unfold sampledWeightInterpolant
    rw [show (K * x - a) / S = (K / S) * x + (-a / S) by ring]
    ring
  rw [he, iteratedDeriv_const_mul_field, iteratedDeriv_affine n ψ hψ]
  have hx : (K / S) * u + (-a / S) = (K * u - a) / S := by ring
  rw [hx]
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def normalizedWeightHistogram (ψ : ℝ → ℝ) (a S R x : ℝ) : ℝ :=
  sampledWeightHistogram ψ a S R x / (sampledWeightSum ψ a S R / S)

theorem normalizedWeightHistogram_integrable (ψ : ℝ → ℝ) (a S R : ℝ) :
    Integrable (normalizedWeightHistogram ψ a S R) :=
  (sampledWeightHistogram_integrable ψ a S R).div_const _

theorem normalizedWeightHistogram_integral (ψ : ℝ → ℝ) (a R : ℝ)
    {S : ℝ} (hS : 0 < S) (hZ : sampledWeightSum ψ a S R ≠ 0) :
    (∫ x, normalizedWeightHistogram ψ a S R x) = 1 := by
  unfold normalizedWeightHistogram
  rw [integral_div, sampledWeightHistogram_integral ψ a hS R, div_self (div_ne_zero hZ hS.ne')]

theorem normalizedWeightHistogram_on_cell (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ) {x : ℝ}
    (hx : x ∈ latticeSamplingCell a S k) :
    normalizedWeightHistogram ψ a S R x = S * sampledWeightMass ψ a S R k := by
  rw [normalizedWeightHistogram, sampledWeightHistogram_eq ψ hS hsupport]
  unfold latticeSample
  rw [(latticeSamplingCell_iff hS k).mp hx]
  simp only [sampledWeightMass, sampledWeight, div_div_eq_mul_div]
  ring

theorem normalizedWeightHistogram_nonneg (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    0 ≤ normalizedWeightHistogram ψ a S R x := by
  rw [normalizedWeightHistogram, sampledWeightHistogram_eq ψ hS hsupport]
  exact div_nonneg (hψ _) (div_nonneg (sampledWeightSum_nonneg ψ hψ a S R) hS.le)

theorem normalizedWeightHistogram_l1 (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hψ : ∀ x, 0 ≤ ψ x) (hI : 0 < ∫ x, ψ x)
    (hlarge : 2 * ((2 * R + 2) * (L : ℝ)) / (∫ x, ψ x) ≤ S) :
    (∫ x, |normalizedWeightHistogram ψ a S R x - ψ x / (∫ y, ψ y)|) ≤
      2 * ((2 * R + 2) * (L : ℝ)) / (S * (∫ x, ψ x)) := by
  have hSp := lt_of_lt_of_le zero_lt_one hS
  have hZ := sampledWeightSum_pos ψ hLip (a := a) hR hS hsupport hI hlarge
  have hg0 : ∀ x, 0 ≤ sampledWeightHistogram ψ a S R x := by
    intro x
    rw [sampledWeightHistogram_eq ψ hSp hsupport]
    exact hψ _
  have hgI : 0 < ∫ x, sampledWeightHistogram ψ a S R x := by
    rw [sampledWeightHistogram_integral ψ a hSp R]
    exact div_pos hZ hSp
  have he := normalized_density_l1 volume ψ (sampledWeightHistogram ψ a S R)
    (compactInterval_integrable ψ hLip.continuous R hsupport)
    (sampledWeightHistogram_integrable ψ a S R) hg0 hI hgI
  rw [sampledWeightHistogram_integral ψ a hSp R] at he
  have herr : (∫ x, |ψ x - sampledWeightHistogram ψ a S R x|) ≤
      (2 * R + 2) * (L : ℝ) / S := by
    simpa only [Real.norm_eq_abs, abs_sub_comm] using
      sampledWeightHistogram_l1_error ψ hLip (a := a) hR hS hsupport
  calc
    _ ≤ 2 * (∫ x, |ψ x - sampledWeightHistogram ψ a S R x|) / (∫ x, ψ x) := by
      simpa only [normalizedWeightHistogram, abs_sub_comm] using he
    _ ≤ 2 * ((2 * R + 2) * (L : ℝ) / S) / (∫ x, ψ x) := by
      gcongr
    _ = _ := by ring

end Erdos3

end

end OAI

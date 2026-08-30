import FabiusFunction.StieltjesCauchyTransform

/-!
# The Herglotz face of the Cauchy transform

Off the real axis the Cauchy transform of the up-measure is
integrable, reflects under conjugation (`R(z̄) = conj (R z)`), and
maps the upper half-plane strictly into the lower one:
`Im R(z) ≤ -Im z/(‖z‖+1)² < 0` for `Im z > 0` — the transform is
minus a Herglotz/Nevanlinna function, with a quantitative sign
bound.  By reflection it maps the lower half-plane strictly into the
upper.  These are the orientation data of the boundary (Plemelj)
theory on the cut `[-1,1]`.
-/

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

namespace Fabius

/-- Off the real axis the Cauchy kernel is integrable: it is bounded
by `|Im z|⁻¹` everywhere. -/
theorem integrable_inv_sub_complex_of_im_ne_zero (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun x : ℝ => (z - x)⁻¹) (rvachevMeasure F) := by
  haveI := rvachevMeasure_isProbability F hF
  refine Integrable.mono' (integrable_const (|z.im|⁻¹))
    ((measurable_inv_sub_complex z).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have him : |z.im| = |(z - (x : ℂ)).im| := by
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero]
  have hle : |z.im| ≤ ‖z - (x : ℂ)‖ := by
    rw [him]
    exact Complex.abs_im_le_norm _
  rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
  exact one_div_le_one_div_of_le (abs_pos.mpr hz) hle

/-- **Schwarz reflection**: the Cauchy transform commutes with
conjugation, `R(z̄) = conj (R z)`. -/
theorem rvachevCauchyTransform_conj (F : BoundedFabius) (z : ℂ) :
    rvachevCauchyTransform F (conj z) =
      conj (rvachevCauchyTransform F z) := by
  rw [rvachevCauchyTransform_apply, rvachevCauchyTransform_apply,
    ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [map_inv₀, map_sub, Complex.conj_ofReal]

/-- **The quantitative Herglotz bound**: for `Im z > 0`,
`Im R(z) ≤ -Im z/(‖z‖+1)²`. -/
theorem im_rvachevCauchyTransform_le (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 0 < z.im) :
    (rvachevCauchyTransform F z).im ≤ -(z.im / (‖z‖ + 1) ^ 2) := by
  haveI := rvachevMeasure_isProbability F hF
  have hint : Integrable (fun x : ℝ => (z - x)⁻¹)
      (rvachevMeasure F) :=
    integrable_inv_sub_complex_of_im_ne_zero F hF (ne_of_gt hz)
  have hbound : ∀ᵐ x : ℝ ∂(rvachevMeasure F),
      RCLike.im ((z - (x : ℂ))⁻¹) ≤ -(z.im / (‖z‖ + 1) ^ 2) := by
    filter_upwards [ae_mem_Ioo_rvachevMeasure F hF] with x hx
    have hzx : z - (x : ℂ) ≠ 0 := by
      intro h0
      have h1 : (z - (x : ℂ)).im = 0 := by
        rw [h0, Complex.zero_im]
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
      exact (ne_of_gt hz) h1
    have hNpos : 0 < Complex.normSq (z - (x : ℂ)) :=
      Complex.normSq_pos.mpr hzx
    have hnle : ‖z - (x : ℂ)‖ ≤ ‖z‖ + 1 := by
      have h1 : ‖(x : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩)
      calc ‖z - (x : ℂ)‖ ≤ ‖z‖ + ‖(x : ℂ)‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + 1 := by linarith
    have hNle : Complex.normSq (z - (x : ℂ)) ≤ (‖z‖ + 1) ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) hnle 2
    have h1 : 1 / (‖z‖ + 1) ^ 2 ≤
        1 / Complex.normSq (z - (x : ℂ)) :=
      one_div_le_one_div_of_le hNpos hNle
    have h2 : z.im * (1 / (‖z‖ + 1) ^ 2) ≤
        z.im * (1 / Complex.normSq (z - (x : ℂ))) :=
      mul_le_mul_of_nonneg_left h1 (le_of_lt hz)
    have h3 : z.im / (‖z‖ + 1) ^ 2 ≤
        z.im / Complex.normSq (z - (x : ℂ)) := by
      rw [div_eq_mul_one_div (z.im) ((‖z‖ + 1) ^ 2),
        div_eq_mul_one_div (z.im) (Complex.normSq (z - (x : ℂ)))]
      exact h2
    have him : RCLike.im ((z - (x : ℂ))⁻¹) =
        -(z.im / Complex.normSq (z - (x : ℂ))) := by
      rw [RCLike.im_to_complex, Complex.inv_im, Complex.sub_im,
        Complex.ofReal_im, sub_zero, neg_div]
    rw [him]
    exact neg_le_neg h3
  have hkey : ∫ x : ℝ,
      RCLike.im ((z - (x : ℂ))⁻¹) ∂(rvachevMeasure F) ≤
      -(z.im / (‖z‖ + 1) ^ 2) := by
    calc ∫ x : ℝ, RCLike.im ((z - (x : ℂ))⁻¹) ∂(rvachevMeasure F)
        ≤ ∫ _x : ℝ, -(z.im / (‖z‖ + 1) ^ 2) ∂(rvachevMeasure F) :=
          integral_mono_ae hint.im (integrable_const _) hbound
      _ = -(z.im / (‖z‖ + 1) ^ 2) := by
          rw [integral_const]
          simp
  rw [rvachevCauchyTransform_apply, ← RCLike.im_to_complex,
    ← integral_im hint]
  exact hkey

/-- **The Herglotz sign**: the transform maps the upper half-plane
strictly into the lower one. -/
theorem im_rvachevCauchyTransform_neg (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : 0 < z.im) :
    (rvachevCauchyTransform F z).im < 0 := by
  have h := im_rvachevCauchyTransform_le F hF hz
  have hpos : 0 < z.im / (‖z‖ + 1) ^ 2 := by positivity
  linarith

/-- By reflection, the transform maps the lower half-plane strictly
into the upper one. -/
theorem im_rvachevCauchyTransform_pos (F : BoundedFabius)
    (hF : IsFabius F) {z : ℂ} (hz : z.im < 0) :
    0 < (rvachevCauchyTransform F z).im := by
  have hconj : 0 < (conj z).im := by
    rw [Complex.conj_im]
    linarith
  have h := im_rvachevCauchyTransform_neg F hF hconj
  rw [rvachevCauchyTransform_conj F z, Complex.conj_im] at h
  linarith

/-- **The Poisson display**: off the real axis the imaginary part of
the Cauchy transform is exactly minus the Poisson integral of the
up-measure — the entry identity of the Plemelj boundary theory. -/
theorem im_rvachevCauchyTransform_eq (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (rvachevCauchyTransform F (x + ε * Complex.I)).im =
      -∫ t : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) ∂(rvachevMeasure F) := by
  have him : ((x : ℂ) + ε * Complex.I).im = ε := by simp
  have hint : Integrable
      (fun t : ℝ => ((x : ℂ) + ε * Complex.I - t)⁻¹)
      (rvachevMeasure F) :=
    integrable_inv_sub_complex_of_im_ne_zero F hF
      (by rw [him]; exact hε)
  rw [rvachevCauchyTransform_apply, ← RCLike.im_to_complex,
    ← integral_im hint, ← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  have hre : ((x : ℂ) + ε * Complex.I - t).re = x - t := by simp
  have him2 : ((x : ℂ) + ε * Complex.I - t).im = ε := by simp
  have hD : (x - t) * (x - t) + ε * ε = (x - t) ^ 2 + ε ^ 2 := by
    ring
  rw [RCLike.im_to_complex, Complex.inv_im, Complex.normSq_apply,
    hre, him2, hD, neg_div]

/-- **The conjugate-Poisson display**: the real part of the Cauchy
transform is the conjugate Poisson integral of the up-measure. -/
theorem re_rvachevCauchyTransform_eq (F : BoundedFabius)
    (hF : IsFabius F) (x : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (rvachevCauchyTransform F (x + ε * Complex.I)).re =
      ∫ t : ℝ, (x - t) / ((x - t) ^ 2 + ε ^ 2)
        ∂(rvachevMeasure F) := by
  have him : ((x : ℂ) + ε * Complex.I).im = ε := by simp
  have hint : Integrable
      (fun t : ℝ => ((x : ℂ) + ε * Complex.I - t)⁻¹)
      (rvachevMeasure F) :=
    integrable_inv_sub_complex_of_im_ne_zero F hF
      (by rw [him]; exact hε)
  rw [rvachevCauchyTransform_apply, ← RCLike.re_to_complex,
    ← integral_re hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  have hre : ((x : ℂ) + ε * Complex.I - t).re = x - t := by simp
  have him2 : ((x : ℂ) + ε * Complex.I - t).im = ε := by simp
  have hD : (x - t) * (x - t) + ε * ε = (x - t) ^ 2 + ε ^ 2 := by
    ring
  rw [RCLike.re_to_complex, Complex.inv_re, Complex.normSq_apply,
    hre, him2, hD]

end Fabius

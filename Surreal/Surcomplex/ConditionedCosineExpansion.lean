import Surreal.Algebra.CirclePerturbation
import Surreal.Surcomplex.ContactAngleDifference
import Surreal.Surcomplex.InverseTrigonometricTaylor
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Uniform second-order inverse-cosine expansion

For `trigonometry:thm:conditioned`, the small parameter is `u = ε/s²`.
The exact half-angle formula and a positive square-root ratio produce
`h = -s u - c s u²/2 + s u³ H`, with finite `H`. This holds even when
`s` is infinitesimal and the value group has arbitrary rank.
-/

universe u

namespace Surreal.Surcomplex.ConditionedCosine

open Foundations

noncomputable section

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

private theorem finite_half : SignSequence.IsFinite (1 / 2 : SignSequence.{u}) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)

/-- An infinitesimal perturbation relative to the squared sine stays in the inverse-cosine domain. -/
theorem perturbed_mem_Ioo (c s e : SignSequence.{u}) (hs : 0 < s)
    (hcircle : c ^ 2 + s ^ 2 = 1) (hu : SignSequence.IsInfinitesimal (e / s ^ 2)) :
    c + e ∈ Set.Ioo (-1) 1 := by
  apply CirclePerturbation.perturbed_mem_Ioo c s e hs hcircle
  have he := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt _).mp hu
    (1 / 2) (by norm_num)
  simpa only [map_div₀, map_one, map_ofNat] using he

private theorem finite_heightRemainder (c s u w : SignSequence.{u})
    (hc : SignSequence.IsFinite c) (hs : SignSequence.IsFinite s)
    (hu : SignSequence.IsFinite u) (hw : SignSequence.IsFinite w) :
    SignSequence.IsFinite (CirclePerturbation.heightRemainder c s u w) := by
  unfold CirclePerturbation.heightRemainder
  exact SignSequence.finite_add
    (SignSequence.finite_mul
      (SignSequence.finite_mul
        (SignSequence.finite_mul hc (SignSequence.finite_add
          (SignSequence.finite_mul finite_two hc)
          (SignSequence.finite_mul (SignSequence.finite_pow hs 2) hu)))
        (SignSequence.finite_pow hw 2)) (SignSequence.finite_add hw finite_half))
    (SignSequence.finite_mul (SignSequence.finite_pow hs 2) (SignSequence.finite_pow hw 2))

/-- The signed inverse-cosine difference has an exact finite cubic remainder in `u=ε/s²`. -/
theorem normalized_expansion (c s e : SignSequence.{u})
    (hc : SignSequence.IsFinite c) (hsf : SignSequence.IsFinite s) (hs : 0 < s)
    (hcircle : c ^ 2 + s ^ 2 = 1) (hu : SignSequence.IsInfinitesimal (e / s ^ 2)) :
    ∃ H : SignSequence.{u}, SignSequence.IsFinite H ∧
      arccosFunction (c + e) - arccosFunction c =
        -s * (e / s ^ 2) - c * s / 2 * (e / s ^ 2) ^ 2 + s * (e / s ^ 2) ^ 3 * H := by
  let u := e / s ^ 2
  let b := SignSequence.sqrt (1 - (c + e) ^ 2)
  let r := b / s
  let w := (1 + r)⁻¹
  have huf : SignSequence.IsFinite u := SignSequence.finite_of_infinitesimal hu
  have he : e = s ^ 2 * u := by dsimp only [u]; field_simp
  have hy := perturbed_mem_Ioo c s e hs hcircle hu
  have hx := CirclePerturbation.coordinate_mem_Ioo c s hs hcircle
  have hbpos : 0 < 1 - (c + e) ^ 2 := by nlinarith [hy.1, hy.2]
  have hbp : 0 < b := SignSequence.sqrt_pos hbpos
  have hb2 : b ^ 2 = 1 - (c + e) ^ 2 := SignSequence.sqrt_sq hbpos.le
  have hrp : 0 < r := div_pos hbp hs
  have hr2 : r ^ 2 = 1 - 2 * c * u - s ^ 2 * u ^ 2 := by
    dsimp only [r]
    rw [div_pow, hb2]
    apply (div_eq_iff (pow_ne_zero 2 hs.ne')).mpr
    rw [he]
    linear_combination -hcircle
  have hri : SignSequence.IsInfinitesimal (r ^ 2 - 1) := by
    rw [hr2, show 1 - 2 * c * u - s ^ 2 * u ^ 2 - 1 =
      u * (-(2 * c) - s ^ 2 * u) by ring]
    exact SignSequence.infinitesimal_mul_finite hu
      (SignSequence.finite_sub (SignSequence.finite_neg (SignSequence.finite_mul finite_two hc))
        (SignSequence.finite_mul (SignSequence.finite_pow hsf 2) huf))
  obtain ⟨hrf, hrs⟩ := SignSequence.finite_standardPart_eq_one_of_sq_sub_one hrp.le hri
  have hdenf := SignSequence.finite_add SignSequence.finite_one hrf
  have hdenst : SignSequence.standardPart (1 + r) = 2 := by
    rw [SignSequence.standardPart_add SignSequence.finite_one hrf,
      SignSequence.standardPart_one, hrs]
    norm_num
  have hden : 1 + r ≠ 0 := (add_pos zero_lt_one hrp).ne'
  have hwf : SignSequence.IsFinite w :=
    SignSequence.finite_inv_of_standardPart_ne_zero hdenf (by rw [hdenst]; norm_num)
  let B := CirclePerturbation.heightRemainder c s u w
  have hBf : SignSequence.IsFinite B := finite_heightRemainder c s u w hc hsf huf hwf
  have hw : 2 * w = 1 + c / 2 * u + u ^ 2 * B :=
    CirclePerturbation.reciprocal_height_expansion c s u r hr2 hden
  let t := -s * u * w
  have hti : SignSequence.IsInfinitesimal t :=
    SignSequence.infinitesimal_mul_finite
      (SignSequence.finite_mul_infinitesimal (SignSequence.finite_neg hsf) hu) hwf
  obtain ⟨R, hR, hat⟩ := arctanFunction_cubic_remainder t hti
  have hbase : SignSequence.sqrt (1 - c ^ 2) = s := by
    rw [show 1 - c ^ 2 = s ^ 2 by nlinarith only [hcircle],
      SignSequence.sqrt_sq_eq_abs, abs_of_pos hs]
  have harg : (c - (c + e)) / (s + b) = t := by
    have hsb : s + b = s * (1 + r) := by dsimp only [r]; field_simp
    rw [hsb]
    dsimp only [t, w]
    rw [he]
    field_simp
    ring
  have hdiff := arccosFunction_difference_eq_two_arctan c (c + e) hx hy
  rw [hbase, harg, hat] at hdiff
  refine ⟨-B - 2 * s ^ 2 * w ^ 3 * R,
    SignSequence.finite_sub (SignSequence.finite_neg hBf)
      (SignSequence.finite_mul
        (SignSequence.finite_mul (SignSequence.finite_mul finite_two (SignSequence.finite_pow hsf 2))
          (SignSequence.finite_pow hwf 3)) hR), ?_⟩
  change arccosFunction (c + e) - arccosFunction c =
    -s * u - c * s / 2 * u ^ 2 + s * u ^ 3 * (-B - 2 * s ^ 2 * w ^ 3 * R)
  rw [hdiff]
  dsimp only [t]
  linear_combination -s * u * hw

end
end Surreal.Surcomplex.ConditionedCosine

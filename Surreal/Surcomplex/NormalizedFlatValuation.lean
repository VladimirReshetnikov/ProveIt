import Surreal.Surcomplex.NormalizedFlatTriangle
import Surreal.Foundations.SignSequenceFiniteLeading

/-!
# The valuation scales of normalized flat triangles

All identities in `trigonometry:eq:flatvals`, the valuation clause of
`trigonometry:thm:flat`, use the actual finite horizontal coordinate and positive infinitesimal
height. Positive ordinary leading factors exclude cancellation between the two base angles.
The slack is quadratic in height, the circumradius has inverse height scale, and the inradius
has height scale.
-/

universe u

namespace Surreal.Surcomplex.NormalizedFlatTriangle

open Foundations

local notation "v" => SignSequence.valuation

variable (D : NormalizedFlatTriangle.{u})

/-- Both base angles and their sum have exactly the positive height's valuation. -/
theorem valuation_base_angles :
    v D.triangle.angleA.val = v D.y ∧ v D.triangle.angleB.val = v D.y ∧
      v (SignSequence.ofReal Real.pi - D.triangle.angleC.val) = v D.y := by
  obtain ⟨F, G, hF, hG, hFs, hGs, hAe, hBe⟩ := D.base_angles_leading_factors
  have hFp : 0 < SignSequence.standardPart F := by
    rw [hFs]
    exact inv_pos.mpr D.x_standardPart_mem.1
  have hGp : 0 < SignSequence.standardPart G := by
    rw [hGs]
    exact inv_pos.mpr (sub_pos.mpr D.x_standardPart_mem.2)
  have hvF := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hF).mpr hFp.ne'
  have hvG := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hG).mpr hGp.ne'
  have hFGp : 0 < SignSequence.standardPart (F + G) := by
    rw [SignSequence.standardPart_add hF hG]
    exact add_pos hFp hGp
  have hvFG := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero
    (SignSequence.finite_add hF hG)).mpr hFGp.ne'
  have hsum : SignSequence.ofReal Real.pi - D.triangle.angleC.val =
      D.triangle.angleA.val + D.triangle.angleB.val := by
    have he := congrArg (fun θ : SignSequence.FiniteElement.{u} => θ.val) D.triangle.angle_sum
    change D.triangle.angleA.val + D.triangle.angleB.val + D.triangle.angleC.val =
      SignSequence.ofReal Real.pi at he
    linarith only [he]
  refine ⟨?_, ?_, ?_⟩
  · rw [hAe, SignSequence.valuation_mul, hvF, add_zero]
  · rw [hBe, SignSequence.valuation_mul, hvG, add_zero]
  · rw [hsum, hAe, hBe, ← mul_add, SignSequence.valuation_mul, hvFG, add_zero]

theorem valuation_angleA : v D.triangle.angleA.val = v D.y := D.valuation_base_angles.1

theorem valuation_angleB : v D.triangle.angleB.val = v D.y := D.valuation_base_angles.2.1

/-- The angle's distance from the straight angle has height valuation, without cancellation. -/
theorem valuation_angleC_supplement :
    v (SignSequence.ofReal Real.pi - D.triangle.angleC.val) = v D.y :=
  D.valuation_base_angles.2.2

/-- The first adjacent side is appreciable, even when its infinitesimal part is nonzero. -/
theorem valuation_sideA : v D.triangle.sideA = 0 := by
  apply (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero D.sideA_finite).mpr
  rw [D.standardPart_sideA]
  exact (sub_pos.mpr D.x_standardPart_mem.2).ne'

theorem valuation_sideB : v D.triangle.sideB = 0 := by
  apply (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero D.sideB_finite).mpr
  rw [D.standardPart_sideB]
  exact D.x_standardPart_mem.1.ne'

/-- The positive triangle-inequality slack has exactly twice the height valuation. -/
theorem valuation_slack :
    v (D.triangle.sideA + D.triangle.sideB - 1) = 2 • v D.y := by
  obtain ⟨E, hE, he⟩ := D.slack_quadratic_expansion
  have htwo : SignSequence.IsFinite (2 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
  have htwoS : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
    simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)
  let q : SignSequence.{u} := 2 * D.x * (1 - D.x)
  have hqf : SignSequence.IsFinite q :=
    SignSequence.finite_mul (SignSequence.finite_mul htwo D.x_finite) D.complement_finite
  have hqs : 0 < SignSequence.standardPart q := by
    dsimp only [q]
    rw [SignSequence.standardPart_mul (SignSequence.finite_mul htwo D.x_finite)
      D.complement_finite, SignSequence.standardPart_mul htwo D.x_finite, htwoS]
    exact mul_pos (mul_pos (by norm_num) D.x_standardPart_mem.1) D.complement_standardPart_pos
  have hqi := SignSequence.finite_inv_of_standardPart_ne_zero hqf hqs.ne'
  have hrem := SignSequence.infinitesimal_mul_finite
    ((SignSequence.infinitesimal_sq_iff D.y).mpr D.y_infinitesimal) hE
  have hremf := SignSequence.finite_of_infinitesimal hrem
  have hKf := SignSequence.finite_add hqi hremf
  have hKs : 0 < SignSequence.standardPart (q⁻¹ + D.y ^ 2 * E) := by
    rw [SignSequence.standardPart_add hqi hremf,
      SignSequence.standardPart_inv_of_ne_zero hqf hqs.ne',
      (SignSequence.standardPart_eq_zero_iff hremf).mpr hrem, add_zero]
    exact inv_pos.mpr hqs
  have hvK := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hKf).mpr hKs.ne'
  have hfact : D.triangle.sideA + D.triangle.sideB - 1 =
      D.y ^ 2 * (q⁻¹ + D.y ^ 2 * E) := by
    rw [he]
    dsimp only [q]
    ring
  rw [hfact, SignSequence.valuation_mul, hvK, add_zero, SignSequence.valuation.map_pow]

private theorem valuation_two : v (2 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using
    (SignSequence.valuation_ofReal_of_ne_zero (by norm_num : (2 : ℝ) ≠ 0) :
      v (SignSequence.ofReal 2 : SignSequence.{u}) = 0)

/-- The normalized circumradius has the inverse height scale. -/
theorem valuation_circumradius : v D.triangle.circumradius = -v D.y := by
  rw [D.circumradius_eq, SignSequence.valuation_div, SignSequence.valuation_mul,
    SignSequence.valuation_mul, D.valuation_sideA, D.valuation_sideB, valuation_two,
    zero_add, zero_add, zero_sub]

/-- The normalized inradius has exactly the height scale. -/
theorem valuation_inradius : v D.triangle.inradius = v D.y := by
  have hsumf := SignSequence.finite_add
    (SignSequence.finite_add D.sideA_finite D.sideB_finite) SignSequence.finite_one
  have hsums : SignSequence.standardPart (D.triangle.sideA + D.triangle.sideB + 1) = 2 := by
    rw [SignSequence.standardPart_add (SignSequence.finite_add D.sideA_finite D.sideB_finite)
      SignSequence.finite_one, SignSequence.standardPart_add D.sideA_finite D.sideB_finite,
      D.standardPart_sideA, D.standardPart_sideB, SignSequence.standardPart_one]
    ring
  have hv := (SignSequence.valuation_eq_zero_iff_standardPart_ne_zero hsumf).mpr
    (by rw [hsums]; norm_num)
  rw [D.inradius_eq, SignSequence.valuation_div, hv, sub_zero]

/-- All six valuation identities in the normalized flat-triangle theorem. -/
theorem valuations :
    v D.triangle.angleA.val = v D.y ∧
      v D.triangle.angleB.val = v D.y ∧
      v (SignSequence.ofReal Real.pi - D.triangle.angleC.val) = v D.y ∧
      v (D.triangle.sideA + D.triangle.sideB - 1) = 2 • v D.y ∧
      v D.triangle.circumradius = -v D.y ∧ v D.triangle.inradius = v D.y :=
  ⟨D.valuation_angleA, D.valuation_angleB, D.valuation_angleC_supplement,
    D.valuation_slack, D.valuation_circumradius, D.valuation_inradius⟩

end Surreal.Surcomplex.NormalizedFlatTriangle

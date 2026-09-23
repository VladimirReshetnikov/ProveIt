import Surreal.Surcomplex.NormalizedFlatTriangle
import Surreal.Foundations.SignSequenceReciprocalExpansion

/-!
# Radius expansions of normalized flat triangles

The literal circumradius and inradius brackets in `trigonometry:eq:flatslack`
follow by multiplying the two normalized side expansions and inverting the
semiperimeter denominator. Each fourth-order bracket remainder is an actual
finite surreal, retaining the source hypotheses of `trigonometry:thm:flat`.
-/

universe u

namespace Surreal.Surcomplex.NormalizedFlatTriangle

open Foundations

noncomputable section

private theorem finite_half : SignSequence.IsFinite ((1 : SignSequence.{u}) / 2) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)

private theorem finite_two : SignSequence.IsFinite (2 : SignSequence.{u}) := by
  simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)

/-- The actual circumradius has the displayed quadratic bracket and a finite quartic tail. -/
theorem circumradius_expansion (D : NormalizedFlatTriangle.{u}) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
      D.triangle.circumradius = D.x * (1 - D.x) / (2 * D.y) *
        (1 + D.y ^ 2 / 2 * (1 / D.x ^ 2 + 1 / (1 - D.x) ^ 2) + D.y ^ 4 * E) := by
  obtain ⟨A, hAf, hAe⟩ := D.sideA_quadratic_expansion
  obtain ⟨B, hBf, hBe⟩ := D.sideB_quadratic_expansion
  let a := (1 / 2) * ((1 - D.x)⁻¹) ^ 2
  let b := (1 / 2) * (D.x⁻¹) ^ 2
  let c := A * (1 - D.x)⁻¹
  let d := B * D.x⁻¹
  have haf : SignSequence.IsFinite a :=
    SignSequence.finite_mul finite_half (SignSequence.finite_pow D.inv_complement_finite 2)
  have hbf : SignSequence.IsFinite b :=
    SignSequence.finite_mul finite_half (SignSequence.finite_pow D.inv_x_finite 2)
  have hcf : SignSequence.IsFinite c := SignSequence.finite_mul hAf D.inv_complement_finite
  have hdf : SignSequence.IsFinite d := SignSequence.finite_mul hBf D.inv_x_finite
  let E := c + d + a * b + D.y ^ 2 * (a * d + b * c) + D.y ^ 4 * (c * d)
  have hEf : SignSequence.IsFinite E :=
    SignSequence.finite_add
      (SignSequence.finite_add
        (SignSequence.finite_add (SignSequence.finite_add hcf hdf)
          (SignSequence.finite_mul haf hbf))
        (SignSequence.finite_mul (SignSequence.finite_pow D.y_finite 2)
          (SignSequence.finite_add (SignSequence.finite_mul haf hdf)
            (SignSequence.finite_mul hbf hcf))))
      (SignSequence.finite_mul (SignSequence.finite_pow D.y_finite 4)
        (SignSequence.finite_mul hcf hdf))
  have ha : D.triangle.sideA = (1 - D.x) * (1 + D.y ^ 2 * a + D.y ^ 4 * c) := by
    rw [hAe]
    dsimp only [a, c]
    field_simp [D.complement_pos.ne']
  have hb : D.triangle.sideB = D.x * (1 + D.y ^ 2 * b + D.y ^ 4 * d) := by
    rw [hBe]
    dsimp only [b, d]
    field_simp [D.x_pos.ne']
  have he : (1 + D.y ^ 2 * a + D.y ^ 4 * c) *
      (1 + D.y ^ 2 * b + D.y ^ 4 * d) =
      1 + D.y ^ 2 / 2 * (1 / D.x ^ 2 + 1 / (1 - D.x) ^ 2) + D.y ^ 4 * E := by
    dsimp only [E, a, b]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  refine ⟨E, hEf, ?_⟩
  rw [D.circumradius_eq, ha, hb, ← he]
  ring

/-- The actual inradius has the displayed negative quadratic correction and finite quartic tail. -/
theorem inradius_expansion (D : NormalizedFlatTriangle.{u}) :
    ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
      D.triangle.inradius = D.y / 2 *
        (1 - D.y ^ 2 / (4 * D.x * (1 - D.x)) + D.y ^ 4 * E) := by
  obtain ⟨F, hFf, hFe⟩ := D.slack_quadratic_expansion
  let c := 1 / (2 * D.x * (1 - D.x))
  have hcf : SignSequence.IsFinite c := by
    have he : c = (1 / 2) * D.x⁻¹ * (1 - D.x)⁻¹ := by
      dsimp only [c]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [he]
    exact SignSequence.finite_mul (SignSequence.finite_mul finite_half D.inv_x_finite)
      D.inv_complement_finite
  have htwo : SignSequence.standardPart (2 : SignSequence.{u}) ≠ 0 := by
    have he : SignSequence.standardPart (2 : SignSequence.{u}) = 2 := by
      simpa only [map_ofNat] using SignSequence.standardPart_ofReal (2 : ℝ)
    rw [he]
    norm_num
  obtain ⟨R, hRf, hRe⟩ := SignSequence.exists_finite_reciprocal_expansion 2 c F (D.y ^ 2)
    finite_two htwo hcf hFf ((SignSequence.infinitesimal_sq_iff _).mpr D.y_infinitesimal)
  have hd : D.triangle.sideA + D.triangle.sideB + 1 = 2 + D.y ^ 2 * c + (D.y ^ 2) ^ 2 * F := by
    dsimp only [c]
    linear_combination hFe
  refine ⟨2 * R, SignSequence.finite_mul finite_two hRf, ?_⟩
  rw [D.inradius_eq, hd, div_eq_mul_inv, hRe]
  dsimp only [c]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

end
end Surreal.Surcomplex.NormalizedFlatTriangle

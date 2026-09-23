import Surreal.Surcomplex.NormalizedFlatValuation
import Surreal.Surcomplex.TriangleAffine
import Surreal.Foundations.SignSequenceSqrtCubic

/-!
# A symmetric triangle of infinitesimal height

The actual triangle with vertices `0`, `1`, and `1/2 + i*ε` realizes
`trigonometry:ex:flat`. Its exact circumradius is infinite despite uniformly
bounded vertices, and its inradius has the displayed seventh-order finite tail.
-/

universe u

namespace Surreal.Surcomplex.SymmetricHeightTriangle

open Foundations

noncomputable section

variable (ε : SignSequence.{u}) (hp : 0 < ε) (hi : SignSequence.IsInfinitesimal ε)

private theorem finite_half : SignSequence.IsFinite ((1 : SignSequence.{u}) / 2) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)

private theorem standardPart_half : SignSequence.standardPart ((1 : SignSequence.{u}) / 2) =
    (1 / 2 : ℝ) := by
  simpa only [map_div₀, map_one, map_ofNat] using SignSequence.standardPart_ofReal (1 / 2 : ℝ)

/-- The symmetric family retains the positive infinitesimal height as an actual surreal. -/
def data : NormalizedFlatTriangle.{u} where
  x := 1 / 2
  y := ε
  x_finite := finite_half
  x_standardPart_mem := by rw [standardPart_half]; norm_num
  y_pos := hp
  y_infinitesimal := hi

/-- Its actual noncollinear triangle. -/
def triangle : Triangle.{u} := (data ε hp hi).triangle

@[simp] theorem vertexA : (triangle ε hp hi).A = 0 := rfl
@[simp] theorem vertexB : (triangle ε hp hi).B = 1 := rfl
@[simp] theorem vertexC : (triangle ε hp hi).C = ⟨1 / 2, ε⟩ := rfl

private theorem root_sq : SignSequence.sqrt (1 + 4 * ε ^ 2) ^ 2 = 1 + 4 * ε ^ 2 :=
  SignSequence.sqrt_sq (by positivity)

/-- The two equal sides are one half of the same positive square root. -/
theorem sideA : (triangle ε hp hi).sideA = SignSequence.sqrt (1 + 4 * ε ^ 2) / 2 := by
  rw [triangle, (data ε hp hi).sideA]
  change SignSequence.sqrt ((1 - 1 / 2) ^ 2 + ε ^ 2) = _
  apply SignSequence.sqrt_eq_of_nonneg_sq
    (div_nonneg (SignSequence.sqrt_nonneg _) (by norm_num))
  rw [div_pow, root_sq]
  ring

theorem sideB : (triangle ε hp hi).sideB = SignSequence.sqrt (1 + 4 * ε ^ 2) / 2 := by
  rw [triangle, (data ε hp hi).sideB]
  change SignSequence.sqrt ((1 / 2) ^ 2 + ε ^ 2) = _
  apply SignSequence.sqrt_eq_of_nonneg_sq
    (div_nonneg (SignSequence.sqrt_nonneg _) (by norm_num))
  rw [div_pow, root_sq]
  ring

@[simp] theorem sideC : (triangle ε hp hi).sideC = 1 := (data ε hp hi).sideC

/-- The two actual base angles have slope twice the height. -/
theorem angleA : (triangle ε hp hi).angleA = arctan (2 * ε) := by
  rw [triangle, (data ε hp hi).angleA]
  congr 1
  change ε / (1 / 2) = 2 * ε
  ring

theorem angleB : (triangle ε hp hi).angleB = arctan (2 * ε) := by
  rw [triangle, (data ε hp hi).angleB]
  congr 1
  change ε / (1 - 1 / 2) = 2 * ε
  ring

/-- The circumradius formula is exact, with no asymptotic remainder. -/
theorem circumradius : (triangle ε hp hi).circumradius = 1 / (8 * ε) + ε / 2 := by
  rw [show (triangle ε hp hi).circumradius =
    (triangle ε hp hi).sideA * (triangle ε hp hi).sideB / (2 * ε) from
      (data ε hp hi).circumradius_eq, sideA, sideB]
  have he : (SignSequence.sqrt (1 + 4 * ε ^ 2) / 2) *
      (SignSequence.sqrt (1 + 4 * ε ^ 2) / 2) = (1 + 4 * ε ^ 2) / 4 := by
    nlinarith only [root_sq ε]
  rw [he]
  field_simp [hp.ne']
  ring

/-- The inradius has the exact square-root denominator from the example. -/
theorem inradius : (triangle ε hp hi).inradius =
    ε / (1 + SignSequence.sqrt (1 + 4 * ε ^ 2)) := by
  rw [show (triangle ε hp hi).inradius =
    ε / ((triangle ε hp hi).sideA + (triangle ε hp hi).sideB + 1) from
      (data ε hp hi).inradius_eq, sideA, sideB]
  congr 1
  ring

/-- Rationalizing the inradius removes its appreciable denominator. -/
theorem inradius_rationalized : (triangle ε hp hi).inradius =
    (SignSequence.sqrt (1 + 4 * ε ^ 2) - 1) / (4 * ε) := by
  rw [inradius]
  have hn : 1 + SignSequence.sqrt (1 + 4 * ε ^ 2) ≠ 0 :=
    (add_pos_of_pos_of_nonneg zero_lt_one (SignSequence.sqrt_nonneg _)).ne'
  apply (div_eq_div_iff hn (mul_ne_zero (by norm_num) hp.ne')).mpr
  nlinarith only [root_sq ε]

/-- The inradius has the displayed cubic and quintic corrections with a finite seventh-order tail. -/
theorem inradius_expansion : ∃ E : SignSequence.{u}, SignSequence.IsFinite E ∧
    (triangle ε hp hi).inradius = ε / 2 - ε ^ 3 / 2 + ε ^ 5 + ε ^ 7 * E := by
  have hfour : SignSequence.IsFinite (4 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (4 : ℝ)
  have ht := SignSequence.finite_mul_infinitesimal hfour
    ((SignSequence.infinitesimal_sq_iff _).mpr hi)
  obtain ⟨E, hE, _, he⟩ := SignSequence.sqrt_one_add_cubic_expansion (4 * ε ^ 2) ht
  have hsixtyfour : SignSequence.IsFinite (64 : SignSequence.{u}) := by
    simpa only [map_ofNat] using SignSequence.finite_ofReal (64 : ℝ)
  refine ⟨64 * E, SignSequence.finite_mul hsixtyfour hE, ?_⟩
  rw [inradius_rationalized, he]
  field_simp [hp.ne']
  ring

/-- The circumradius is infinite, as its valuation equals that of the inverse height. -/
theorem circumradius_not_finite : ¬ SignSequence.IsFinite (triangle ε hp hi).circumradius := by
  have hn : ¬ SignSequence.IsFinite ε⁻¹ :=
    (SignSequence.infinitesimal_inv_iff_not_finite (inv_ne_zero hp.ne')).mp (by simpa using hi)
  have hv : SignSequence.valuation (triangle ε hp hi).circumradius =
      SignSequence.valuation ε⁻¹ := by
    rw [SignSequence.valuation_inv]
    exact (data ε hp hi).valuation_circumradius
  simpa only [SignSequence.isFinite_iff_valuation_nonneg, hv] using hn

/-- All three vertices lie in one fixed ordinary disk, independently of the infinitesimal height. -/
theorem vertices_bounded : modulus (triangle ε hp hi).A < 2 ∧
    modulus (triangle ε hp hi).B < 2 ∧ modulus (triangle ε hp hi).C < 2 := by
  have he : ε < 1 := by
    have h := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt ε).mp hi 1 zero_lt_one
    simpa only [map_one, abs_of_pos hp] using h
  refine ⟨?_, ?_, ?_⟩
  · rw [vertexA, modulus_zero]; norm_num
  · rw [vertexB, modulus_one]; norm_num
  · rw [vertexC]
    have h := modulus_le_abs_re_add_abs_im (⟨1 / 2, ε⟩ : Surcomplex.{u})
    change modulus (⟨1 / 2, ε⟩ : Surcomplex.{u}) ≤ |1 / 2| + |ε| at h
    rw [abs_of_pos (by norm_num : (0 : SignSequence.{u}) < 1 / 2), abs_of_pos hp] at h
    linarith

/-- The ordinary shadow of the upper vertex lies on the real base. -/
theorem standardPart_vertexC : standardPart (triangle ε hp hi).C = (1 / 2 : ℂ) := by
  apply Complex.ext
  · change SignSequence.standardPart (1 / 2 : SignSequence.{u}) = (1 / 2 : ℂ).re
    rw [standardPart_half]
    norm_num
  · change SignSequence.standardPart ε = (1 / 2 : ℂ).im
    rw [(SignSequence.standardPart_eq_zero_iff (SignSequence.finite_of_infinitesimal hi)).mpr hi]
    norm_num

/-- The standard-part vertices have zero oriented area although the actual triangle is noncollinear. -/
theorem standardPart_cross_zero :
    (standardPart (triangle ε hp hi).B - standardPart (triangle ε hp hi).A).re *
        (standardPart (triangle ε hp hi).C - standardPart (triangle ε hp hi).A).im -
      (standardPart (triangle ε hp hi).B - standardPart (triangle ε hp hi).A).im *
        (standardPart (triangle ε hp hi).C - standardPart (triangle ε hp hi).A).re = 0 := by
  have hzero : standardPart (0 : Surcomplex.{u}) = 0 :=
    Complex.ext SignSequence.standardPart_zero SignSequence.standardPart_zero
  have hone : standardPart (1 : Surcomplex.{u}) = 1 :=
    Complex.ext SignSequence.standardPart_one SignSequence.standardPart_zero
  rw [vertexA, vertexB, standardPart_vertexC, hzero, hone]
  norm_num

/-- The ordinary shadow is literally collinear in Mathlib's real affine plane. -/
theorem standardPart_collinear : Collinear ℝ
    ({standardPart (triangle ε hp hi).A, standardPart (triangle ε hp hi).B,
      standardPart (triangle ε hp hi).C} : Set ℂ) := by
  have hzero : standardPart (0 : Surcomplex.{u}) = 0 :=
    Complex.ext SignSequence.standardPart_zero SignSequence.standardPart_zero
  have hone : standardPart (1 : Surcomplex.{u}) = 1 :=
    Complex.ext SignSequence.standardPart_one SignSequence.standardPart_zero
  rw [vertexA, vertexB, standardPart_vertexC, hzero, hone]
  apply (collinear_iff_of_mem (by simp : (0 : ℂ) ∈ ({0, 1, 1 / 2} : Set ℂ))).mpr
  refine ⟨(1 : ℂ), ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨1 / 2, by norm_num [Complex.real_smul]⟩

/-- The actual triangle retains affine noncollinearity over the surreal field. -/
theorem not_collinear : ¬ Collinear SignSequence.{u}
    ({(triangle ε hp hi).A, (triangle ε hp hi).B, (triangle ε hp hi).C} : Set Surcomplex.{u}) :=
  (triangle ε hp hi).not_collinear

end
end Surreal.Surcomplex.SymmetricHeightTriangle

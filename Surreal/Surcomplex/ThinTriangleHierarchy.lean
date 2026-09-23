import Surreal.Surcomplex.ThinTriangle

/-!
# Thin triangles whose base angles have different scales

The second explicit family in `trigonometry:ex:hierarchies` has vertices
`0`, `1`, and `epsilon+i*epsilon^2`. Its two base angles are relatively
equivalent to epsilon and epsilon squared, while the radius formulas keep
their exact source constants.
-/

universe u

namespace Surreal.Surcomplex.ThinTriangleHierarchy

open Foundations

noncomputable section

variable (ε : SignSequence.{u}) (hp : 0 < ε) (hi : SignSequence.IsInfinitesimal ε)

include hp hi in
private theorem epsilon_lt_one : ε < 1 := by
  have h := (SignSequence.isInfinitesimal_iff_forall_real_abs_lt ε).mp hi 1 zero_lt_one
  simpa only [map_one, abs_of_pos hp] using h

include hi in
private theorem complement_finite : SignSequence.IsFinite (1 - ε) :=
  SignSequence.finite_sub SignSequence.finite_one (SignSequence.finite_of_infinitesimal hi)

include hi in
private theorem standardPart_complement : SignSequence.standardPart (1 - ε) = 1 := by
  rw [SignSequence.standardPart_sub SignSequence.finite_one (SignSequence.finite_of_infinitesimal hi),
    SignSequence.standardPart_one,
    (SignSequence.standardPart_eq_zero_iff (SignSequence.finite_of_infinitesimal hi)).mpr hi,
    sub_zero]

include hi in
private theorem inv_complement_finite : SignSequence.IsFinite (1 - ε)⁻¹ := by
  apply SignSequence.finite_inv_of_standardPart_ne_zero (complement_finite ε hi)
  rw [standardPart_complement ε hi]
  exact one_ne_zero

/-- The altitude epsilon squared is infinitesimal relative to both horizontal displacements. -/
def data : ThinTriangle.{u} where
  L := 1
  x := ε
  h := ε ^ 2
  x_pos := hp
  x_lt_base := epsilon_lt_one ε hp hi
  height_pos := sq_pos_of_pos hp
  slope_left_infinitesimal := by
    have he : ε ^ 2 / ε = ε := by field_simp
    rwa [he]
  slope_right_infinitesimal := by
    exact SignSequence.infinitesimal_mul_finite
      ((SignSequence.infinitesimal_sq_iff _).mpr hi) (inv_complement_finite ε hi)

/-- The actual coordinate triangle of the second hierarchy family. -/
def triangle : Triangle.{u} := (data ε hp hi).triangle

@[simp] theorem vertexA : (triangle ε hp hi).A = 0 := rfl
@[simp] theorem vertexB : (triangle ε hp hi).B = 1 := rfl
@[simp] theorem vertexC : (triangle ε hp hi).C = ⟨ε, ε ^ 2⟩ := rfl

/-- The first base angle has slope epsilon exactly. -/
theorem angleA : (triangle ε hp hi).angleA = arctan ε := by
  rw [triangle, (data ε hp hi).angleA]
  congr 1
  change ε ^ 2 / ε = ε
  field_simp

/-- The second base angle has the smaller, quadratic slope. -/
theorem angleB : (triangle ε hp hi).angleB = arctan (ε ^ 2 / (1 - ε)) :=
  (data ε hp hi).angleB

theorem area : (triangle ε hp hi).area = ε ^ 2 / 2 := by
  simpa only [triangle, data, one_mul] using (data ε hp hi).area

/-- The first base angle is relatively equivalent to epsilon. -/
theorem angleA_asymptotic : SignSequence.IsInfinitesimal
    ((triangle ε hp hi).angleA.val / ε - 1) := by
  rw [angleA]
  exact infinitesimal_arctanFunction_div_sub_one ε hi hp.ne'

/-- The second base angle is relatively equivalent to epsilon squared. -/
theorem angleB_asymptotic : SignSequence.IsInfinitesimal
    ((triangle ε hp hi).angleB.val / ε ^ 2 - 1) := by
  have hc : 0 < 1 - ε := sub_pos.mpr (epsilon_lt_one ε hp hi)
  have hs : SignSequence.IsInfinitesimal ((ε ^ 2 / (1 - ε)) / ε ^ 2 - 1) := by
    have he : (ε ^ 2 / (1 - ε)) / ε ^ 2 = (1 - ε)⁻¹ := by
      field_simp [hp.ne', hc.ne']
    rw [he]
    apply SignSequence.infinitesimal_inv_sub_one
    simpa only [sub_sub_cancel_left] using SignSequence.infinitesimal_neg hi
  exact SignSequence.infinitesimal_div_sub_one_trans (div_pos (sq_pos_of_pos hp) hc).ne'
    (data ε hp hi).angleB_asymptotic hs

/-- The two base-angle valuations are the first and second multiples of the height-parameter value. -/
theorem angle_valuations :
    SignSequence.valuation (triangle ε hp hi).angleA.val = SignSequence.valuation ε ∧
      SignSequence.valuation (triangle ε hp hi).angleB.val = 2 • SignSequence.valuation ε := by
  refine ⟨SignSequence.valuation_eq_of_infinitesimal_div_sub_one hp.ne'
    (angleA_asymptotic ε hp hi), ?_⟩
  rw [SignSequence.valuation_eq_of_infinitesimal_div_sub_one (pow_ne_zero 2 hp.ne')
    (angleB_asymptotic ε hp hi), SignSequence.valuation.map_pow]

theorem base_angles_infinitesimal :
    SignSequence.IsInfinitesimal (triangle ε hp hi).angleA.val ∧
      SignSequence.IsInfinitesimal (triangle ε hp hi).angleB.val :=
  ⟨(data ε hp hi).angleA_infinitesimal, (data ε hp hi).angleB_infinitesimal⟩

/-- The circumradius retains the source's reciprocal-epsilon scale and leading constant. -/
theorem circumradius_asymptotic : SignSequence.IsInfinitesimal
    ((triangle ε hp hi).circumradius / (1 / (2 * ε)) - 1) := by
  have hc : 0 < 1 - ε := sub_pos.mpr (epsilon_lt_one ε hp hi)
  have hmid : 0 < ε * (1 - ε) / (2 * ε ^ 2) := by positivity
  have hs : SignSequence.IsInfinitesimal
      ((ε * (1 - ε) / (2 * ε ^ 2)) / (1 / (2 * ε)) - 1) := by
    have he : (ε * (1 - ε) / (2 * ε ^ 2)) / (1 / (2 * ε)) - 1 = -ε := by
      field_simp [hp.ne']
      ring
    rw [he]
    exact SignSequence.infinitesimal_neg hi
  exact SignSequence.infinitesimal_div_sub_one_trans hmid.ne'
    (data ε hp hi).circumradius_asymptotic hs

/-- The inradius is relatively equivalent to one half of epsilon squared. -/
theorem inradius_asymptotic : SignSequence.IsInfinitesimal
    ((triangle ε hp hi).inradius / (ε ^ 2 / 2) - 1) := (data ε hp hi).inradius_asymptotic

/-- The inradius is infinitesimal. -/
theorem inradius_infinitesimal : SignSequence.IsInfinitesimal (triangle ε hp hi).inradius := by
  apply (SignSequence.infinitesimal_iff_of_infinitesimal_div_sub_one
    (div_ne_zero (pow_ne_zero 2 hp.ne') (by norm_num)) (inradius_asymptotic ε hp hi)).mpr
  have hf : SignSequence.IsFinite ((2 : SignSequence.{u})⁻¹) := by
    simpa only [map_inv₀, map_ofNat] using SignSequence.finite_ofReal ((2 : ℝ)⁻¹)
  exact SignSequence.infinitesimal_mul_finite ((SignSequence.infinitesimal_sq_iff _).mpr hi) hf

/-- The circumradius is infinite. -/
theorem circumradius_not_finite : ¬ SignSequence.IsFinite (triangle ε hp hi).circumradius := by
  have hn : 1 / (2 * ε) ≠ 0 := one_div_ne_zero (mul_ne_zero (by norm_num) hp.ne')
  have hscale : ¬ SignSequence.IsFinite (1 / (2 * ε)) := by
    apply (SignSequence.infinitesimal_inv_iff_not_finite hn).mp
    rw [inv_div, div_one]
    have hf : SignSequence.IsFinite (2 : SignSequence.{u}) := by
      simpa only [map_ofNat] using SignSequence.finite_ofReal (2 : ℝ)
    exact SignSequence.finite_mul_infinitesimal hf hi
  exact hscale ∘ (SignSequence.finite_iff_of_infinitesimal_div_sub_one hn
    (circumradius_asymptotic ε hp hi)).mp

end
end Surreal.Surcomplex.ThinTriangleHierarchy

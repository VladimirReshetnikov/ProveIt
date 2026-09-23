import Surreal.Surcomplex.TriangleFlatGap
import Surreal.Foundations.SignSequenceRelativeAsymptotics

/-!
# Relative flat-triangle asymptotics at arbitrary side scales

The three square-root equivalents in `trigonometry:eq:flatpreview` follow from
normalized squared identities. The relative gap is the only infinitesimality
hypothesis; the adjacent sides need not have comparable magnitudes. All lengths,
angles, areas and circumradii belong to the constructed actual surreal triangle.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- A relative infinitesimal gap is also infinitesimal relative to the adjacent-side sum. -/
theorem infinitesimal_sideGap_div_sum (T : Triangle.{u})
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal (T.sideGap / (T.sideB + T.sideC)) := by
  have hsum := add_pos T.sideB_pos T.sideC_pos
  have hkpos : 0 < T.sideB * T.sideC / (T.sideB + T.sideC) ^ 2 :=
    div_pos (mul_pos T.sideB_pos T.sideC_pos) (sq_pos_of_pos hsum)
  have hkbound : T.sideB * T.sideC / (T.sideB + T.sideC) ^ 2 ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos hsum)).mpr
    nlinarith only [sq_nonneg T.sideB, sq_nonneg T.sideC,
      mul_pos T.sideB_pos T.sideC_pos]
  have hkfinite : SignSequence.IsFinite (T.sideB * T.sideC / (T.sideB + T.sideC) ^ 2) := by
    apply (SignSequence.isFinite_iff_exists_nat_abs_le _).mpr
    exact ⟨1, by simpa only [Nat.cast_one, abs_of_pos hkpos] using hkbound⟩
  have he : T.sideGap / (T.sideB + T.sideC) =
      T.relativeGap * (T.sideB * T.sideC / (T.sideB + T.sideC) ^ 2) := by
    unfold relativeGap
    field_simp [T.sideB_pos.ne', T.sideC_pos.ne', hsum.ne']
  rw [he]
  exact SignSequence.infinitesimal_mul_finite hr hkfinite

/-- The longest side is relatively equivalent to the sum of the other two under flatness. -/
theorem infinitesimal_sideA_div_sum_sub_one (T : Triangle.{u})
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal (T.sideA / (T.sideB + T.sideC) - 1) := by
  have he : T.sideA / (T.sideB + T.sideC) - 1 =
      -(T.sideGap / (T.sideB + T.sideC)) := by
    unfold sideGap
    field_simp [(add_pos T.sideB_pos T.sideC_pos).ne']
    ring
  rw [he]
  exact SignSequence.infinitesimal_neg (T.infinitesimal_sideGap_div_sum hr)

private theorem infinitesimal_half_gap_correction (T : Triangle.{u})
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal (1 - T.sideGap / (2 * (T.sideB + T.sideC)) - 1) := by
  have hf : SignSequence.IsFinite ((1 : SignSequence.{u}) / 2) := by
    simpa only [map_div₀, map_one, map_ofNat] using SignSequence.finite_ofReal (1 / 2 : ℝ)
  have he : 1 - T.sideGap / (2 * (T.sideB + T.sideC)) - 1 =
      -(T.sideGap / (T.sideB + T.sideC) * (1 / 2)) := by
    field_simp
    ring
  rw [he]
  exact SignSequence.infinitesimal_neg
    (SignSequence.infinitesimal_mul_finite (T.infinitesimal_sideGap_div_sum hr) hf)

private theorem infinitesimal_flatParameter (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal T.flatParameter :=
  T.infinitesimal_angleSupplement_iff_flatParameter.mp
    ((T.infinitesimal_angleSupplement_iff_relativeGap hB hC).mpr hr)

private theorem infinitesimal_sqrt_normalization {x y : SignSequence.{u}}
    (hx : 0 ≤ x) (hy : 0 < y) (h : SignSequence.IsInfinitesimal (x ^ 2 / y - 1)) :
    SignSequence.IsInfinitesimal (x / SignSequence.sqrt y - 1) := by
  apply SignSequence.infinitesimal_sub_one_of_sq_sub_one
    (div_nonneg hx (SignSequence.sqrt_nonneg y))
  simpa only [div_pow, SignSequence.sqrt_sq hy.le] using h

/-- The angle supplement has the square-root equivalent in the relative flatness theorem. -/
theorem flat_supplement_asymptotic (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal
      (T.angleSupplement.val / SignSequence.sqrt
        (2 * (T.sideB + T.sideC) * T.sideGap / (T.sideB * T.sideC)) - 1) := by
  have hsum := add_pos T.sideB_pos T.sideC_pos
  have hq := T.infinitesimal_flatParameter hB hC hr
  have hs := SignSequence.infinitesimal_sqrt T.flatParameter_mem.1.le hq
  obtain ⟨F, hFf, hFs, hFe⟩ := arcsinFunction_leading_factor _ hs
  have hF : SignSequence.IsInfinitesimal (F - 1) :=
    SignSequence.infinitesimal_sub_one_iff.mpr ⟨hFf, hFs⟩
  have he : T.angleSupplement.val ^ 2 /
      (2 * (T.sideB + T.sideC) * T.sideGap / (T.sideB * T.sideC)) =
      (F * F) * (1 - T.sideGap / (2 * (T.sideB + T.sideC))) := by
    rw [T.angleSupplement_eq_two_arcsin_sqrt, hFe, mul_pow, mul_pow,
      SignSequence.sqrt_sq T.flatParameter_mem.1.le]
    unfold flatParameter
    field_simp [T.sideB_pos.ne', T.sideC_pos.ne', hsum.ne', T.sideGap_pos.ne']
    ring
  apply infinitesimal_sqrt_normalization T.angleSupplement_mem.1.le
    (div_pos (mul_pos (mul_pos (by norm_num) hsum) T.sideGap_pos)
      (mul_pos T.sideB_pos T.sideC_pos))
  rw [he]
  exact SignSequence.infinitesimal_mul_sub_one
    (SignSequence.infinitesimal_mul_sub_one hF hF) (T.infinitesimal_half_gap_correction hr)

/-- Heron's identity splits the normalized squared area into two explicit correction factors. -/
theorem flat_area_sq_ratio (T : Triangle.{u}) :
    T.area ^ 2 / (T.sideB * T.sideC * (T.sideB + T.sideC) * T.sideGap / 2) =
      (1 - T.sideGap / (2 * (T.sideB + T.sideC))) * (1 - T.flatParameter) := by
  rw [T.heron]
  unfold semiperimeter flatParameter sideGap
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne',
    (add_pos T.sideB_pos T.sideC_pos).ne',
    (show T.sideB + T.sideC - T.sideA ≠ 0 from T.sideGap_pos.ne')]
  ring

private theorem infinitesimal_flat_area_sq_ratio (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal
      (T.area ^ 2 / (T.sideB * T.sideC * (T.sideB + T.sideC) * T.sideGap / 2) - 1) := by
  have hq := T.infinitesimal_flatParameter hB hC hr
  have hc : SignSequence.IsInfinitesimal (1 - T.flatParameter - 1) := by
    simpa only [sub_sub_cancel_left] using SignSequence.infinitesimal_neg hq
  rw [T.flat_area_sq_ratio]
  exact SignSequence.infinitesimal_mul_sub_one (T.infinitesimal_half_gap_correction hr) hc

/-- The actual area has the square-root equivalent at every relative side scale. -/
theorem flat_area_asymptotic (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal
      (T.area / SignSequence.sqrt
        (T.sideB * T.sideC * (T.sideB + T.sideC) * T.sideGap / 2) - 1) := by
  apply infinitesimal_sqrt_normalization T.area_pos.le
    (div_pos (mul_pos (mul_pos (mul_pos T.sideB_pos T.sideC_pos)
      (add_pos T.sideB_pos T.sideC_pos)) T.sideGap_pos) (by norm_num))
  exact T.infinitesimal_flat_area_sq_ratio hB hC hr

/-- The exact circumradius square uses only the normalized longest side and area square. -/
theorem flat_circumradius_sq_ratio (T : Triangle.{u}) :
    T.circumradius ^ 2 / ((T.sideB + T.sideC) * T.sideB * T.sideC / (8 * T.sideGap)) =
      ((T.sideA / (T.sideB + T.sideC)) * (T.sideA / (T.sideB + T.sideC))) /
        (T.area ^ 2 / (T.sideB * T.sideC * (T.sideB + T.sideC) * T.sideGap / 2)) := by
  rw [T.circumradius_eq_side_product]
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne',
    (add_pos T.sideB_pos T.sideC_pos).ne', T.sideGap_pos.ne', T.area_pos.ne']
  ring

/-- The actual circumradius has the reciprocal-gap square-root equivalent. -/
theorem flat_circumradius_asymptotic (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA)
    (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    SignSequence.IsInfinitesimal
      (T.circumradius / SignSequence.sqrt
        ((T.sideB + T.sideC) * T.sideB * T.sideC / (8 * T.sideGap)) - 1) := by
  apply infinitesimal_sqrt_normalization T.circumradius_pos.le
    (div_pos (mul_pos (mul_pos (add_pos T.sideB_pos T.sideC_pos) T.sideB_pos) T.sideC_pos)
      (mul_pos (by norm_num) T.sideGap_pos))
  rw [T.flat_circumradius_sq_ratio]
  exact SignSequence.infinitesimal_div_sub_one
    (SignSequence.infinitesimal_mul_sub_one (T.infinitesimal_sideA_div_sum_sub_one hr)
      (T.infinitesimal_sideA_div_sum_sub_one hr))
    (T.infinitesimal_flat_area_sq_ratio hB hC hr)

end
end Surreal.Surcomplex.Triangle

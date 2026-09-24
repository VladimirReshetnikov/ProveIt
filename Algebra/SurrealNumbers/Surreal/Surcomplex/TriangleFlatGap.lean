import Surreal.Surcomplex.TriangleHeron
import Surreal.Surcomplex.ArcsinSeries
import Surreal.Foundations.SignSequenceSqrtInfinitesimal

/-!
# Exact triangle gaps and the relative flatness threshold

This proves the exact identity, inverse-sine formula and necessary-and-sufficient criterion in
`trigonometry:thm:flatrelative`, `trigonometry:eq:gapidentity` and
`trigonometry:eq:flatcriterion`. The sides, gap and comparison scale are arbitrary actual
surreals. The later strong-series, asymptotic and valuation conclusions are proved in
`TriangleFlatSeries.lean`, `TriangleFlatAsymptotics.lean` and `TriangleFlatValuation.lean`.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

noncomputable section

/-- The positive gap in the first strict triangle inequality. -/
def sideGap (T : Triangle.{u}) : SignSequence.{u} := T.sideB + T.sideC - T.sideA

/-- The supplement of the angle opposite the first side. -/
def angleSupplement (T : Triangle.{u}) : SignSequence.FiniteElement.{u} :=
  SignSequence.finiteOfReal Real.pi - T.angleA

/-- The exact squared half-sine parameter of the angle supplement. -/
def flatParameter (T : Triangle.{u}) : SignSequence.{u} :=
  T.sideGap * (2 * (T.sideB + T.sideC) - T.sideGap) / (4 * T.sideB * T.sideC)

/-- The gap relative to the harmonic scale of its two adjacent sides. -/
def relativeGap (T : Triangle.{u}) : SignSequence.{u} :=
  T.sideGap / (T.sideB * T.sideC / (T.sideB + T.sideC))

theorem sideGap_pos (T : Triangle.{u}) : 0 < T.sideGap := sub_pos.mpr T.sideA_lt_add

/-- If the first side is longest, its triangle gap is at most either adjacent side. -/
theorem sideGap_le_min (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) : T.sideGap ≤ min T.sideB T.sideC := by
  dsimp [sideGap]
  exact le_min (by linarith only [hC]) (by linarith only [hB])

@[simp] theorem val_angleSupplement (T : Triangle.{u}) :
    T.angleSupplement.val = SignSequence.ofReal Real.pi - T.angleA.val := rfl

theorem angleSupplement_mem (T : Triangle.{u}) :
    T.angleSupplement.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi) := by
  rw [val_angleSupplement]
  exact ⟨sub_pos.mpr T.angleA_mem.2, sub_lt_self _ T.angleA_mem.1⟩

theorem half_angleSupplement_mem (T : Triangle.{u}) :
    (finiteHalf T.angleSupplement).val ∈ Set.Ioo 0 (SignSequence.ofReal (Real.pi / 2)) := by
  rw [val_finiteHalf, map_div₀, map_ofNat]
  exact ⟨div_pos T.angleSupplement_mem.1 (by norm_num),
    div_lt_div_of_pos_right T.angleSupplement_mem.2 (by norm_num)⟩

private theorem half_angleSupplement_central_mem (T : Triangle.{u}) :
    (finiteHalf T.angleSupplement).val ∈ Set.Icc
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2)) := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal (Real.pi / 2) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono (half_pos Real.pi_pos)
  rw [map_neg]
  exact ⟨by linarith [T.half_angleSupplement_mem.1], T.half_angleSupplement_mem.2.le⟩

theorem sin_half_angleSupplement_pos (T : Triangle.{u}) :
    0 < finiteSin (finiteHalf T.angleSupplement) := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hi := T.half_angleSupplement_mem
  rw [map_div₀, map_ofNat] at hi
  exact finiteSin_pos_of_mem_Ioo _ ⟨hi.1, by linarith [hi.2]⟩

/-- The supplement cosine is the negative of the original angle cosine. -/
theorem cos_angleSupplement (T : Triangle.{u}) :
    finiteCos T.angleSupplement = -finiteCos T.angleA := by
  simp only [angleSupplement, finiteCos_sub, finiteSin_constant, finiteCos_constant,
    Real.sin_pi, Real.cos_pi, map_neg, map_one, map_zero, zero_mul, add_zero, neg_one_mul]

/-- The exact gap identity, without any scale or longest-side restriction. -/
theorem flat_gap_identity (T : Triangle.{u}) :
    4 * T.sideB * T.sideC * finiteSin (finiteHalf T.angleSupplement) ^ 2 =
      T.sideGap * (2 * (T.sideB + T.sideC) - T.sideGap) := by
  have hs := finiteSin_finiteHalf_sq T.angleSupplement
  rw [T.cos_angleSupplement] at hs
  dsimp [sideGap]
  linear_combination 4 * T.sideB * T.sideC * hs + T.cosine_law

/-- The rational gap parameter is exactly the squared actual half-sine. -/
theorem flatParameter_eq_sin_half_sq (T : Triangle.{u}) :
    T.flatParameter = finiteSin (finiteHalf T.angleSupplement) ^ 2 := by
  unfold flatParameter
  apply (div_eq_iff (mul_ne_zero (mul_ne_zero (by norm_num) T.sideB_pos.ne')
    T.sideC_pos.ne')).mpr
  linear_combination -T.flat_gap_identity

/-- The inverse-sine argument remains strictly inside its actual domain. -/
theorem flatParameter_mem (T : Triangle.{u}) : T.flatParameter ∈ Set.Ioo 0 1 := by
  rw [T.flatParameter_eq_sin_half_sq]
  refine ⟨sq_pos_of_pos T.sin_half_angleSupplement_pos, ?_⟩
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal (Real.pi / 2) := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono (half_pos Real.pi_pos)
  have hc : 0 < finiteCos (finiteHalf T.angleSupplement) := by
    apply finiteCos_pos_of_mem_Ioo
    rw [map_neg]
    exact ⟨by linarith [T.half_angleSupplement_mem.1], T.half_angleSupplement_mem.2⟩
  nlinarith only [finiteCos_sq_add_finiteSin_sq (finiteHalf T.angleSupplement), sq_pos_of_pos hc]

/-- Positivity selects the half-sine as the square root of the gap parameter. -/
theorem sqrt_flatParameter (T : Triangle.{u}) :
    SignSequence.sqrt T.flatParameter = finiteSin (finiteHalf T.angleSupplement) :=
  SignSequence.sqrt_eq_of_nonneg_sq T.sin_half_angleSupplement_pos.le
    T.flatParameter_eq_sin_half_sq.symm

/-- The exact supplement is twice inverse sine of the square root of its gap parameter. -/
theorem angleSupplement_eq_two_arcsin_sqrt (T : Triangle.{u}) :
    T.angleSupplement.val = 2 * arcsinFunction (SignSequence.sqrt T.flatParameter) := by
  have hi : arcsinFunction (finiteSin (finiteHalf T.angleSupplement)) =
      (finiteHalf T.angleSupplement).val := by
    rw [arcsinFunction_eq ⟨finiteSin (finiteHalf T.angleSupplement), finiteSin_mem_Icc _⟩,
      arcsin_finiteSin _ T.half_angleSupplement_central_mem]
  rw [T.sqrt_flatParameter, hi, val_finiteHalf]
  ring

theorem relativeGap_pos (T : Triangle.{u}) : 0 < T.relativeGap :=
  div_pos T.sideGap_pos (div_pos (mul_pos T.sideB_pos T.sideC_pos)
    (add_pos T.sideB_pos T.sideC_pos))

/-- The source's correction factor lies between three halves and two for a longest side. -/
theorem flat_gap_factor_bounds (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) :
    (3 : SignSequence.{u}) / 2 ≤ 2 - T.sideGap / (T.sideB + T.sideC) ∧
      2 - T.sideGap / (T.sideB + T.sideC) < 2 := by
  have hsum := add_pos T.sideB_pos T.sideC_pos
  have hgB := (T.sideGap_le_min hB hC).trans (min_le_left _ _)
  have hgC := (T.sideGap_le_min hB hC).trans (min_le_right _ _)
  have hhalf : T.sideGap / (T.sideB + T.sideC) ≤ 1 / 2 := by
    apply (div_le_iff₀ hsum).mpr
    linarith only [hgB, hgC]
  have hpos := div_pos T.sideGap_pos hsum
  constructor <;> linarith only [hhalf, hpos]

/-- The gap parameter is the relative gap times its bounded correction factor. -/
theorem flatParameter_eq_relativeGap_mul (T : Triangle.{u}) :
    T.flatParameter = T.relativeGap * (2 - T.sideGap / (T.sideB + T.sideC)) / 4 := by
  unfold flatParameter relativeGap
  field_simp [T.sideB_pos.ne', T.sideC_pos.ne', (add_pos T.sideB_pos T.sideC_pos).ne']

/-- Ordinary-factor comparisons characterize relative flatness even for unequal side scales. -/
theorem flatParameter_relativeGap_bounds (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA) :
    T.flatParameter ≤ T.relativeGap ∧ T.relativeGap ≤ 4 * T.flatParameter := by
  have hb := T.flat_gap_factor_bounds hB hC
  have hlo := mul_le_mul_of_nonneg_left hb.1 T.relativeGap_pos.le
  have hhi := mul_le_mul_of_nonneg_left hb.2.le T.relativeGap_pos.le
  rw [T.flatParameter_eq_relativeGap_mul]
  constructor <;> nlinarith only [hlo, hhi, T.relativeGap_pos]

/-- A supplement is infinitesimal exactly when its squared half-sine parameter is. -/
theorem infinitesimal_angleSupplement_iff_flatParameter (T : Triangle.{u}) :
    SignSequence.IsInfinitesimal T.angleSupplement.val ↔
      SignSequence.IsInfinitesimal T.flatParameter := by
  constructor
  · intro hh
    apply SignSequence.infinitesimal_of_abs_le (y := T.angleSupplement.val) _ hh
    rw [abs_of_pos T.flatParameter_mem.1, abs_of_pos T.angleSupplement_mem.1,
      T.flatParameter_eq_sin_half_sq]
    have hj := (finiteSin_jordan (finiteHalf T.angleSupplement)
      ⟨T.half_angleSupplement_mem.1.le, T.half_angleSupplement_mem.2.le⟩).2
    rw [val_finiteHalf] at hj
    have hs := mul_nonneg T.sin_half_angleSupplement_pos.le
      (sub_nonneg.mpr (finiteSin_mem_Icc (finiteHalf T.angleSupplement)).2)
    nlinarith only [hj, hs, T.angleSupplement_mem.1]
  · intro hq
    have hs := SignSequence.infinitesimal_sqrt T.flatParameter_mem.1.le hq
    have ha := infinitesimal_arcsinFunction (SignSequence.sqrt T.flatParameter) hs
    rw [T.angleSupplement_eq_two_arcsin_sqrt, two_mul]
    exact SignSequence.infinitesimal_add ha ha

/-- Flatness is equivalent to gap infinitesimality relative to the harmonic adjacent-side scale. -/
theorem infinitesimal_angleSupplement_iff_relativeGap (T : Triangle.{u})
    (hB : T.sideB ≤ T.sideA) (hC : T.sideC ≤ T.sideA) :
    SignSequence.IsInfinitesimal T.angleSupplement.val ↔
      SignSequence.IsInfinitesimal T.relativeGap := by
  rw [T.infinitesimal_angleSupplement_iff_flatParameter]
  have hb := T.flatParameter_relativeGap_bounds hB hC
  constructor
  · intro hq
    have h2 := SignSequence.infinitesimal_add hq hq
    have h4 := SignSequence.infinitesimal_add h2 h2
    rw [show T.flatParameter + T.flatParameter + (T.flatParameter + T.flatParameter) =
      4 * T.flatParameter by ring] at h4
    apply SignSequence.infinitesimal_of_abs_le (y := 4 * T.flatParameter) _ h4
    rw [abs_of_pos T.relativeGap_pos, abs_of_pos (mul_pos (by norm_num) T.flatParameter_mem.1)]
    exact hb.2
  · intro hr
    apply SignSequence.infinitesimal_of_abs_le (y := T.relativeGap) _ hr
    rw [abs_of_pos T.flatParameter_mem.1, abs_of_pos T.relativeGap_pos]
    exact hb.1

end
end Surreal.Surcomplex.Triangle

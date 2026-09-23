import Surreal.Surcomplex.TriangleFlatAsymptotics

/-!
# Exact valuation scales of relative flat triangles

The positive square-root equivalents give the three finite half-valuation
formulas in `trigonometry:eq:flatvaluations`. Both their explicit actual
surreal exponents and their intrinsic doubled valuation identities are
recorded, with no infinite-value subtraction at these positive inputs.
-/

universe u

namespace Surreal.Surcomplex.Triangle

open Foundations

local notation "v" => SignSequence.valuation
local notation "L" => SignSequence.leadingExponent

private theorem leadingExponent_two : L (2 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using SignSequence.leadingExponent_ofReal (2 : ℝ)

private theorem leadingExponent_eight : L (8 : SignSequence.{u}) = 0 := by
  simpa only [map_ofNat] using SignSequence.leadingExponent_ofReal (8 : ℝ)

private theorem coe_sub_valuation (a b : SignSequence.{u}) :
    ((a - b : SignSequence.{u}) : WithTop SignSequence.{u}) =
      (a : WithTop SignSequence.{u}) - (b : WithTop SignSequence.{u}) := rfl

/-- The supplement valuation is half the gap-plus-sum valuation minus the adjacent-side valuations. -/
theorem flat_valuation_supplement (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    v T.angleSupplement.val =
      (((-L T.sideGap - L (T.sideB + T.sideC) + L T.sideB + L T.sideC) / 2 :
        SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have hb := T.sideB_pos
  have hc := T.sideC_pos
  have hg := T.sideGap_pos
  have hs := add_pos hb hc
  have hx : 0 < 2 * (T.sideB + T.sideC) * T.sideGap / (T.sideB * T.sideC) := by positivity
  have he := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (SignSequence.sqrt_pos hx).ne' (T.flat_supplement_asymptotic hB hC hr)
  rw [he, SignSequence.valuation_sqrt hx,
    SignSequence.leadingExponent_div
      (mul_ne_zero (mul_ne_zero (by norm_num) hs.ne') hg.ne') (mul_ne_zero hb.ne' hc.ne'),
    SignSequence.leadingExponent_mul (mul_ne_zero (by norm_num) hs.ne') hg.ne',
    SignSequence.leadingExponent_mul (by norm_num : (2 : SignSequence.{u}) ≠ 0) hs.ne',
    SignSequence.leadingExponent_mul hb.ne' hc.ne', leadingExponent_two]
  congr 1
  ring

/-- The area valuation is half the sum of the gap, side-sum and both adjacent-side valuations. -/
theorem flat_valuation_area (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    v T.area =
      (((-L T.sideGap - L (T.sideB + T.sideC) - L T.sideB - L T.sideC) / 2 :
        SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have hb := T.sideB_pos
  have hc := T.sideC_pos
  have hg := T.sideGap_pos
  have hs := add_pos hb hc
  have hx : 0 < T.sideB * T.sideC * (T.sideB + T.sideC) * T.sideGap / 2 := by positivity
  have he := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (SignSequence.sqrt_pos hx).ne' (T.flat_area_asymptotic hB hC hr)
  rw [he, SignSequence.valuation_sqrt hx,
    SignSequence.leadingExponent_div
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hb.ne' hc.ne') hs.ne') hg.ne')
      (by norm_num : (2 : SignSequence.{u}) ≠ 0),
    SignSequence.leadingExponent_mul (mul_ne_zero (mul_ne_zero hb.ne' hc.ne') hs.ne') hg.ne',
    SignSequence.leadingExponent_mul (mul_ne_zero hb.ne' hc.ne') hs.ne',
    SignSequence.leadingExponent_mul hb.ne' hc.ne', leadingExponent_two]
  congr 1
  ring

/-- The circumradius valuation has the reciprocal square-root dependence on the side gap. -/
theorem flat_valuation_circumradius (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    v T.circumradius =
      (((-L (T.sideB + T.sideC) - L T.sideB - L T.sideC + L T.sideGap) / 2 :
        SignSequence.{u}) : WithTop SignSequence.{u}) := by
  have hb := T.sideB_pos
  have hc := T.sideC_pos
  have hg := T.sideGap_pos
  have hs := add_pos hb hc
  have hx : 0 < (T.sideB + T.sideC) * T.sideB * T.sideC / (8 * T.sideGap) := by positivity
  have he := SignSequence.valuation_eq_of_infinitesimal_div_sub_one
    (SignSequence.sqrt_pos hx).ne' (T.flat_circumradius_asymptotic hB hC hr)
  rw [he, SignSequence.valuation_sqrt hx,
    SignSequence.leadingExponent_div (mul_ne_zero (mul_ne_zero hs.ne' hb.ne') hc.ne')
      (mul_ne_zero (by norm_num) hg.ne'),
    SignSequence.leadingExponent_mul (mul_ne_zero hs.ne' hb.ne') hc.ne',
    SignSequence.leadingExponent_mul hs.ne' hb.ne',
    SignSequence.leadingExponent_mul (by norm_num : (8 : SignSequence.{u}) ≠ 0) hg.ne',
    leadingExponent_eight]
  congr 1
  ring

/-- The supplement's half-valuation formula in intrinsic additive-valuation notation. -/
theorem flat_two_nsmul_valuation_supplement (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    2 • v T.angleSupplement.val =
      v T.sideGap + v (T.sideB + T.sideC) - v T.sideB - v T.sideC := by
  rw [T.flat_valuation_supplement hB hC hr,
    SignSequence.valuation_of_ne_zero T.sideGap_pos.ne',
    SignSequence.valuation_of_ne_zero (add_pos T.sideB_pos T.sideC_pos).ne',
    SignSequence.valuation_of_ne_zero T.sideB_pos.ne',
    SignSequence.valuation_of_ne_zero T.sideC_pos.ne', ← WithTop.coe_nsmul,
    ← WithTop.coe_add, ← coe_sub_valuation, ← coe_sub_valuation]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- The area half-valuation formula in intrinsic additive-valuation notation. -/
theorem flat_two_nsmul_valuation_area (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    2 • v T.area =
      v T.sideGap + v (T.sideB + T.sideC) + v T.sideB + v T.sideC := by
  rw [T.flat_valuation_area hB hC hr,
    SignSequence.valuation_of_ne_zero T.sideGap_pos.ne',
    SignSequence.valuation_of_ne_zero (add_pos T.sideB_pos T.sideC_pos).ne',
    SignSequence.valuation_of_ne_zero T.sideB_pos.ne',
    SignSequence.valuation_of_ne_zero T.sideC_pos.ne', ← WithTop.coe_nsmul,
    ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- The circumradius half-valuation formula in intrinsic additive-valuation notation. -/
theorem flat_two_nsmul_valuation_circumradius (T : Triangle.{u}) (hB : T.sideB ≤ T.sideA)
    (hC : T.sideC ≤ T.sideA) (hr : SignSequence.IsInfinitesimal T.relativeGap) :
    2 • v T.circumradius =
      v (T.sideB + T.sideC) + v T.sideB + v T.sideC - v T.sideGap := by
  rw [T.flat_valuation_circumradius hB hC hr,
    SignSequence.valuation_of_ne_zero T.sideGap_pos.ne',
    SignSequence.valuation_of_ne_zero (add_pos T.sideB_pos T.sideC_pos).ne',
    SignSequence.valuation_of_ne_zero T.sideB_pos.ne',
    SignSequence.valuation_of_ne_zero T.sideC_pos.ne', ← WithTop.coe_nsmul,
    ← WithTop.coe_add, ← WithTop.coe_add, ← coe_sub_valuation]
  congr 1
  simp only [nsmul_eq_mul]
  ring

end Surreal.Surcomplex.Triangle

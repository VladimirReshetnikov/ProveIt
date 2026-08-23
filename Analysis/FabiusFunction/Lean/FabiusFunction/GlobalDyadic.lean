import FabiusFunction.DyadicAnalytic
import FabiusFunction.GlobalExtension

/-!
# Analytic correctness of the signed dyadic evaluators

The global evaluator reduces a positive input modulo a length-two block,
folds the residue into the unit interval, and applies the appropriate
Thue–Morse sign.  Local finiteness of `extendedFabius` shows that this is
exactly the one translate which contributes to its defining series.
-/

open scoped BigOperators ContDiff Interval
open Finset MeasureTheory Set

namespace Fabius

set_option autoImplicit false

/-- The total signed-numerator evaluator computes the signed global extension. -/
theorem extendedFabiusDyadicValue_cast (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) (a : ℤ) :
    (extendedFabiusDyadicValue n a : ℝ) =
      extendedFabius F ((a : ℝ) / (2 : ℝ) ^ n) := by
  by_cases ha : a ≤ 0
  · rw [extendedFabiusDyadicValue_of_nonpos n a ha]
    norm_num
    exact (extendedFabius_eq_zero_of_nonpos F hF
      (div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast ha) (by positivity))).symm
  · have hapos : 0 < a := lt_of_not_ge ha
    have hatoNat : (a.toNat : ℤ) = a := Int.toNat_of_nonneg hapos.le
    let scale : ℕ := 2 ^ n
    let period : ℕ := 2 * scale
    let naturalNumerator : ℕ := a.toNat
    let block : ℕ := naturalNumerator / period
    let residue : ℕ := naturalNumerator % period
    let coreNumerator : ℕ :=
      if residue ≤ scale then residue else period - residue
    have hscalePos : 0 < scale := by simp [scale]
    have hperiodPos : 0 < period := by simp [period, hscalePos]
    have hresidueLt : residue < period := Nat.mod_lt _ hperiodPos
    have hdecomp : naturalNumerator = period * block + residue :=
      (Nat.div_add_mod naturalNumerator period).symm
    have hx : ((a : ℝ) / (2 : ℝ) ^ n) =
        2 * (block : ℝ) + (residue : ℝ) / (scale : ℝ) := by
      have hnat : (a.toNat : ℕ) = period * block + residue := hdecomp
      rw [← hatoNat]
      push_cast
      dsimp only [scale, period] at hnat ⊢
      rw [show (a.toNat : ℝ) =
          ((2 * 2 ^ n) * block + residue : ℕ) by exact_mod_cast hnat]
      push_cast
      field_simp
    have hxLower : 2 * (block : ℝ) ≤ (a : ℝ) / (2 : ℝ) ^ n := by
      rw [hx]
      exact le_add_of_nonneg_right (div_nonneg (by positivity) (by positivity))
    have hxUpper : (a : ℝ) / (2 : ℝ) ^ n ≤
        2 * (block : ℝ) + 2 := by
      rw [hx]
      have hrle : (residue : ℝ) ≤ period := by exact_mod_cast hresidueLt.le
      have hspos : (0 : ℝ) < scale := by exact_mod_cast hscalePos
      dsimp only [period] at hrle
      have hfrac : (residue : ℝ) / (scale : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hspos]
        push_cast at hrle
        exact hrle
      linarith
    have hsingle := extendedFabius_eq_single_translate F hF block hxLower hxUpper
    have harg : (a : ℝ) / (2 : ℝ) ^ n - 2 * (block : ℝ) - 1 =
        (residue : ℝ) / (scale : ℝ) - 1 := by
      rw [hx]
      ring
    rw [harg] at hsingle
    have hcoreLe : coreNumerator ≤ scale := by
      dsimp only [coreNumerator]
      split
      · assumption
      · rename_i hres
        dsimp only [period]
        omega
    have hunit : (fabiusDyadicUnit n coreNumerator : ℝ) =
        fabiusReal F ((coreNumerator : ℝ) / (scale : ℝ)) := by
      rw [fabiusDyadicUnit_eq_fabiusDyadic n coreNumerator hcoreLe,
        fabiusDyadic_cast F hF n coreNumerator]
      · norm_num [scale]
      · simpa only [scale] using hcoreLe
    rw [extendedFabiusDyadicValue, if_neg ha]
    dsimp only
    change (((thueMorseSign block : ℚ) * fabiusDyadicUnit n coreNumerator : ℚ) : ℝ) = _
    rw [hsingle]
    push_cast
    rw [hunit]
    have hsign : (thueMorseSign block : ℝ) =
        (-1 : ℝ) ^ binaryWeight block := by
      norm_num [thueMorseSign]
    rw [hsign]
    congr 1
    dsimp only [coreNumerator]
    split
    · rename_i hres
      have hargNonpos : (residue : ℝ) / (scale : ℝ) - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_one (by exact_mod_cast hscalePos)]
        exact_mod_cast hres
      rw [rvachevUp, if_pos hargNonpos]
      congr 1
      ring
    · rename_i hres
      have hargPos : 0 < (residue : ℝ) / (scale : ℝ) - 1 := by
        rw [sub_pos, one_lt_div (by exact_mod_cast hscalePos)]
        exact_mod_cast (lt_of_not_ge hres)
      rw [rvachevUp, if_neg (not_le.mpr hargPos)]
      congr 1
      have hperiod : (period : ℝ) = 2 * (scale : ℝ) := by
        norm_num [period]
      rw [Nat.cast_sub hresidueLt.le, hperiod]
      field_simp
      ring

/-- The exact integer-numerator dyadic evaluator agrees with Rvachev's function. -/
theorem rvachevDyadic_cast (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) (a : ℤ) (ha : a.natAbs ≤ 2 ^ n) :
    (rvachevDyadic n a : ℝ) = rvachevUp F (a / (2 : ℝ) ^ n) := by
  rw [rvachevDyadic, if_pos ha, Rat.cast_abs,
    fabiusDyadic_cast F hF n (2 ^ n - a.natAbs) (by omega),
    abs_of_nonneg (fabiusReal_nonneg F _)]
  by_cases ha0 : a ≤ 0
  · rw [rvachevUp, if_pos (div_nonpos_of_nonpos_of_nonneg
        (by exact_mod_cast ha0) (by positivity))]
    congr 1
    have habs : (a.natAbs : ℤ) = -a := by
      simpa only [Int.natAbs_neg] using
        (Int.natAbs_of_nonneg (a := -a) (neg_nonneg.mpr ha0))
    rw [Nat.cast_sub ha]
    push_cast
    field_simp
    norm_cast
    omega
  · have ha0' : 0 ≤ a := (lt_of_not_ge ha0).le
    rw [rvachevUp, if_neg (not_le.mpr (div_pos (by exact_mod_cast lt_of_not_ge ha0)
      (by positivity)))]
    congr 1
    have habs : (a.natAbs : ℤ) = a := Int.natAbs_of_nonneg ha0'
    rw [Nat.cast_sub ha]
    push_cast
    field_simp
    norm_cast
    omega

end Fabius

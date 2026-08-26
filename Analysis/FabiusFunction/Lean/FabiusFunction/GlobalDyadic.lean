import FabiusFunction.DyadicAnalytic
import FabiusFunction.Existence
import FabiusFunction.GlobalExtension

/-!
# Analytic correctness of the signed dyadic evaluators

The global evaluator reduces a positive input modulo a length-two block,
folds the residue into the unit interval, and applies the appropriate
Thue–Morse sign.  Local finiteness of `extendedFabius` shows that this is
exactly the one translate which contributes to its defining series.  As a
consequence, the natural-numerator closed formula is independent of the
chosen dyadic presentation; convenient one-step and iterated refinement
forms are recorded below.  The signed integer-numerator evaluator is also
identified with Rvachev's function on the whole dyadic grid, including points
outside the compact support where both sides vanish.  Finally, an exact
rational-input wrapper recognizes precisely the dyadic rationals and returns
the corresponding analytic Rvachev value.
-/

open scoped BigOperators ContDiff Interval
open Finset MeasureTheory Set

namespace Fabius

set_option autoImplicit false

/-! ## The closed formula on the first signed block -/

/-- Across the leading dyadic block, the two closed-form values add to one.
This includes the right endpoint `r = 2^n`, where the value at `2` vanishes. -/
theorem fabiusDyadic_add_pow_eq_one (n r : ℕ) (hr : r ≤ 2 ^ n) :
    fabiusDyadic n (2 ^ n + r) + fabiusDyadic n r = 1 := by
  rw [fabiusDyadic_add_remainder_eq_block n n r hr]
  have hblock := dyadicBlock_eq_taylor_sum n n le_rfl (r : ℚ)
  convert hblock using 1
  · congr 1
    apply Finset.sum_congr rfl
    intro h hh
    congr 2
    ring
  · simp [fabiusAtInverseTwoPow_eq_halfMoment, halfMomentFabiusValue]

/-- On `[0,1]`, the second half of the signed extension is the reflected
bounded Fabius function. -/
theorem extendedFabius_one_add (F : BoundedFabius) (hF : IsFabius F)
    {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    extendedFabius F (1 + y) = 1 - fabiusReal F y := by
  have hyhi : y ≤ 1 := hy.2
  have hext : extendedFabius F (1 + y) = rvachevUp F y := by
    have h := extendedFabius_add_one_eq_rvachevUp F hF hyhi
    rw [show y + 1 = 1 + y by ring] at h
    exact h
  rw [hext]
  by_cases hy0 : y ≤ 0
  · have : y = 0 := le_antisymm hy0 hy.1
    subst y
    simp [rvachevUp, hF.one_of_one_le, hF.zero_of_nonpos]
  · rw [rvachevUp, if_neg hy0, hF.symmetry y hy]

/-- Equation (32) on its full `[0,2]` range, using the signed extension. -/
theorem fabiusDyadic_cast_extended_formula
    (F : BoundedFabius) (hF : IsFabius F)
    (n a : ℕ) (ha : a ≤ 2 ^ (n + 1)) :
    (fabiusDyadic n a : ℝ) =
      extendedFabius F (a / (2 : ℝ) ^ n) := by
  by_cases hunit : a ≤ 2 ^ n
  · rw [fabiusDyadic_cast F hF n a hunit]
    apply (extendedFabius_eq_fabiusReal F hF ?_).symm
    constructor
    · positivity
    · apply (div_le_one (by positivity)).2
      exact_mod_cast hunit
  · have hpowle : 2 ^ n ≤ a := (Nat.lt_of_not_ge hunit).le
    let r := a - 2 ^ n
    have haeq : a = 2 ^ n + r := by
      dsimp only [r]
      omega
    have hr : r ≤ 2 ^ n := by
      dsimp only [r]
      rw [pow_succ] at ha
      omega
    have hreflect := fabiusDyadic_add_pow_eq_one n r hr
    have hreflectCast := congrArg (fun q : ℚ => (q : ℝ)) hreflect
    push_cast at hreflectCast
    have hrCast := fabiusDyadic_cast F hF n r hr
    have hry : (r : ℝ) / (2 : ℝ) ^ n ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · positivity
      · apply (div_le_one (by positivity)).2
        exact_mod_cast hr
    have harg : (a : ℝ) / (2 : ℝ) ^ n =
        1 + (r : ℝ) / (2 : ℝ) ^ n := by
      rw [haeq]
      push_cast
      field_simp
    rw [harg, extendedFabius_one_add F hF hry, ← hrCast]
    rw [haeq]
    linarith

/-- Reflection of the closed dyadic formula across the midpoint of its unit
grid. The statement is exact and independent of the chosen analytic model. -/
theorem fabiusDyadic_unit_reflection (n r : ℕ) (hr : r ≤ 2 ^ n) :
    fabiusDyadic n (2 ^ n - r) = 1 - fabiusDyadic n r := by
  obtain ⟨F, hF, _hunique⟩ := existsUnique_fabius
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [fabiusDyadic_cast F hF n (2 ^ n - r) (by omega),
    fabiusDyadic_cast F hF n r hr]
  have harg : ((2 ^ n - r : ℕ) : ℝ) / (2 : ℝ) ^ n =
      1 - (r : ℝ) / (2 : ℝ) ^ n := by
    rw [Nat.cast_sub hr]
    push_cast
    field_simp
  rw [harg]
  apply hF.symmetry
  constructor
  · positivity
  · apply (div_le_one (by positivity)).2
    exact_mod_cast hr

private theorem fabiusDyadic_first_block_eq_fold
    (n residue : ℕ) (hresidue : residue < 2 ^ (n + 1)) :
    fabiusDyadic n residue =
      let scale := 2 ^ n
      let period := 2 * scale
      let core := if residue ≤ scale then residue else period - residue
      fabiusDyadicUnit n core := by
  let scale : ℕ := 2 ^ n
  let period : ℕ := 2 * scale
  let core : ℕ := if residue ≤ scale then residue else period - residue
  change fabiusDyadic n residue = fabiusDyadicUnit n core
  have hperiod : period = 2 ^ (n + 1) := by
    simp only [period, scale, pow_succ]
    omega
  have hresidue' : residue < period := by simpa only [hperiod] using hresidue
  by_cases hfirst : residue ≤ scale
  · have hcore : core = residue := by simp [core, hfirst]
    rw [hcore, fabiusDyadicUnit_eq_fabiusDyadic n residue]
    simpa only [scale] using hfirst
  · let offset := residue - scale
    have hscaleLe : scale ≤ residue := (Nat.lt_of_not_ge hfirst).le
    have hresidueEq : residue = scale + offset := by
      dsimp only [offset]
      omega
    have hoffsetLe : offset ≤ scale := by
      dsimp only [offset]
      dsimp only [period] at hresidue'
      omega
    have hcoreEq : core = scale - offset := by
      dsimp only [core]
      rw [if_neg hfirst]
      dsimp only [period, offset]
      omega
    have hadd := fabiusDyadic_add_pow_eq_one n offset
      (by simpa only [scale] using hoffsetLe)
    have hsym := fabiusDyadic_unit_reflection n offset
      (by simpa only [scale] using hoffsetLe)
    rw [hcoreEq, fabiusDyadicUnit_eq_fabiusDyadic n (scale - offset)]
    · rw [hresidueEq]
      dsimp only [scale] at hadd hsym ⊢
      linarith
    · exact Nat.sub_le _ _

/-- Equation (32), evaluated at any natural numerator, is exactly the total
rational evaluator for the signed global Fabius extension. -/
theorem fabiusDyadic_eq_extendedFabiusDyadicValue_nat
    (n m : ℕ) :
    fabiusDyadic n m = extendedFabiusDyadicValue n (m : ℤ) := by
  by_cases hm : m = 0
  · subst m
    rw [fabiusDyadic_arg_zero]
    exact (extendedFabiusDyadicValue_zero n).symm
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hmposInt' : 0 < (m : ℤ) := by exact_mod_cast hmpos
    have hmposInt : ¬ (m : ℤ) ≤ 0 := not_le_of_gt hmposInt'
    rw [extendedFabiusDyadicValue, if_neg hmposInt]
    simp only [Int.toNat_natCast]
    let scale : ℕ := 2 ^ n
    let period : ℕ := 2 * scale
    let block : ℕ := m / period
    let residue : ℕ := m % period
    let core : ℕ := if residue ≤ scale then residue else period - residue
    change fabiusDyadic n m =
      (thueMorseSign block : ℚ) * fabiusDyadicUnit n core
    have hperiodPos : 0 < period := by simp [period, scale]
    have hresidueLt : residue < period := Nat.mod_lt _ hperiodPos
    have hperiod : period = 2 ^ (n + 1) := by
      simp only [period, scale, pow_succ]
      omega
    have hmdecomp : m = block * 2 ^ (n + 1) + residue := by
      calc
        m = period * (m / period) + m % period :=
          (Nat.div_add_mod m period).symm
        _ = (m / period) * period + m % period := by ac_rfl
        _ = block * 2 ^ (n + 1) + residue := by rw [← hperiod]
    rw [hmdecomp, fabiusDyadic_block_translate n block residue
      (by simpa only [← hperiod] using hresidueLt)]
    congr 1
    simpa only [core, scale, period] using
      fabiusDyadic_first_block_eq_fold n residue
        (by simpa only [← hperiod] using hresidueLt)

/-! ## Representation invariance -/

/-- Refining the natural dyadic grid once leaves the closed formula
unchanged.  This specializes the kernel-level refinement theorem to the
proved Fabius kernel law. -/
theorem fabiusDyadic_refine (n m : ℕ) :
    fabiusDyadic (n + 1) (2 * m) = fabiusDyadic n m :=
  fabiusDyadic_refine_of_kernel dyadicKernel_has_refinement n m

/-- Refining the natural dyadic grid by `k` binary places leaves the closed
formula unchanged. -/
theorem fabiusDyadic_refine_pow (n k m : ℕ) :
    fabiusDyadic (n + k) (2 ^ k * m) = fabiusDyadic n m :=
  fabiusDyadic_refine_pow_of_kernel dyadicKernel_has_refinement n k m

/-- The natural-numerator closed formula depends only on the represented
rational number, even when both numerator and denominator exponent change. -/
theorem fabiusDyadic_eq_of_rat_eq
    (n₁ n₂ m₁ m₂ : ℕ)
    (h : (m₁ : ℚ) / (2 : ℚ) ^ n₁ =
      (m₂ : ℚ) / (2 : ℚ) ^ n₂) :
    fabiusDyadic n₁ m₁ = fabiusDyadic n₂ m₂ := by
  rw [fabiusDyadic_eq_extendedFabiusDyadicValue_nat n₁ m₁,
    fabiusDyadic_eq_extendedFabiusDyadicValue_nat n₂ m₂]
  apply extendedFabiusDyadicValue_eq_of_rat_eq
    n₁ n₂ (m₁ : ℤ) (m₂ : ℤ)
  norm_num only [Int.cast_natCast]
  exact h

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

/-- Equation (32) computes the signed global Fabius extension at every
nonnegative dyadic numerator, with no unit-interval restriction. -/
theorem fabiusDyadic_cast_extended_nat
    (F : BoundedFabius) (hF : IsFabius F) (n m : ℕ) :
    (fabiusDyadic n m : ℝ) =
      extendedFabius F ((m : ℝ) / (2 : ℝ) ^ n) := by
  rw [fabiusDyadic_eq_extendedFabiusDyadicValue_nat]
  simpa using extendedFabiusDyadicValue_cast F hF n (m : ℤ)

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

/-- The signed dyadic evaluator agrees with Rvachev's function for every
integer numerator.  Outside `[-1,1]` both sides vanish, so this removes the
support restriction from `rvachevDyadic_cast`. -/
theorem rvachevDyadic_cast_global
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) (a : ℤ) :
    (rvachevDyadic n a : ℝ) = rvachevUp F (a / (2 : ℝ) ^ n) := by
  by_cases ha : a.natAbs ≤ 2 ^ n
  · exact rvachevDyadic_cast F hF n a ha
  · have halt : 2 ^ n < a.natAbs := Nat.lt_of_not_ge ha
    have habs : 1 < |(a : ℝ) / (2 : ℝ) ^ n| := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      rw [one_lt_div (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)]
      have hcast : (2 : ℝ) ^ n < (a.natAbs : ℝ) := by
        exact_mod_cast halt
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hcast
    have hzero : rvachevUp F ((a : ℝ) / (2 : ℝ) ^ n) = 0 := by
      apply rvachevUp_eq_zero_of_not_mem_Ioo F hF
      intro hx
      have hxabs : |(a : ℝ) / (2 : ℝ) ^ n| < 1 := (abs_lt).2 hx
      linarith
    rw [rvachevDyadic, if_neg ha, Rat.cast_zero, hzero]

/-! ## Rational-input Rvachev evaluator -/

/-- A successful rational-input evaluation has the correct Rvachev value. -/
theorem evalRvachevDyadic_eq_some_correct
    (F : BoundedFabius) (hF : IsFabius F)
    (x value : ℚ) (hvalue : evalRvachevDyadic x = some value) :
    (value : ℝ) = rvachevUp F (x : ℝ) := by
  unfold evalRvachevDyadic at hvalue
  split at hvalue
  · simp at hvalue
  · rename_i exponent hexponent
    injection hvalue with hvalue
    subst value
    have hden : x.den = 2 ^ exponent := by
      unfold dyadicExponent? at hexponent
      dsimp only at hexponent
      split at hexponent
      · rename_i h
        injection hexponent with he
        simpa [he] using h
      · simp at hexponent
    rw [rvachevDyadic_cast_global F hF]
    congr 1
    rw [Rat.cast_def, hden]
    norm_num

/-- Every dyadic rational has an explicitly computed rational value equal to
the analytic Rvachev function. -/
theorem evalRvachevDyadic_complete_correct
    (F : BoundedFabius) (hF : IsFabius F) (x : ℚ)
    (hx : IsDyadicRational x) :
    ∃ value : ℚ,
      evalRvachevDyadic x = some value ∧
        (value : ℝ) = rvachevUp F (x : ℝ) := by
  obtain ⟨exponent, hexponent⟩ := (dyadicExponent?_exists_iff x).2 hx
  let value := rvachevDyadic exponent x.num
  have hvalue : evalRvachevDyadic x = some value := by
    simp [evalRvachevDyadic, hexponent, value]
  exact ⟨value, hvalue,
    evalRvachevDyadic_eq_some_correct F hF x value hvalue⟩

end Fabius

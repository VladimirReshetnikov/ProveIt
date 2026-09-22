/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license; see vendor/combinatorial-games/LICENSE.
Authors: Violeta Hernández Palacios

Adapted for this project from the proved finite-arithmetic lemmas in
vihdzp/combinatorial-games commit 02b4a908ea2ecfefffecb438f691951a814a5264,
CombinatorialGames/Surreal/Birthday/Dyadic.lean, Surreal/Dyadic.lean,
and Mathlib/Dyadic.lean. The adaptations keep these arithmetic proofs local
and identify the result with a natural-ceiling and denominator-log formula.
-/
import CombinatorialGames.Surreal.Dyadic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Prime.Basic

/-!
# Finite arithmetic for dyadic birthdays

The arithmetic quantity `height q = ⌈|q.toRat|⌉₊ + Nat.log 2 q.den`
satisfies the lower/upper option recurrence needed for the finite-birthday
calculation in `found:sub:cutoffs`. This module only proves finite dyadic
arithmetic; the identification with birthdays is proved separately.

The reference source's game-birthday modules are not imported. Only the
proved arithmetic helpers are adapted here, with their provenance above.
-/

namespace Surreal.Foundations.DyadicBirthdayArithmetic

open Dyadic

/-- The closed arithmetic expression for the birthday of a dyadic number. -/
def height (q : Dyadic) : ℕ := Nat.ceil |q.toRat| + Nat.log 2 q.den

private theorem div_lt_div_iff_exists {a b c : ℕ} : a / c < b / c ↔ ∃ d, a < d ∧ d ≤ b ∧ c ∣ d := by
  constructor
  · intro h
    refine ⟨b - b % c, ?_, Nat.sub_le b _, Nat.dvd_sub_mod b⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at h
    have hmul := (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hc0)).mp h
    have hmod : b / c * c + b % c = b := by
      simpa only [Nat.mul_comm c] using Nat.div_add_mod b c
    omega
  · intro ⟨d, ha, hb, hc⟩
    grw [← hb]
    exact Nat.div_lt_div_of_lt_of_dvd hc ha

private theorem den_eq_two_pow_toNat_precision (x : Dyadic) :
    x.den = 2 ^ (x.precision.getD 0).toNat := by
  cases x with
  | zero => rfl
  | ofOdd n k hn =>
    cases k with
    | ofNat k => rfl
    | negSucc k => rfl

private theorem precision_eq_none {x : Dyadic} : x.precision = none ↔ x = 0 := by
  cases x <;> simp [Dyadic.precision]

private theorem isSome_precision_eq_true {x : Dyadic} : x.precision.isSome = true ↔ x ≠ 0 :=
  Option.isSome_iff_ne_none.trans precision_eq_none.not

private theorem isSome_precision_eq_true_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) :
    x.precision.isSome = true :=
  isSome_precision_eq_true.mpr (mt (by rintro rfl; rfl) hx)

private theorem max_den_lower_upper {x : Dyadic} (hx : x.den ≠ 1) :
    max x.lower.den x.upper.den = x.den / 2 := by
  unfold Dyadic.den at hx ⊢
  rw [coe_lower, coe_upper]
  unfold Dyadic.den
  rw [Rat.sub_def', Rat.den_mkRat, if_neg (by positivity),
    Rat.add_def', Rat.den_mkRat, if_neg (by positivity),
    Rat.den_inv_of_ne_zero (by positivity), Rat.num_inv, Rat.num_natCast,
    Int.natAbs_natCast, Rat.den_natCast, Int.sign_natCast_of_ne_zero x.den_ne_zero,
    Nat.cast_one, Int.one_mul, ← Int.sub_mul, ← Int.add_mul,
    Int.natAbs_mul, Int.natAbs_mul, Int.natAbs_natCast,
    Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ x.den_pos,
    Nat.gcd_mul_right, Nat.mul_div_mul_right _ _ x.den_pos]
  generalize hn : x.toRat.num = n, hd : x.toRat.den = d
  obtain ⟨e, rfl⟩ : ∃ e, 2 ^ e = d := by
    rw [← hd, ← Submonoid.mem_powers_iff]
    exact x.den_mem_powers
  cases e with
  | zero => exact (hx hd).elim
  | succ e =>
    have ⟨l2, hl2⟩ : Even (n - 1).natAbs := by simpa [hn] using x.odd_num hx
    have ⟨u2, hu2⟩ : Even (n + 1).natAbs := by simpa [hn] using x.odd_num hx
    rw [pow_succ, Nat.mul_div_cancel _ two_pos, hl2, hu2,
      ← Nat.mul_two, ← Nat.mul_two, Nat.gcd_mul_right, Nat.gcd_mul_right,
      Nat.mul_div_mul_right _ _ two_pos, Nat.mul_div_mul_right _ _ two_pos]
    refine le_antisymm (max_le (Nat.div_le_self _ _) (Nat.div_le_self _ _)) ?_
    suffices h : Nat.gcd 2 l2 = 1 ∨ Nat.gcd 2 u2 = 1 by
      obtain h | h := h
      · rw [Nat.gcd_pow_left_of_gcd_eq_one h, Nat.div_one]
        exact Nat.le_max_left _ _
      · rw [Nat.gcd_pow_left_of_gcd_eq_one h, Nat.div_one]
        exact Nat.le_max_right _ _
    rw [← Nat.coprime_iff_gcd_eq_one, ← Nat.coprime_iff_gcd_eq_one,
      Nat.coprime_two_left, Nat.coprime_two_left,
      ← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, ← not_and_or]
    rintro ⟨⟨l4, rfl⟩, ⟨u4, rfl⟩⟩
    omega

private def rawHeight (x : Dyadic) : Nat :=
  if h : x.den = 1 then x.num.natAbs else
  (x.precision.get (isSome_precision_eq_true_of_den_ne_one h)).toNat + x.num.natAbs / x.den + 1

@[simp]
private theorem rawHeight_intCast (n : Int) : rawHeight n = n.natAbs := by
  unfold rawHeight
  rw [dif_pos (Dyadic.den_intCast n), Dyadic.num_intCast]

@[simp]
private theorem rawHeight_natCast (n : Nat) : rawHeight n = n := by
  rw [← Int.cast_natCast, rawHeight_intCast, Int.natAbs_natCast]

private theorem rawHeight_of_den_eq_one {x : Dyadic} (hx : x.den = 1) :
    rawHeight x = x.num.natAbs :=
  (congrArg rawHeight (intCast_num_eq_self_of_den_eq_one hx)).symm.trans
    (rawHeight_intCast x.num)

private theorem rawHeight_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) :
    rawHeight x =
      (x.precision.get (isSome_precision_eq_true_of_den_ne_one hx)).toNat +
        x.num.natAbs / x.den + 1 :=
  dif_neg hx


private theorem natAbs_num_div_den_lower_eq_natAbs_num_div_den {x : Dyadic}
    (hxl : x.lower.den ≠ 1) : x.lower.num.natAbs / x.lower.den = x.num.natAbs / x.den := by
  have hcd : x.num / x.den = x.toRat := x.toRat.num_div_den
  have hd : x.den ≠ 1 := by
    contrapose hxl
    rw [x.lower_eq_of_den_eq_one hxl, ← Int.cast_one, ← Int.cast_sub, Dyadic.den_intCast]
  have hle : x.lower.toRat = Int.cast (x.num - 1) / x.den := by
    rw [x.coe_lower, ← hcd, ← one_div, ← sub_div, ← Rat.intCast_one, ← Int.cast_sub]
  have hlnd : x.lower.num.natAbs / x.lower.den = (x.num - 1).natAbs / x.den := by
    rw [Dyadic.num, Dyadic.den, x.coe_lower, ← hcd, ← one_div, ← sub_div,
      ← Int.cast_one, ← Int.cast_sub, ← Rat.mkRat_eq_div, Rat.num_mkRat, Rat.den_mkRat,
      if_neg x.den_ne_zero, if_neg x.den_ne_zero,
      Int.natAbs_ediv_of_dvd (Int.natCast_dvd.2 (Nat.gcd_dvd_right _ _)),
      Int.natAbs_natCast, ← Nat.mul_div_mul_right _ _ (Nat.gcd_pos_of_pos_left _ x.den_pos),
      Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
  rw [hlnd]
  apply le_antisymm
  · rw [← not_lt, div_lt_div_iff_exists]
    push Not
    intro k hkl hkr
    cases le_antisymm (Nat.add_one_le_of_lt hkl) (hkr.trans (Int.natAbs_sub_le _ 1))
    rw [le_antisymm hkr (Int.natAbs_sub_le _ 1), ← Int.natCast_dvd]
    contrapose! hxl
    obtain ⟨e, he⟩ := hxl
    rw [he, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ (by positivity)] at hle
    rw [Dyadic.den, hle, Rat.den_intCast]
  · rw [← not_lt, div_lt_div_iff_exists]
    push Not
    intro k hkl hkr
    rw [← Int.sub_add_cancel x.num 1] at hkr
    cases le_antisymm (Nat.add_one_le_of_lt hkl) (hkr.trans (Int.natAbs_add_le _ 1))
    rw [le_antisymm hkr (Int.natAbs_add_le _ 1), Int.sub_add_cancel, ← Int.natCast_dvd]
    contrapose! hd
    obtain ⟨e, he⟩ := hd
    rw [he, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ (by positivity)] at hcd
    rw [Dyadic.den, ← hcd, Rat.den_intCast]

private theorem natAbs_num_div_den_upper_eq_natAbs_num_div_den {x : Dyadic}
    (hxl : x.upper.den ≠ 1) : x.upper.num.natAbs / x.upper.den = x.num.natAbs / x.den := by
  rw [← den_neg] at hxl
  rw [← Int.natAbs_neg x.upper.num, ← Int.natAbs_neg x.num, ← den_neg x.upper, ← den_neg x,
    ← num_neg x.upper, ← num_neg x]
  rw [← lower_neg] at hxl ⊢
  exact natAbs_num_div_den_lower_eq_natAbs_num_div_den hxl

private theorem max_rawHeight_lower_rawHeight_upper_add_one_of_den_ne_one {x : Dyadic}
    (hx : x.den ≠ 1) : max (rawHeight x.lower) (rawHeight x.upper) + 1 = rawHeight x := by
  have hcd : x.num / x.den = x.toRat := x.toRat.num_div_den
  have hnd := max_den_lower_upper hx
  have hnd0 : (x.precision.getD 0).toNat ≠ 0 := by
    apply_fun (2 ^ ·)
    rwa [← den_eq_two_pow_toNat_precision]
  simp_rw [den_eq_two_pow_toNat_precision] at hnd
  rw [← (pow_right_monotone one_le_two).map_max,
    ← Nat.pow_sub_one two_ne_zero hnd0, pow_right_inj₀ Nat.two_pos (by decide),
    eq_comm, Nat.sub_eq_iff_eq_add (Nat.one_le_iff_ne_zero.2 hnd0)] at hnd
  rw [rawHeight_of_den_ne_one hx, Option.get_eq_getD, hnd, Nat.add_one_inj, Nat.add_right_comm]
  have hk (c : ℤ) (d : ℕ) : (Rat.num (c / d)).natAbs / Rat.den (c / d) = c.natAbs / d := by
    obtain hd0 | hd0 := eq_zero_or_pos d
    · simp [hd0]
    · rw [← Rat.mkRat_eq_div, Rat.num_mkRat, Rat.den_mkRat,
        if_neg hd0.ne', if_neg hd0.ne',
        Int.natAbs_ediv_of_dvd (Int.natCast_dvd.2 (Nat.gcd_dvd_right _ _)),
        Int.natAbs_natCast, ← Nat.mul_div_mul_right _ _ (Nat.gcd_pos_of_pos_left c.natAbs hd0),
        Nat.div_mul_cancel (Nat.gcd_dvd_left _ _), Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]
  have hle : x.lower.toRat = Int.cast (x.num - 1) / x.den := by
    rw [x.coe_lower, ← hcd, ← one_div, ← sub_div, ← Rat.intCast_one, ← Int.cast_sub]
  have hue : x.upper.toRat = Int.cast (x.num + 1) / x.den := by
    rw [x.coe_upper, ← hcd, ← one_div, ← add_div, ← Rat.intCast_one, ← Int.cast_add]
  have hlnd (hl : x.lower.den = 1) : x.lower.num.natAbs = (x.num - 1).natAbs / x.den := by
    have hlnd := congr((x.lower.num / $hl : ℚ))
    rw [Nat.cast_one, div_one, ← Int.cast_natCast, ← Rat.intCast_div _ _ (by simp [hl]),
      Int.cast_inj] at hlnd
    rw [← hlnd, Int.natAbs_ediv_of_dvd (by simp [hl]), Int.natAbs_natCast,
      Dyadic.num, Dyadic.den, hle, hk]
  have hund (hr : x.upper.den = 1) : x.upper.num.natAbs = (x.num + 1).natAbs / x.den := by
    have hund := congr((x.upper.num / $hr : Rat))
    rw [Nat.cast_one, div_one, ← Int.cast_natCast, ← Rat.intCast_div _ _ (by simp [hr]),
      Int.cast_inj] at hund
    rw [← hund, Int.natAbs_ediv_of_dvd (by simp [hr]), Int.natAbs_natCast,
      Dyadic.num, Dyadic.den, hue, hk]
  by_cases hl : x.lower.den = 1 <;> by_cases hr : x.upper.den = 1
  · rw [rawHeight_of_den_eq_one hl, rawHeight_of_den_eq_one hr]
    rw [den_eq_two_pow_toNat_precision, Nat.pow_eq_one, or_iff_right (by decide)] at hl hr
    rw [hl, hr, max_self, zero_add, ← Nat.pow_right_inj Nat.one_lt_two, Nat.pow_one,
      ← den_eq_two_pow_toNat_precision] at hnd
    rw [hnd, hl, hr, max_self, zero_add]
    obtain ⟨c, hc⟩ := x.odd_num hx
    unfold Dyadic.num
    rw [hle, hue, hnd, hc, Int.add_sub_cancel, Int.add_assoc, ← two_mul, ← Int.mul_add,
      Rat.intCast_mul, Rat.intCast_mul, Rat.intCast_ofNat, Rat.natCast_ofNat,
      mul_div_cancel_left₀ _ two_ne_zero, mul_div_cancel_left₀ _ two_ne_zero,
      Rat.num_intCast, Rat.num_intCast]
    rw [show x.toRat.num = 2 * c + 1 from hc]
    omega
  · rw [rawHeight_of_den_eq_one hl, rawHeight_of_den_ne_one hr,
      natAbs_num_div_den_upper_eq_natAbs_num_div_den hr, hlnd hl]
    rw [den_eq_two_pow_toNat_precision, Nat.pow_eq_one, or_iff_right (by decide)] at hl
    rw [hl, zero_max] at hnd ⊢
    rw [Option.get_eq_getD, max_eq_right_iff, Nat.add_assoc]
    apply le_add_of_le_right
    grw [Int.natAbs_sub_le]
    rw [Int.natAbs_one, Nat.succ_div, Nat.add_le_add_iff_left]
    apply ite_le_sup
  · rw [rawHeight_of_den_ne_one hl, rawHeight_of_den_eq_one hr,
      natAbs_num_div_den_lower_eq_natAbs_num_div_den hl, hund hr]
    rw [den_eq_two_pow_toNat_precision, Nat.pow_eq_one, or_iff_right (by decide)] at hr
    rw [hr, max_zero] at hnd ⊢
    rw [Option.get_eq_getD, max_eq_left_iff, Nat.add_assoc]
    apply le_add_of_le_right
    grw [Int.natAbs_add_le]
    rw [Int.natAbs_one, Nat.succ_div, Nat.add_le_add_iff_left]
    apply ite_le_sup
  · rw [rawHeight_of_den_ne_one hl, rawHeight_of_den_ne_one hr,
      natAbs_num_div_den_lower_eq_natAbs_num_div_den hl,
      natAbs_num_div_den_upper_eq_natAbs_num_div_den hr,
      Nat.add_max_add_right, Nat.add_max_add_right, Option.get_eq_getD, Option.get_eq_getD]


private theorem abs_toRat_eq_natAbs_num_div_den (q : Dyadic) :
    |q.toRat| = (q.num.natAbs : ℚ) / q.den := by
  calc
    |q.toRat| = |(q.num : ℚ) / (q.den : ℚ)| := congrArg abs q.toRat.num_div_den.symm
    _ = _ := by rw [abs_div, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]

private theorem den_abs_toRat (q : Dyadic) : |q.toRat|.den = q.den := by
  rcases le_total 0 q.toRat with hq | hq
  · rw [abs_of_nonneg hq]
  · rw [abs_of_nonpos hq, Rat.den_neg_eq_den]

private theorem ceil_abs_of_den_ne_one {q : Dyadic} (hq : q.den ≠ 1) :
    Nat.ceil |q.toRat| = q.num.natAbs / q.den + 1 := by
  have hne : (Nat.floor |q.toRat| : ℚ) ≠ |q.toRat| := by
    intro h
    have hd := congrArg Rat.den h
    rw [Rat.den_natCast, den_abs_toRat] at hd
    exact hq hd.symm
  have hc : Nat.ceil |q.toRat| = Nat.floor |q.toRat| + 1 := by
    apply le_antisymm (Nat.ceil_le_floor_add_one _) (Nat.add_one_le_ceil_iff.mpr ?_)
    exact lt_of_le_of_ne (Nat.floor_le (abs_nonneg _)) hne
  rw [hc, abs_toRat_eq_natAbs_num_div_den, Rat.natFloor_natCast_div_natCast]

private theorem log_den_eq_precision (q : Dyadic) :
    Nat.log 2 q.den = (q.precision.getD 0).toNat := by
  rw [den_eq_two_pow_toNat_precision, Nat.log_pow (by decide : 1 < 2)]

/-- For an integral dyadic, the height is the absolute value of its numerator. -/
theorem height_of_den_eq_one {q : Dyadic} (hq : q.den = 1) : height q = q.num.natAbs := by
  rw [height, hq, Nat.log_one_right, add_zero, abs_toRat_eq_natAbs_num_div_den,
    hq, Nat.cast_one, div_one, Nat.ceil_natCast]

private theorem height_eq_rawHeight (q : Dyadic) : height q = rawHeight q := by
  by_cases hq : q.den = 1
  · rw [height_of_den_eq_one hq, rawHeight_of_den_eq_one hq]
  · rw [height, ceil_abs_of_den_ne_one hq, log_den_eq_precision,
      rawHeight_of_den_ne_one hq, Option.get_eq_getD (fallback := 0)]
    omega

/-- The nonintegral dyadic option recurrence for the closed height formula. -/
theorem max_height_lower_upper_add_one {q : Dyadic} (hq : q.den ≠ 1) :
    max (height q.lower) (height q.upper) + 1 = height q := by
  simp only [height_eq_rawHeight]
  exact max_rawHeight_lower_rawHeight_upper_add_one_of_den_ne_one hq

end Surreal.Foundations.DyadicBirthdayArithmetic

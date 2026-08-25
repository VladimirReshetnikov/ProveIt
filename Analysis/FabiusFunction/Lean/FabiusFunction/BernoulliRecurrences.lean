import FabiusFunction.MomentPowerSeries
import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli recurrences for the Fabius moments

This module proves Proposition 22 of *Arithmetic of the Fabius function* from
the executable moment recurrences and Mathlib's formal generating series for
the Bernoulli numbers.  The positive-index formulas are accompanied by
successor-index forms, so downstream recursions can use them without carrying
a separate positivity hypothesis.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius

/-- A positive power of two is not one in `ℚ`.  This is the common
denominator fact used by the moment and recurrence-sequence formulas. -/
theorem rat_two_pow_sub_one_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℚ) ^ n - 1 ≠ 0 := by
  exact ne_of_gt (sub_pos.mpr
    (one_lt_pow₀ (a := (2 : ℚ)) (by norm_num) (by omega)))

/-- The original, non-isolated recurrence for the half moments. -/
theorem halfMoment_original_recurrence (n : ℕ) :
    (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n) * halfMoment n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (n + 1) k : ℚ) * halfMoment k := by
  cases n with
  | zero => norm_num [halfMoment]
  | succ n =>
      rw [sum_range_succ, halfMoment_succ]
      rw [Fin.sum_univ_eq_sum_range
        (fun k => (Nat.choose (n + 2) k : ℚ) * halfMoment k) (n + 1)]
      have hchoose : (n + 2).choose (n + 1) = n + 2 := by
        exact Nat.choose_succ_self_right (n + 1)
      rw [hchoose]
      have hpow := rat_two_pow_sub_one_ne_zero (n + 1) (by omega)
      field_simp
      ring

private noncomputable def halfMomentPS22 : PowerSeries ℚ :=
  PowerSeries.mk fun n => halfMoment n / (n.factorial : ℚ)

private noncomputable def expm1DivPS22 : PowerSeries ℚ :=
  PowerSeries.mk fun n => 1 / ((n + 1).factorial : ℚ)

private lemma X_mul_expm1DivPS22 :
    (PowerSeries.X : PowerSeries ℚ) * expm1DivPS22 =
      PowerSeries.exp ℚ - 1 := by
  ext (_ | n)
  · simp
  · simp [expm1DivPS22, PowerSeries.coeff_exp]

private lemma halfMomentPS22_functional :
    PowerSeries.rescale 2 halfMomentPS22 = halfMomentPS22 * expm1DivPS22 := by
  ext n
  rw [PowerSeries.coeff_rescale, PowerSeries.coeff_mul]
  simp only [halfMomentPS22, expm1DivPS22, PowerSeries.coeff_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hleft :
      (((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ n * halfMoment n) /
          ((n + 1).factorial : ℚ) =
        2 ^ n * (halfMoment n / (n.factorial : ℚ)) := by
    rw [Nat.factorial_succ]
    field_simp
    push_cast
    ring
  have hterm (x : ℕ) (hx : x ∈ range (n + 1)) :
      ((Nat.choose (n + 1) x : ℚ) * halfMoment x) /
          ((n + 1).factorial : ℚ) =
        halfMoment x / (x.factorial : ℚ) *
          (1 / ((n - x + 1).factorial : ℚ)) := by
    have hxlt := mem_range.1 hx
    have hxle : x ≤ n + 1 := by omega
    rw [Nat.cast_choose ℚ hxle]
    have hsub : n + 1 - x = n - x + 1 := by omega
    rw [hsub]
    field_simp
  have h := congrArg
    (fun q : ℚ => q / ((n + 1).factorial : ℚ))
    (halfMoment_original_recurrence n)
  rw [hleft] at h
  rw [Finset.sum_div] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro x hx
  exact hterm x hx

private lemma bernoulli_mul_rescale_halfMomentPS22 :
    bernoulliPowerSeries ℚ * PowerSeries.rescale 2 halfMomentPS22 =
      halfMomentPS22 := by
  apply PowerSeries.X_pow_mul_cancel (k := 1)
  simp only [pow_one]
  rw [halfMomentPS22_functional]
  calc
    (PowerSeries.X : PowerSeries ℚ) *
          (bernoulliPowerSeries ℚ * (halfMomentPS22 * expm1DivPS22)) =
        halfMomentPS22 *
          (bernoulliPowerSeries ℚ *
            ((PowerSeries.X : PowerSeries ℚ) * expm1DivPS22)) := by ring
    _ = halfMomentPS22 *
          (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) := by
      rw [X_mul_expm1DivPS22]
    _ = halfMomentPS22 * PowerSeries.X := by
      rw [bernoulliPowerSeries_mul_exp_sub_one]
    _ = PowerSeries.X * halfMomentPS22 := by ring

/-- The coefficient identity obtained from the Bernoulli generating series and
the half-moment generating series. -/
theorem halfMoment_bernoulli_convolution (n : ℕ) :
    (∑ k ∈ range (n + 1),
        (Nat.choose n k : ℚ) * bernoulli k * (2 : ℚ) ^ (n - k) *
          halfMoment (n - k)) = halfMoment n := by
  have h := congrArg (PowerSeries.coeff n)
    bernoulli_mul_rescale_halfMomentPS22
  simp only [PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, bernoulliPowerSeries,
    PowerSeries.coeff_mk, PowerSeries.coeff_rescale, halfMomentPS22] at h
  calc
    (∑ k ∈ range (n + 1),
          (Nat.choose n k : ℚ) * bernoulli k * 2 ^ (n - k) *
            halfMoment (n - k)) =
        (n.factorial : ℚ) *
          ∑ x ∈ range n.succ,
            bernoulli x / (x.factorial : ℚ) *
              (2 ^ (n - x) *
                (halfMoment (n - x) / ((n - x).factorial : ℚ))) := by
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkle : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
      rw [Nat.cast_choose ℚ hkle]
      field_simp
    _ = (n.factorial : ℚ) *
        (halfMoment n / (n.factorial : ℚ)) := by
      simpa using congrArg (fun q : ℚ => (n.factorial : ℚ) * q) h
    _ = halfMoment n := by field_simp

/-- Equation (39), the Bernoulli recurrence for the half moments. -/
theorem halfMoment_bernoulli_recurrence (n : ℕ) (hn : 1 ≤ n) :
    halfMoment n =
      ((n : ℚ) * (2 : ℚ) ^ n / (4 * ((2 : ℚ) ^ n - 1))) *
          halfMoment (n - 1) -
        (∑ k ∈ Icc 1 (n / 2),
          (Nat.choose n (2 * k) : ℚ) * (2 : ℚ) ^ (n - 2 * k) *
            bernoulli (2 * k) * halfMoment (n - 2 * k)) /
          ((2 : ℚ) ^ n - 1) := by
  let f : ℕ → ℚ := fun k =>
    (Nat.choose n k : ℚ) * bernoulli k * (2 : ℚ) ^ (n - k) *
      halfMoment (n - k)
  have hconv : (∑ k ∈ range (n + 1), f k) = halfMoment n := by
    simpa [f] using halfMoment_bernoulli_convolution n
  have hevenSet :
      (range (n + 1)).filter (fun k => Even k) =
        (range (n / 2 + 1)).image (fun k => 2 * k) := by
    ext x
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hx, ⟨k, rfl⟩⟩
      refine ⟨k, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨by omega, ⟨k, by omega⟩⟩
  have hevenSum :
      (∑ k ∈ (range (n + 1)).filter (fun k => Even k), f k) =
        ∑ k ∈ range (n / 2 + 1), f (2 * k) := by
    rw [hevenSet, Finset.sum_image]
    intro a ha b hb hab
    change 2 * a = 2 * b at hab
    omega
  have hoddSet :
      (range (n + 1)).filter (fun k => ¬ Even k) =
        (range (n + 1)).filter (fun k => Odd k) := by
    ext k
    simp only [mem_filter]
    exact and_congr_right (fun _ => Nat.not_even_iff_odd)
  have honeMem : 1 ∈ (range (n + 1)).filter (fun k => Odd k) := by
    rw [mem_filter]
    constructor
    · simp
      omega
    · norm_num
  have hoddSum :
      (∑ k ∈ (range (n + 1)).filter (fun k => Odd k), f k) = f 1 := by
    apply Finset.sum_eq_single 1
    · intro k hk hkne
      have hkOdd : Odd k := (mem_filter.mp hk).2
      have hklt : k < n + 1 := mem_range.mp (mem_filter.mp hk).1
      have hkgt : 1 < k := by
        have hkpos := hkOdd.pos
        omega
      dsimp [f]
      rw [bernoulli_eq_zero_of_odd hkOdd hkgt]
      ring
    · intro hnot
      exact (hnot honeMem).elim
  have hrangeErase :
      (range (n / 2 + 1)).erase 0 = Icc 1 (n / 2) := by
    ext k
    simp
    omega
  have hevenDecomp :
      (∑ k ∈ range (n / 2 + 1), f (2 * k)) =
        f 0 + ∑ k ∈ Icc 1 (n / 2), f (2 * k) := by
    have h := Finset.sum_erase_add (range (n / 2 + 1))
      (fun k => f (2 * k)) (show 0 ∈ range (n / 2 + 1) by simp)
    rw [hrangeErase] at h
    simpa [add_comm] using h.symm
  have hsplitBase := Finset.sum_filter_add_sum_filter_not
    (range (n + 1)) (fun k => Even k) f
  rw [hoddSet, hevenSum, hoddSum, hevenDecomp] at hsplitBase
  have hf0 : f 0 = (2 : ℚ) ^ n * halfMoment n := by
    simp [f]
  have hf1 :
      f 1 = -((n : ℚ) * (2 : ℚ) ^ n / 4 * halfMoment (n - 1)) := by
    dsimp [f]
    rw [Nat.choose_one_right, bernoulli_one]
    have hnEq : n = n - 1 + 1 := by omega
    rw [hnEq, pow_succ]
    push_cast
    ring
  have hevenTerm (k : ℕ) :
      f (2 * k) =
        (Nat.choose n (2 * k) : ℚ) * (2 : ℚ) ^ (n - 2 * k) *
          bernoulli (2 * k) * halfMoment (n - 2 * k) := by
    dsimp [f]
    ring
  simp_rw [hevenTerm] at hsplitBase
  rw [hf0, hf1] at hsplitBase
  have hrel :
      (2 : ℚ) ^ n * halfMoment n +
            (∑ k ∈ Icc 1 (n / 2),
              (Nat.choose n (2 * k) : ℚ) * (2 : ℚ) ^ (n - 2 * k) *
                bernoulli (2 * k) * halfMoment (n - 2 * k)) -
          ((n : ℚ) * (2 : ℚ) ^ n / 4 * halfMoment (n - 1)) =
        halfMoment n := by
    calc
      _ = ∑ k ∈ range (n + 1), f k := by linear_combination hsplitBase
      _ = halfMoment n := hconv
  have hpow := rat_two_pow_sub_one_ne_zero n hn
  field_simp [hpow]
  linear_combination 4 * hrel

/-- All-index successor form of the half-moment Bernoulli recurrence. -/
theorem halfMoment_bernoulli_succ_recurrence (n : ℕ) :
    halfMoment (n + 1) =
      ((((n + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (n + 1) /
          (4 * ((2 : ℚ) ^ (n + 1) - 1))) * halfMoment n) -
        (∑ k ∈ Icc 1 ((n + 1) / 2),
          (Nat.choose (n + 1) (2 * k) : ℚ) *
            (2 : ℚ) ^ (n + 1 - 2 * k) *
            bernoulli (2 * k) * halfMoment (n + 1 - 2 * k)) /
          ((2 : ℚ) ^ (n + 1) - 1) := by
  simpa only [Nat.add_sub_cancel] using
    halfMoment_bernoulli_recurrence (n + 1) (by omega)

private noncomputable def bernoulliCoshFactorPS22 : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    ((2 : ℚ) - 4 ^ n) * bernoulli (2 * n) / ((2 * n).factorial : ℚ)

private noncomputable def fullBernoulliCoshFactorPS22 : PowerSeries ℚ :=
  PowerSeries.C 2 * bernoulliPowerSeries ℚ -
    PowerSeries.rescale 2 (bernoulliPowerSeries ℚ)

private noncomputable def fullSinhDivPS22 : PowerSeries ℚ :=
  PowerSeries.expand 2 (by omega) sinhDivPS

private lemma expand_two_injective {P Q : PowerSeries ℚ}
    (h : PowerSeries.expand 2 (by omega) P =
      PowerSeries.expand 2 (by omega) Q) : P = Q := by
  ext n
  have hn := congrArg (PowerSeries.coeff (2 * n)) h
  simpa [PowerSeries.coeff_expand] using hn

private lemma expand_bernoulliCoshFactorPS22 :
    PowerSeries.expand 2 (by omega) bernoulliCoshFactorPS22 =
      fullBernoulliCoshFactorPS22 := by
  ext m
  simp only [fullBernoulliCoshFactorPS22, map_sub,
    PowerSeries.coeff_expand, bernoulliCoshFactorPS22,
    PowerSeries.coeff_mk, PowerSeries.coeff_rescale,
    bernoulliPowerSeries, PowerSeries.coeff_C_mul]
  rcases m.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul k]
    simp [pow_mul]
    ring
  · have hnot : ¬ 2 ∣ 2 * k + 1 := Nat.not_two_dvd_bit1 k
    rw [if_neg hnot]
    cases k with
    | zero => norm_num
    | succ k =>
        rw [bernoulli_eq_zero_of_odd ⟨k + 1, by omega⟩ (by omega)]
        simp

private lemma two_X_mul_fullSinhDivPS22 :
    PowerSeries.C 2 * ((PowerSeries.X : PowerSeries ℚ) * fullSinhDivPS22) =
      PowerSeries.exp ℚ -
        PowerSeries.rescale (-1) (PowerSeries.exp ℚ) := by
  ext (_ | m)
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_zero_X_mul, map_sub,
      PowerSeries.coeff_rescale]
    norm_num [PowerSeries.coeff_exp]
  · rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul]
    simp only [fullSinhDivPS22,
      PowerSeries.coeff_expand, sinhDivPS, PowerSeries.coeff_mk,
      map_sub, PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
    rcases m.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [← two_mul k]
      simp
      norm_num [pow_succ, pow_mul]
      ring
    · have hnot : ¬ 2 ∣ 2 * k + 1 := Nat.not_two_dvd_bit1 k
      rw [if_neg hnot]
      norm_num [pow_succ, pow_mul]

private lemma rescale_two_exp_eq_mul_exp :
    PowerSeries.rescale 2 (PowerSeries.exp ℚ) =
      PowerSeries.exp ℚ * PowerSeries.exp ℚ := by
  convert
    (PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) (1 : ℚ) 1).symm using 1 <;>
      norm_num

private lemma exp_mul_rescale_neg_one_exp :
    PowerSeries.exp ℚ * PowerSeries.rescale (-1) (PowerSeries.exp ℚ) = 1 := by
  simpa using
    (PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) (1 : ℚ) (-1))

private lemma fullBernoulliCoshFactorPS22_functional :
    fullBernoulliCoshFactorPS22 *
        (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) =
      PowerSeries.C 2 * PowerSeries.X * PowerSeries.exp ℚ := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one (A := ℚ)
  have hB2 := congrArg (PowerSeries.rescale (2 : ℚ)) hB
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at hB2
  have hfactor :
      PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1 =
        (PowerSeries.exp ℚ - 1) * (PowerSeries.exp ℚ + 1) := by
    rw [rescale_two_exp_eq_mul_exp]
    ring
  rw [fullBernoulliCoshFactorPS22]
  calc
    (PowerSeries.C 2 * bernoulliPowerSeries ℚ -
          PowerSeries.rescale 2 (bernoulliPowerSeries ℚ)) *
        (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) =
      PowerSeries.C 2 *
            (bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1)) *
          (PowerSeries.exp ℚ + 1) -
        PowerSeries.rescale 2 (bernoulliPowerSeries ℚ) *
          (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) := by
            rw [hfactor]
            ring
    _ = PowerSeries.C 2 * PowerSeries.X * (PowerSeries.exp ℚ + 1) -
        PowerSeries.C 2 * PowerSeries.X := by rw [hB, hB2]
    _ = PowerSeries.C 2 * PowerSeries.X * PowerSeries.exp ℚ := by ring

private lemma fullBernoulliCoshFactorPS22_mul_fullSinhDivPS22 :
    fullBernoulliCoshFactorPS22 * fullSinhDivPS22 = 1 := by
  have hne : PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1 ≠ 0 := by
    intro hzero
    have hcoeff := congrArg (PowerSeries.coeff 1) hzero
    norm_num [PowerSeries.coeff_rescale, PowerSeries.coeff_exp] at hcoeff
  apply mul_right_cancel₀ (b :=
    PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) hne
  calc
    (fullBernoulliCoshFactorPS22 * fullSinhDivPS22) *
          (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) =
        fullSinhDivPS22 *
          (fullBernoulliCoshFactorPS22 *
            (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1)) := by ring
    _ = fullSinhDivPS22 *
        (PowerSeries.C 2 * PowerSeries.X * PowerSeries.exp ℚ) := by
      rw [fullBernoulliCoshFactorPS22_functional]
    _ = PowerSeries.exp ℚ *
        (PowerSeries.C 2 * (PowerSeries.X * fullSinhDivPS22)) := by ring
    _ = PowerSeries.exp ℚ *
        (PowerSeries.exp ℚ -
          PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) := by
      rw [two_X_mul_fullSinhDivPS22]
    _ = PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1 := by
      rw [mul_sub, ← rescale_two_exp_eq_mul_exp,
        exp_mul_rescale_neg_one_exp]
    _ = 1 * (PowerSeries.rescale 2 (PowerSeries.exp ℚ) - 1) := by ring

private lemma bernoulliCoshFactorPS22_mul_sinhDivPS22 :
    bernoulliCoshFactorPS22 * sinhDivPS = 1 := by
  apply expand_two_injective
  rw [map_mul, expand_bernoulliCoshFactorPS22]
  simpa [fullSinhDivPS22] using
    fullBernoulliCoshFactorPS22_mul_fullSinhDivPS22

private lemma momentPS22_bernoulli_functional :
    momentPS =
      bernoulliCoshFactorPS22 * PowerSeries.rescale 4 momentPS := by
  calc
    momentPS = momentPS * 1 := by ring
    _ = momentPS * (bernoulliCoshFactorPS22 * sinhDivPS) := by
      rw [bernoulliCoshFactorPS22_mul_sinhDivPS22]
    _ = bernoulliCoshFactorPS22 * (momentPS * sinhDivPS) := by ring
    _ = bernoulliCoshFactorPS22 * PowerSeries.rescale 4 momentPS := by
      rw [momentPS_functional]

/-- The coefficient identity obtained by inverting the hyperbolic-sine factor
in the moment generating-series equation. -/
theorem moment_bernoulli_convolution (n : ℕ) :
    moment n =
      ∑ k ∈ range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℚ) * (2 : ℚ) ^ (2 * n - 2 * k) *
          ((2 : ℚ) - (2 : ℚ) ^ (2 * k)) * bernoulli (2 * k) *
            moment (n - k) := by
  have h := congrArg (PowerSeries.coeff n) momentPS22_bernoulli_functional
  simp only [PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, bernoulliCoshFactorPS22,
    PowerSeries.coeff_mk, PowerSeries.coeff_rescale, momentPS] at h
  calc
    moment n = ((2 * n).factorial : ℚ) *
        (moment n / ((2 * n).factorial : ℚ)) := by field_simp
    _ = ((2 * n).factorial : ℚ) *
        ∑ x ∈ range n.succ,
          ((2 - 4 ^ x) * bernoulli (2 * x) / ((2 * x).factorial : ℚ)) *
            (4 ^ (n - x) *
              (moment (n - x) / ((2 * (n - x)).factorial : ℚ))) := by
      simpa using congrArg (fun q : ℚ => ((2 * n).factorial : ℚ) * q) h
    _ = ∑ k ∈ range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℚ) * 2 ^ (2 * n - 2 * k) *
          (2 - 2 ^ (2 * k)) * bernoulli (2 * k) * moment (n - k) := by
      rw [mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (mem_range.1 hk)
      have hkle : 2 * k ≤ 2 * n := by
        omega
      have hsub : 2 * (n - k) = 2 * n - 2 * k := by omega
      have hpow : (4 : ℚ) ^ (n - k) = (2 : ℚ) ^ (2 * n - 2 * k) := by
        rw [← hsub]
        norm_num [pow_mul]
      rw [Nat.cast_choose ℚ hkle]
      rw [hsub, hpow]
      norm_num [pow_mul]
      field_simp

/-- Equation (38), the Bernoulli recurrence for the even moments. -/
theorem moment_bernoulli_recurrence (n : ℕ) (hn : 1 ≤ n) :
    moment n =
      (∑ k ∈ Icc 1 n,
        (2 : ℚ) ^ (2 * n - 2 * k) * ((2 : ℚ) ^ (2 * k) - 2) *
          Nat.choose (2 * n) (2 * k) * bernoulli (2 * k) * moment (n - k)) /
        ((2 : ℚ) ^ (2 * n) - 1) := by
  let g : ℕ → ℚ := fun k =>
    (2 : ℚ) ^ (2 * n - 2 * k) * ((2 : ℚ) ^ (2 * k) - 2) *
      Nat.choose (2 * n) (2 * k) * bernoulli (2 * k) * moment (n - k)
  have hconv := moment_bernoulli_convolution n
  have hneg :
      (∑ k ∈ range (n + 1),
        (Nat.choose (2 * n) (2 * k) : ℚ) * (2 : ℚ) ^ (2 * n - 2 * k) *
          ((2 : ℚ) - (2 : ℚ) ^ (2 * k)) * bernoulli (2 * k) *
            moment (n - k)) =
        -∑ k ∈ range (n + 1), g k := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp [g]
    ring
  rw [hneg] at hconv
  have hrangeErase : (range (n + 1)).erase 0 = Icc 1 n := by
    ext k
    simp
    omega
  have hsplit :
      (∑ k ∈ range (n + 1), g k) =
        g 0 + ∑ k ∈ Icc 1 n, g k := by
    have h := Finset.sum_erase_add (range (n + 1)) g
      (show 0 ∈ range (n + 1) by simp)
    rw [hrangeErase] at h
    simpa [add_comm] using h.symm
  have hg0 : g 0 = -((2 : ℚ) ^ (2 * n) * moment n) := by
    dsimp [g]
    norm_num
  rw [hsplit, hg0] at hconv
  have hpow := rat_two_pow_sub_one_ne_zero (2 * n) (by omega)
  field_simp [hpow]
  linear_combination -hconv

/-- All-index successor form of the even-moment Bernoulli recurrence. -/
theorem moment_bernoulli_succ_recurrence (n : ℕ) :
    moment (n + 1) =
      (∑ k ∈ Icc 1 (n + 1),
        (2 : ℚ) ^ (2 * (n + 1) - 2 * k) *
          ((2 : ℚ) ^ (2 * k) - 2) *
          Nat.choose (2 * (n + 1)) (2 * k) * bernoulli (2 * k) *
            moment (n + 1 - k)) /
        ((2 : ℚ) ^ (2 * (n + 1)) - 1) := by
  exact moment_bernoulli_recurrence (n + 1) (by omega)

/-- Both Bernoulli recurrences packaged in the conjunction used by Proposition
22 of the paper. -/
theorem proposition_twenty_two_formula (n : ℕ) (hn : 1 ≤ n) :
    moment n =
      (∑ k ∈ Icc 1 n,
        (2 : ℚ) ^ (2 * n - 2 * k) * ((2 : ℚ) ^ (2 * k) - 2) *
          Nat.choose (2 * n) (2 * k) * bernoulli (2 * k) * moment (n - k)) /
        ((2 : ℚ) ^ (2 * n) - 1) ∧
    halfMoment n =
      ((n : ℚ) * (2 : ℚ) ^ n / (4 * ((2 : ℚ) ^ n - 1))) *
          halfMoment (n - 1) -
        (∑ k ∈ Icc 1 (n / 2),
          (Nat.choose n (2 * k) : ℚ) * (2 : ℚ) ^ (n - 2 * k) *
            bernoulli (2 * k) * halfMoment (n - 2 * k)) /
          ((2 : ℚ) ^ n - 1) := by
  exact ⟨moment_bernoulli_recurrence n hn,
    halfMoment_bernoulli_recurrence n hn⟩

end Fabius

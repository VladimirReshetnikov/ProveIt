import GRHArticle.ProgressionFree.DensityBounds
import Mathlib.Algebra.BigOperators.Field

/-!
# Uniform tails for large prime powers

The reciprocal power tail is bounded by a telescoping difference of
reciprocal powers of one degree lower. The bound applies to every
finite sample.
-/

namespace GRHArticle.ProgressionFree

open Finset
open scoped BigOperators

private theorem mul_reciprocal_pow_le_difference (m : ℕ) {x : ℝ} (hx : 0 < x) :
    (m : ℝ)*(1/(x+1))^(m+1) ≤ (1/x)^m-(1/(x+1))^m := by
  let u : ℝ := 1/x
  let v : ℝ := 1/(x+1)
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hvu : v ≤ u := one_div_le_one_div_of_le hx (by linarith)
  have hsq : v^2 ≤ u-v := by
    have hx₁ : 0 < x+1 := by positivity
    have hdiff : u-v = 1/(x*(x+1)) := by
      dsimp [u,v]
      field_simp [hx.ne',hx₁.ne']
      ring
    dsimp [v]
    rw [hdiff,one_div_pow,pow_two]
    exact one_div_le_one_div_of_le (mul_pos hx hx₁) (mul_le_mul_of_nonneg_right (by linarith) hx₁.le)
  change (m:ℝ)*v^(m+1) ≤ u^m-v^m
  induction m with
  | zero => simp
  | succ m ih =>
    have hpow : v^m ≤ u^m := pow_le_pow_left₀ hv hvu _
    have h₁ : v^m * v^2 ≤ u^m * (u-v) :=
      mul_le_mul hpow hsq (sq_nonneg _) (pow_nonneg (hv.trans hvu) _)
    have h₂ := mul_le_mul_of_nonneg_left ih hv
    calc
      _ = v^m*v^2 + v*((m:ℝ)*v^(m+1)) := by
        simp only [Nat.cast_succ,pow_succ]
        ring
      _ ≤ u^m*(u-v) + v*(u^m-v^m) := add_le_add h₁ h₂
      _ = _ := by simp only [pow_succ]; ring

/-- Reciprocal powers over an interval are bounded by the elementary
telescoping tail used in the bounded-block loss estimate. -/
theorem sum_Ioc_one_div_pow_le (Y N m : ℕ) (hY : 0 < Y) (hm : 0 < m) :
    (∑ q ∈ Ioc Y N, 1/(q : ℝ)^(m+1)) ≤ 1/((m : ℝ)*(Y : ℝ)^m) := by
  by_cases hYN : Y ≤ N
  · have he : Ico (Y+1) (N+1) = Ioc Y N := by
      ext q
      simp only [mem_Ico,mem_Ioc]
      omega
    have hs := sum_Ico_add' (fun q : ℕ ↦ 1/(q : ℝ)^(m+1)) Y N 1
    rw [he] at hs
    rw [← hs]
    have hm₀ : (0 : ℝ) < m := by exact_mod_cast hm
    calc
      _ ≤ ∑ q ∈ Ico Y N, (1/(q : ℝ)^m - 1/((q+1 : ℕ) : ℝ)^m)/(m : ℝ) := by
        apply sum_le_sum
        intro q hq
        have hq₀ : (0 : ℝ) < q := by exact_mod_cast hY.trans_le (mem_Ico.mp hq).1
        have h := mul_reciprocal_pow_le_difference m hq₀
        simp only [one_div_pow] at h
        apply (le_div_iff₀ hm₀).mpr
        simpa only [Nat.cast_add,Nat.cast_one,mul_comm] using h
      _ = (1/(Y : ℝ)^m - 1/(N : ℝ)^m)/(m : ℝ) := by
        rw [← sum_div]
        have ht := sum_Ico_sub (fun q : ℕ ↦ 1/(q : ℝ)^m) hYN
        rw [show (∑ q ∈ Ico Y N, (1/(q : ℝ)^m - 1/((q+1 : ℕ) : ℝ)^m)) =
            -(∑ q ∈ Ico Y N, (1/((q+1 : ℕ) : ℝ)^m - 1/(q : ℝ)^m)) by
          simp only [← sum_neg_distrib,neg_sub], ht, neg_sub]
      _ ≤ (1/(Y : ℝ)^m)/(m : ℝ) := div_le_div_of_nonneg_right
        (sub_le_self _ (by positivity)) hm₀.le
      _ = _ := by rw [div_div,mul_comm ((Y : ℝ)^m)]
  · rw [Ioc_eq_empty_of_le (by omega),sum_empty]
    positivity

/-- Uniform density bound for multiples of large prime powers. -/
theorem densityUpTo_largePrimePower_le (Y N m : ℕ) (hY : 0 < Y) (hm : 0 < m) :
    densityUpTo {n | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p^(m+1) ∣ n} N ≤
      1/((m : ℝ)*(Y : ℝ)^m) := by
  calc
    _ ≤ densityUpTo {n | ∃ p ∈ Ioc Y N, p^(m+1) ∣ n} N := by
      apply densityUpTo_le_of_subset_on_cutoff N
      rintro n hn ⟨p,hpY,hp,hD⟩
      have hpN := (Nat.le_of_dvd (mem_Icc.mp hn).1
        ((dvd_pow_self p (show m+1 ≠ 0 by omega)).trans hD)).trans (mem_Icc.mp hn).2
      exact ⟨p,mem_Ioc.mpr ⟨hpY,hpN⟩,hD⟩
    _ ≤ ∑ p ∈ Ioc Y N, 1/(p : ℝ)^(m+1) := by
      simpa only [Nat.cast_pow] using densityUpTo_divisibleByOneOf_le (Ioc Y N)
        (fun p ↦ p^(m+1)) N (fun p hp ↦ pow_pos (hY.trans (mem_Ioc.mp hp).1) _)
    _ ≤ _ := sum_Ioc_one_div_pow_le Y N m hY hm

/-- When the cutoff is even and positive, all remaining primes are odd.
Telescoping the odd reciprocal-square tail gives the sharper bound used
for triples. -/
theorem densityUpTo_largePrimeSquare_even_cutoff_le (K N : ℕ) (hK : 0 < K) :
    densityUpTo {n | ∃ p : ℕ, 2*K < p ∧ p.Prime ∧ p^2 ∣ n} N ≤ 1/(4*(K : ℝ)) := by
  calc
    _ ≤ densityUpTo {n | ∃ j ∈ Icc K N, (2*j+1)^2 ∣ n} N := by
      apply densityUpTo_le_of_subset_on_cutoff N
      rintro n hn ⟨p,hpK,hp,hd⟩
      have hpN := (Nat.le_of_dvd (mem_Icc.mp hn).1
        ((dvd_pow_self p (show (2 : ℕ) ≠ 0 by decide)).trans hd)).trans (mem_Icc.mp hn).2
      obtain ⟨j,hj⟩ := hp.odd_of_ne_two (by omega)
      have hEq : p = 2*j+1 := by simpa only [two_mul] using hj
      exact ⟨j,mem_Icc.mpr ⟨by omega,by omega⟩,hEq ▸ hd⟩
    _ ≤ ∑ j ∈ Icc K N, 1/(2*(j : ℝ)+1)^2 := by
      simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using
        densityUpTo_divisibleByOneOf_le (Icc K N) (fun j ↦ (2*j+1)^2) N
          (fun j _ ↦ pow_pos (by omega) _)
    _ ≤ _ := by
      by_cases hKN : K ≤ N
      · have hI : Icc K N = Ico K (N+1) := by
          ext j
          simp only [mem_Icc,mem_Ico]
          omega
        rw [hI]
        calc
          _ ≤ ∑ j ∈ Ico K (N+1), (1/(j : ℝ)-1/((j+1 : ℕ) : ℝ))/4 := by
            apply sum_le_sum
            intro j hj
            have ht : (0 : ℝ) < j := by exact_mod_cast hK.trans_le (mem_Ico.mp hj).1
            have ht' : (0 : ℝ) < (j:ℝ)+1 := by positivity
            have he : (1/(j : ℝ)-1/((j+1 : ℕ) : ℝ))/4 = 1/(4*(j:ℝ)*((j:ℝ)+1)) := by
              push_cast
              field_simp [ht.ne',ht'.ne']
              ring
            rw [he]
            exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
          _ = (1/(K : ℝ)-1/((N+1 : ℕ) : ℝ))/4 := by
            rw [← sum_div]
            have ht := sum_Ico_sub (fun j : ℕ ↦ 1/(j : ℝ)) (hKN.trans (Nat.le_succ N))
            rw [show (∑ j ∈ Ico K (N+1), (1/(j : ℝ)-1/((j+1 : ℕ) : ℝ))) =
                -(∑ j ∈ Ico K (N+1), (1/((j+1 : ℕ) : ℝ)-1/(j : ℝ))) by
              simp only [← sum_neg_distrib,neg_sub],ht,neg_sub]
          _ ≤ (1/(K : ℝ))/4 := div_le_div_of_nonneg_right
            (sub_le_self _ (by positivity)) (by norm_num)
          _ = _ := by rw [div_div,mul_comm (K : ℝ)]
      · rw [Icc_eq_empty (by omega),sum_empty]
        positivity

end GRHArticle.ProgressionFree

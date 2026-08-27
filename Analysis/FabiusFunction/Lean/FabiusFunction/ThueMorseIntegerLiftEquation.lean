import FabiusFunction.ThueMorseCatalanConvolution
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# The algebraic equation of the integral lift

The constructed sequence `c(n) = ∑ (-1)^(k-1)·Cat(k-1)·C(n,k)` really
does satisfy the atlas's algebraic equation: with
`C(z) = ∑ c(n)·zⁿ` in `ℤ⟦z⟧`,

`(1-z)³·C(z)² + (1-z)²·C(z) = z`.

The finite results compose: the second-difference bridge identifies
`(1-z)²·C(z)` with the substituted Catalan series `A`, the convolution
identity gives `A² + (1-z)·A = z·(1-z)` coefficientwise, and
cancelling the non-zero-divisor `1-z` finishes.

* `integerLiftSeries` / `catalanSubstSeries` — `C(z)` and `A(z)`.
* `catalanSubstSeries_eq` — `(1-X)²·C = A`.
* `catalanSubstSeries_quadratic` — `A² + (1-X)·A = X·(1-X)`.
* `integerLiftSeries_algebraic` — **the boxed equation**
  (`eq:integer-lift-algebraic`).
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-- The generating series `C(z)` of the integral lift. -/
noncomputable def integerLiftSeries : PowerSeries ℤ :=
  PowerSeries.mk integerLift

/-- The shifted substituted-Catalan series `A(z) = (1-z)²·C(z)`:
`a(0) = 0` and `a(n) = h(n-1)`. -/
noncomputable def catalanSubstSeries : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 0 else catalanSeriesDelta (n - 1)

/-- The sequence-level bridge in all degrees. -/
private theorem coeff_delta_all (n : ℕ) :
    integerLift n - 2 * integerLift (n - 1) + integerLift (n - 2) =
      if n = 0 then 0 else catalanSeriesDelta (n - 1) := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp
    · rw [if_neg (by omega)]
      simp [integerLift_one, catalanSeriesDelta_zero]
  · rw [if_neg (by omega)]
    exact integerLift_delta_bridge n hn

/-- `(1-X)²·C = A`. -/
theorem catalanSubstSeries_eq :
    (1 - X : PowerSeries ℤ) ^ 2 * integerLiftSeries = catalanSubstSeries := by
  have hexp : (1 - X : PowerSeries ℤ) ^ 2 * integerLiftSeries =
      integerLiftSeries -
        (PowerSeries.C (R := ℤ)) 2 * (X * integerLiftSeries) +
        X ^ 2 * integerLiftSeries := by
    have h2 : ((PowerSeries.C (R := ℤ)) 2 : PowerSeries ℤ) = 2 :=
      map_ofNat _ 2
    rw [h2]
    ring
  rw [hexp]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, catalanSubstSeries,
    PowerSeries.coeff_mk]
  have hXC : (PowerSeries.coeff n) (X * integerLiftSeries) =
      if n = 0 then 0 else integerLift (n - 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl]
      exact PowerSeries.coeff_zero_X_mul _
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      rw [if_neg (by omega), PowerSeries.coeff_succ_X_mul,
        integerLiftSeries, PowerSeries.coeff_mk, Nat.add_sub_cancel]
  have hX2C : (PowerSeries.coeff n) (X ^ 2 * integerLiftSeries) =
      if 2 ≤ n then integerLift (n - 2) else 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with h
    · rw [integerLiftSeries, PowerSeries.coeff_mk]
    · rfl
  have hguard : (if 2 ≤ n then integerLift (n - 2) else 0) =
      integerLift (n - 2) := by
    split_ifs with h
    · rfl
    · rw [show n - 2 = 0 by omega, integerLift_zero]
  have hXguard : (if n = 0 then 0 else integerLift (n - 1)) =
      integerLift (n - 1) := by
    split_ifs with h
    · subst h
      rw [show (0 : ℕ) - 1 = 0 from rfl, integerLift_zero]
    · rfl
  rw [hXC, hX2C, hguard, hXguard, integerLiftSeries, PowerSeries.coeff_mk]
  exact coeff_delta_all n

/-- The quadratic identity `A² + (1-X)·A = X·(1-X)`, coefficientwise
from the convolution identity of the substituted Catalan series. -/
theorem catalanSubstSeries_quadratic :
    catalanSubstSeries ^ 2 + (1 - X : PowerSeries ℤ) * catalanSubstSeries =
      X * (1 - X) := by
  have hexpand : catalanSubstSeries ^ 2 +
      (1 - X : PowerSeries ℤ) * catalanSubstSeries =
      catalanSubstSeries * catalanSubstSeries + catalanSubstSeries -
        X * catalanSubstSeries := by
    ring
  have hrhs : (X : PowerSeries ℤ) * (1 - X) = X - X ^ 2 := by
    ring
  rw [hexpand, hrhs]
  ext n
  simp only [map_add, map_sub]
  have hmul : (PowerSeries.coeff n)
      (catalanSubstSeries * catalanSubstSeries) =
      ∑ p ∈ range (n + 1),
        (if p = 0 then 0 else catalanSeriesDelta (p - 1)) *
          (if n - p = 0 then 0 else catalanSeriesDelta (n - p - 1)) := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [catalanSubstSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mk]
  have hXA : (PowerSeries.coeff n) (X * catalanSubstSeries) =
      if n = 0 then 0 else
        (if n - 1 = 0 then 0 else catalanSeriesDelta (n - 1 - 1)) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl]
      exact PowerSeries.coeff_zero_X_mul _
    · obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
      rw [if_neg (by omega), PowerSeries.coeff_succ_X_mul,
        catalanSubstSeries, PowerSeries.coeff_mk, Nat.add_sub_cancel]
  rw [hmul, hXA, catalanSubstSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_X, PowerSeries.coeff_X_pow]
  rcases Nat.lt_or_ge n 3 with hn | hn
  · interval_cases n
    · rw [Finset.sum_range_one]
      norm_num
    · rw [Finset.sum_range_succ, Finset.sum_range_one]
      norm_num [catalanSeriesDelta_zero]
    · rw [Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one]
      norm_num [catalanSeriesDelta_zero, catalanSeriesDelta_one]
  · -- `n ≥ 3`: the pure convolution regime
    have hconv := catalanSeriesDelta_conv (n - 2)
    rw [if_neg (by omega)] at hconv
    have hshift : ∑ p ∈ range (n + 1),
        (if p = 0 then 0 else catalanSeriesDelta (p - 1)) *
          (if n - p = 0 then 0 else catalanSeriesDelta (n - p - 1)) =
        ∑ q ∈ range (n - 2 + 1),
          catalanSeriesDelta q * catalanSeriesDelta (n - 2 - q) := by
      have hsub : Icc 1 (n - 1) ⊆ range (n + 1) := by
        intro p hp
        have := Finset.mem_Icc.mp hp
        exact Finset.mem_range.mpr (by omega)
      have hvan : ∀ p ∈ range (n + 1), p ∉ Icc 1 (n - 1) →
          (if p = 0 then 0 else catalanSeriesDelta (p - 1)) *
            (if n - p = 0 then 0 else catalanSeriesDelta (n - p - 1)) = 0 := by
        intro p hp hnot
        have h1 := Finset.mem_range.mp hp
        rcases Nat.eq_zero_or_pos p with rfl | hpos
        · rw [if_pos rfl, zero_mul]
        · have hn' : n ≤ p := by
            by_contra hcon
            exact hnot (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
          rw [if_pos (by omega : n - p = 0), mul_zero]
      calc ∑ p ∈ range (n + 1),
            (if p = 0 then 0 else catalanSeriesDelta (p - 1)) *
              (if n - p = 0 then 0 else catalanSeriesDelta (n - p - 1))
          = ∑ p ∈ Icc 1 (n - 1),
              (if p = 0 then 0 else catalanSeriesDelta (p - 1)) *
                (if n - p = 0 then 0 else catalanSeriesDelta (n - p - 1)) :=
            (Finset.sum_subset hsub hvan).symm
        _ = ∑ p ∈ Icc 1 (n - 1),
              catalanSeriesDelta (p - 1) * catalanSeriesDelta (n - p - 1) := by
            refine Finset.sum_congr rfl fun p hp => ?_
            have := Finset.mem_Icc.mp hp
            rw [if_neg (by omega), if_neg (by omega)]
        _ = ∑ q ∈ range (n - 2 + 1),
              catalanSeriesDelta q * catalanSeriesDelta (n - 2 - q) := by
            rw [← Finset.Ico_add_one_right_eq_Icc,
              Finset.sum_Ico_eq_sum_range]
            refine Finset.sum_congr (by congr 1; omega)
              fun i hi => ?_
            rw [show 1 + i - 1 = i by omega,
              show n - (1 + i) - 1 = n - 2 - i by omega]
    rw [hshift, hconv]
    rw [if_neg (by omega : ¬n = 0), if_neg (by omega : ¬n - 1 = 0),
      if_neg (by omega : ¬n = 1), if_neg (by omega : ¬n = 2)]
    rw [show n - 1 - 1 = n - 2 by omega,
      show n - 2 + 1 = n - 1 by omega]
    rw [if_neg (by omega : ¬ n = 0)]
    ring

/-- **The algebraic equation of the integral lift**
(`eq:integer-lift-algebraic`): in `ℤ⟦z⟧`,
`(1-z)³·C(z)² + (1-z)²·C(z) = z` for the constructed series. -/
theorem integerLiftSeries_algebraic :
    (1 - X : PowerSeries ℤ) ^ 3 * integerLiftSeries ^ 2 +
      (1 - X) ^ 2 * integerLiftSeries = X := by
  have hne : (1 - X : PowerSeries ℤ) ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.constantCoeff (R := ℤ)) h
    simp only [map_sub, map_one, PowerSeries.constantCoeff_X, map_zero,
      sub_zero] at hc
    exact one_ne_zero hc
  apply mul_left_cancel₀ hne
  calc (1 - X : PowerSeries ℤ) *
        ((1 - X) ^ 3 * integerLiftSeries ^ 2 +
          (1 - X) ^ 2 * integerLiftSeries)
      = ((1 - X) ^ 2 * integerLiftSeries) ^ 2 +
          (1 - X) * ((1 - X) ^ 2 * integerLiftSeries) := by ring
    _ = catalanSubstSeries ^ 2 + (1 - X) * catalanSubstSeries := by
        rw [catalanSubstSeries_eq]
    _ = X * (1 - X) := catalanSubstSeries_quadratic
    _ = (1 - X) * X := by ring

end Fabius

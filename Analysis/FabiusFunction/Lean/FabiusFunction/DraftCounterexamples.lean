import FabiusFunction.Basic
import FabiusFunction.ThueMorsePrefix
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Counterexamples to claims in the K-fold Thue--Morse draft

This file records two obstructions in
`Papers/K-fold summation over the signed Thue-Morse sequence/` while preserving
the draft's definitions literally.

* Equation (7) proposes the maximum, over `n ≥ 1`, of
  `(2^n x)^n / (n! 2^(choose n 2))` as a proxy for the Fabius function near
  zero.  Its successive-term ratio is `x * 2^(n+1) / (n+1)`, which tends to
  infinity for every `x > 0`.  Thus the displayed terms are unbounded and the
  proposed maximum does not exist (even if the index `n = 0` is omitted).
* Section 3 claims a uniform local error bounded by `4h` for the normalized
  polygonal curves from equation (1).  With the stated inclusive prefix sums,
  at `k = 2`, `j = 1` the grid slope is `-2`, whereas every bounded Fabius
  function has derivative `1` at `1/4`.  The error is therefore `3`, while
  `4h = 1`.

These are counterexamples to the printed normalization and proxy, not to a
subsequently corrected approximation scheme.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset Set

namespace Fabius

/-- The term displayed under the maximum in equation (7) of the K-fold draft. -/
noncomputable def paperProxyTerm (x : ℝ) (n : ℕ) : ℝ :=
  (((2 : ℝ) ^ n * x) ^ n) /
    ((n.factorial : ℝ) * (2 : ℝ) ^ n.choose 2)

private lemma choose_succ_two (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  rw [show n + 1 = Nat.succ n by omega, Nat.choose_succ_succ]
  simp [Nat.choose_one_right, add_comm]

/-- The exact successive-term ratio of the proxy in equation (7). -/
theorem paperProxyTerm_succ (x : ℝ) (n : ℕ) :
    paperProxyTerm x (n + 1) =
      paperProxyTerm x n * (x * (2 : ℝ) ^ (n + 1) / (n + 1)) := by
  rw [paperProxyTerm, paperProxyTerm, choose_succ_two]
  rw [Nat.factorial_succ]
  push_cast
  rw [pow_add]
  field_simp
  ring

/-- The successive-term ratio tends to infinity at every positive argument. -/
theorem paperProxyRatio_tendsto_atTop {x : ℝ} (hx : 0 < x) :
    Filter.Tendsto
      (fun n : ℕ => x * (2 : ℝ) ^ (n + 1) / (n + 1))
      Filter.atTop Filter.atTop := by
  have hzero0 :
      Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 1 / (2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num)
  have hzero :
      Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
        Filter.atTop (nhds 0) := by
    convert hzero0.comp (Filter.tendsto_add_atTop_nat 1) using 1
    ext n
    simp
  have hwithin :
      Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1))
        Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hzero, Filter.Eventually.of_forall (fun n => by
      simp only [Set.mem_Ioi]
      positivity)⟩
  have hinv := hwithin.inv_tendsto_nhdsGT_zero
  have hmul := hinv.const_mul_atTop hx
  have hmul' :
      Filter.Tendsto
        (fun n : ℕ => x * ((2 : ℝ) ^ (n + 1) / ((n + 1 : ℕ) : ℝ)))
        Filter.atTop Filter.atTop := by
    simpa only [Pi.inv_apply, inv_div] using hmul
  simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using hmul'

lemma paperProxyTerm_pos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    0 < paperProxyTerm x n := by
  unfold paperProxyTerm
  positivity

private theorem paperProxyTerm_unbounded_all {x : ℝ} (hx : 0 < x) :
    ∀ B : ℝ, ∃ n : ℕ, B < paperProxyTerm x n := by
  have hratio := (paperProxyRatio_tendsto_atTop hx).eventually_ge_atTop (2 : ℝ)
  rcases Filter.eventually_atTop.1 hratio with ⟨N, hN⟩
  have hgrowth : ∀ m : ℕ,
      paperProxyTerm x N * (2 : ℝ) ^ m ≤ paperProxyTerm x (N + m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [pow_succ]
        calc
          paperProxyTerm x N * ((2 : ℝ) ^ m * 2) =
              (paperProxyTerm x N * (2 : ℝ) ^ m) * 2 := by ring
          _ ≤ paperProxyTerm x (N + m) * 2 :=
            mul_le_mul_of_nonneg_right ih (by norm_num)
          _ ≤ paperProxyTerm x (N + m) *
              (x * (2 : ℝ) ^ (N + m + 1) /
                (((N + m : ℕ) : ℝ) + 1)) := by
            exact mul_le_mul_of_nonneg_left (hN (N + m) (Nat.le_add_right N m))
              (paperProxyTerm_pos hx _).le
          _ = paperProxyTerm x (N + m + 1) :=
            (paperProxyTerm_succ x (N + m)).symm
          _ = paperProxyTerm x (N + Nat.succ m) := by congr 1
  intro B
  have hpow :
      Filter.Tendsto (fun m : ℕ => paperProxyTerm x N * (2 : ℝ) ^ m)
        Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (α := ℝ) (by norm_num)).const_mul_atTop
      (paperProxyTerm_pos hx N)
  rcases (hpow.eventually_ge_atTop (B + 1)).exists with ⟨m, hm⟩
  exact ⟨N + m, lt_of_lt_of_le (by linarith) (hm.trans (hgrowth m))⟩

/-- Equation (7)'s proxy terms with the printed restriction `n ≥ 1` are
unbounded above for every positive `x`. -/
theorem paperProxyTerm_unbounded {x : ℝ} (hx : 0 < x) :
    ∀ B : ℝ, ∃ n : ℕ, 1 ≤ n ∧ B < paperProxyTerm x n := by
  intro B
  rcases paperProxyTerm_unbounded_all hx (max B (paperProxyTerm x 0)) with ⟨n, hn⟩
  have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.2 fun hnzero => by
    subst n
    exact (not_lt_of_ge (le_max_right B (paperProxyTerm x 0))) hn
  exact ⟨n, hnpos, (le_max_left B (paperProxyTerm x 0)).trans_lt hn⟩

/-- Consequently, the displayed `max` over `n ≥ 1` in equation (7) does not exist. -/
theorem paperProxyTerm_has_no_maximum {x : ℝ} (hx : 0 < x) :
    ¬ ∃ n : ℕ, 1 ≤ n ∧
      ∀ m : ℕ, 1 ≤ m → paperProxyTerm x m ≤ paperProxyTerm x n := by
  rintro ⟨n, hnpos, hn⟩
  rcases paperProxyTerm_unbounded hx (paperProxyTerm x n) with ⟨m, hmpos, hm⟩
  exact (not_lt_of_ge (hn m hmpos)) hm

/-- Equation (1)'s literal normalized value at the `j`-th dyadic grid point. -/
def literalPrefixGrid (k j : ℕ) : ℚ :=
  (iteratedPrefix k j : ℚ) / (2 : ℚ) ^ k.choose 2

/-- The forward slope of the polygon joining consecutive literal grid values. -/
def literalGridSlope (k j : ℕ) : ℚ :=
  (2 : ℚ) ^ k * (literalPrefixGrid k (j + 1) - literalPrefixGrid k j)

@[simp] private lemma thueMorseSign_zero : thueMorseSign 0 = 1 := by
  norm_num [thueMorseSign, binaryWeight, Nat.digits_zero]

@[simp] private lemma thueMorseSign_one : thueMorseSign 1 = -1 := by
  simpa using thueMorseSign_two_mul_add_one 0

@[simp] private lemma thueMorseSign_two : thueMorseSign 2 = -1 := by
  simpa using thueMorseSign_two_mul 1

/-- At `k = 2`, `j = 1`, the literal polygonal grid slope is `-2`. -/
theorem literalGridSlope_two_one : literalGridSlope 2 1 = -2 := by
  norm_num [literalGridSlope, literalPrefixGrid, iteratedPrefix, Finset.sum_range_succ]

private lemma fabius_half (F : BoundedFabius) (hF : IsFabius F) :
    fabiusReal F (1 / 2) = 1 / 2 := by
  have h := hF.symmetry (1 / 2) (by constructor <;> norm_num)
  norm_num at h ⊢
  linarith

private lemma fabius_deriv_quarter (F : BoundedFabius) (hF : IsFabius F) :
    deriv (fabiusReal F) (1 / 4) = 1 := by
  rw [(hF.hasDerivAt (1 / 4) (by constructor <;> norm_num)).deriv]
  rw [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num, fabius_half F hF]
  norm_num

/-- At `k = 2`, `j = 1`, the claimed Section 3 error is `3`, but `4h = 1`. -/
theorem literal_local_error_bound_false
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ |(literalGridSlope 2 1 : ℝ) - deriv (fabiusReal F) (1 / 4)| ≤
      4 * ((2 : ℝ) ^ 2)⁻¹ := by
  rw [literalGridSlope_two_one, fabius_deriv_quarter F hF]
  norm_num

end Fabius

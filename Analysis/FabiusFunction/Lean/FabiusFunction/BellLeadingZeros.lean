import FabiusFunction.BellGeneratingFunctions

/-!
# Partial Bell polynomials with leading zeros

Inserting `q` leading zeros into the weights rescales the partial Bell polynomials:

`B_{n,k}(x_{q+1}/C(q+1,q), x_{q+2}/C(q+2,q), …)
  = n! (q!)^k / (n+qk)! · B_{n+qk,k}(0, …, 0, x_{q+1}, x_{q+2}, …)`.

The weight series of the zero-padded weights is `t^q/q!` times the weight
series of the rescaled weights, so the `k`-th powers differ by `t^{qk}/(q!)^k`,
and the coefficients of `t^{n+qk}/(n+qk)!` and `t^n/n!` compare as stated.

## Main results

* `leadingZeros`, `qScaled`, `bellWeightSeries_leadingZeros`.
* `partialBell_leadingZeros`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The weights `x` with their first `q` entries replaced by zero. -/
def leadingZeros (x : ℕ → A) (q : ℕ) : ℕ → A := fun j => if j ≤ q then 0 else x j

/-- The rescaled weights `i ↦ x_{q+i} / C(q+i, q)`. -/
noncomputable def qScaled (x : ℕ → A) (q : ℕ) : ℕ → A :=
  fun i => algebraMap ℚ A (1 / ((q + i).choose q : ℚ)) * x (q + i)

/-- The weight series of the zero-padded weights is `t^q/q!` times the weight
series of the rescaled weights. -/
theorem bellWeightSeries_leadingZeros (x : ℕ → A) (q : ℕ) :
    bellWeightSeries A (leadingZeros A x q) =
      X ^ q * (PowerSeries.C (algebraMap ℚ A (1 / q.factorial)) *
        bellWeightSeries A (qScaled A x q)) := by
  ext m
  rcases Nat.lt_or_ge m q with hlt | hge
  · rw [coeff_X_pow_mul', if_neg (by omega), bellWeightSeries, coeff_egfA]
    simp [leadingZeros, hlt.le]
  · obtain ⟨i, rfl⟩ : ∃ i, m = q + i := ⟨m - q, by omega⟩
    rw [coeff_X_pow_mul', if_pos (Nat.le_add_right q i), Nat.add_sub_cancel_left, coeff_C_mul,
      bellWeightSeries, bellWeightSeries, coeff_egfA, coeff_egfA]
    cases i with
    | zero => simp [leadingZeros]
    | succ i =>
      simp only [leadingZeros, qScaled, show ¬ (q + (i + 1) ≤ q) by omega,
        show q + (i + 1) ≠ 0 by omega, Nat.succ_ne_zero, if_false]
      have hc : ((q + (i + 1)).choose q : ℚ) * q.factorial * (i + 1).factorial =
          (q + (i + 1)).factorial := by
        rw [Nat.choose_symm_add]
        exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial q (i + 1)
      have hC : ((q + (i + 1)).choose q : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.choose_pos (Nat.le_add_right q (i + 1))).ne'
      have hq : (q.factorial : ℚ) ≠ 0 := by positivity
      have hi : ((i + 1).factorial : ℚ) ≠ 0 := by positivity
      have key : algebraMap ℚ A (1 / q.factorial) * (algebraMap ℚ A (1 / (i + 1).factorial) *
          algebraMap ℚ A (1 / ((q + (i + 1)).choose q : ℚ)))
          = algebraMap ℚ A (1 / (q + (i + 1)).factorial) := by
        rw [← map_mul, ← map_mul, ← hc]
        congr 1
        field_simp
      calc algebraMap ℚ A (1 / (q + (i + 1)).factorial) * x (q + (i + 1))
          = (algebraMap ℚ A (1 / q.factorial) * (algebraMap ℚ A (1 / (i + 1).factorial) *
              algebraMap ℚ A (1 / ((q + (i + 1)).choose q : ℚ)))) * x (q + (i + 1)) := by
            rw [key]
        _ = _ := by ring

/-- **Insertion of `q` leading zeros:**
`B_{n,k}(x_{q+1}/C(q+1,q), x_{q+2}/C(q+2,q), …) = n!(q!)^k/(n+qk)! · B_{n+qk,k}(0,…,0,x_{q+1},…)`. -/
theorem partialBell_leadingZeros (x : ℕ → A) (q n k : ℕ) :
    partialBell (qScaled A x q) n k =
      algebraMap ℚ A ((n.factorial : ℚ) * q.factorial ^ k / (n + q * k).factorial) *
        partialBell (leadingZeros A x q) (n + q * k) k := by
  have h : coeff (n + q * k) (bellWeightSeries A (leadingZeros A x q) ^ k) =
      coeff (n + q * k) ((X ^ q * (PowerSeries.C (algebraMap ℚ A (1 / q.factorial)) *
        bellWeightSeries A (qScaled A x q))) ^ k) := by
    rw [bellWeightSeries_leadingZeros]
  rw [mul_pow, ← pow_mul, mul_pow, ← map_pow, coeff_X_pow_mul', if_pos (Nat.le_add_left _ _),
    Nat.add_sub_cancel, coeff_C_mul, bellWeightSeries_pow, bellWeightSeries_pow,
    PowerSeries.coeff_smul, PowerSeries.coeff_smul, coeff_egfA, coeff_egfA, smul_eq_mul,
    smul_eq_mul] at h
  have hk : algebraMap ℚ A (1 / k.factorial) * (k.factorial : A) = 1 := by
    rw [show (k.factorial : A) = algebraMap ℚ A (k.factorial : ℚ) by simp, ← map_mul,
      one_div_mul_cancel (by positivity), map_one]
  have key : algebraMap ℚ A (1 / (n + q * k).factorial) *
      partialBell (leadingZeros A x q) (n + q * k) k
      = algebraMap ℚ A (1 / q.factorial) ^ k *
        (algebraMap ℚ A (1 / n.factorial) * partialBell (qScaled A x q) n k) := by
    calc algebraMap ℚ A (1 / (n + q * k).factorial) *
          partialBell (leadingZeros A x q) (n + q * k) k
        = algebraMap ℚ A (1 / k.factorial) * ((k.factorial : A) *
            (algebraMap ℚ A (1 / (n + q * k).factorial) *
              partialBell (leadingZeros A x q) (n + q * k) k)) := by
          rw [← mul_assoc, hk, one_mul]
      _ = algebraMap ℚ A (1 / k.factorial) * (algebraMap ℚ A (1 / q.factorial) ^ k *
            ((k.factorial : A) * (algebraMap ℚ A (1 / n.factorial) *
              partialBell (qScaled A x q) n k))) := by rw [h]
      _ = (algebraMap ℚ A (1 / k.factorial) * (k.factorial : A)) *
            (algebraMap ℚ A (1 / q.factorial) ^ k *
              (algebraMap ℚ A (1 / n.factorial) * partialBell (qScaled A x q) n k)) := by ring
      _ = _ := by rw [hk, one_mul]
  have hn : algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (1 / n.factorial) = 1 := by
    rw [← map_mul, mul_one_div_cancel (by positivity), map_one]
  have hq : algebraMap ℚ A (q.factorial : ℚ) ^ k * algebraMap ℚ A (1 / q.factorial) ^ k = 1 := by
    rw [← mul_pow, ← map_mul, mul_one_div_cancel (by positivity), map_one, one_pow]
  calc partialBell (qScaled A x q) n k
      = (algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (1 / n.factorial)) *
          ((algebraMap ℚ A (q.factorial : ℚ) ^ k * algebraMap ℚ A (1 / q.factorial) ^ k) *
            partialBell (qScaled A x q) n k) := by rw [hn, hq]; ring
    _ = algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (q.factorial : ℚ) ^ k *
          (algebraMap ℚ A (1 / q.factorial) ^ k *
            (algebraMap ℚ A (1 / n.factorial) * partialBell (qScaled A x q) n k)) := by ring
    _ = algebraMap ℚ A (n.factorial : ℚ) * algebraMap ℚ A (q.factorial : ℚ) ^ k *
          (algebraMap ℚ A (1 / (n + q * k).factorial) *
            partialBell (leadingZeros A x q) (n + q * k) k) := by rw [key]
    _ = _ := by
        rw [← map_pow, ← map_mul, ← mul_assoc, ← map_mul]
        congr 2
        ring

end Fabius

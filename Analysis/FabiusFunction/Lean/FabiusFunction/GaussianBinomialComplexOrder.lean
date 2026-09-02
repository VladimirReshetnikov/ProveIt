import FabiusFunction.GaussianBinomialInteger
import FabiusFunction.QPochhammerComplexOrder

/-!
# Gaussian coefficients with a complex upper parameter, and generalized `q`-binomial series

With the principal branch of `q^α`, the **complex upper-parameter Gaussian coefficient** is

`[α,k]_q = (q^{α-k+1};q)_k / (q;q)_k`.

At an integer parameter it is the integer-index coefficient of `gaussianBinomialZ`.  Three
specializations of Euler's infinite `q`-binomial theorem are recorded in this language:

* the **upper-parameter series** `(q^{α+1}z;q)_∞/(z;q)_∞ = ∑_k [α+k,k]_q z^k`  (`a = q^{α+1}`);
* the **generalized reciprocal theorem** `1/(z;q)_α = ∑_k [α+k-1,k]_q z^k`  (`a = q^α`);
* the **generalized finite theorem** `(z;q)_α = ∑_k (-1)^k q^{C(k,2)} [α,k]_q z^k`
  (`a = q^{-α}` at the argument `zq^α`, followed by base reversal of the numerator).

Here `(z;q)_α = (z;q)_∞/(zq^α;q)_∞` is the complex-order symbol `qPochhammerC`.

## Main declarations

* `gaussianBinomialC`, `gaussianBinomialC_intCast`, `gaussianBinomialC_natCast`.
* `hasSum_gaussianBinomialC_add`, `hasSum_qPochhammerC_inv`, `hasSum_qPochhammerC`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

/-- **The Gaussian coefficient with complex upper parameter**
`[α,k]_q = (q^{α-k+1};q)_k/(q;q)_k`, with the principal branch of `q^α`. -/
noncomputable def gaussianBinomialC (q α : ℂ) (k : ℕ) : ℂ :=
  finiteQPochhammerIn (q ^ (α - k + 1)) q k / finiteQPochhammerIn q q k

variable {q z : ℂ}

/-- At an integer upper parameter the complex coefficient is the integer-index one. -/
theorem gaussianBinomialC_intCast (N : ℤ) (k : ℕ) :
    gaussianBinomialC q N k = gaussianBinomialZ q N k := by
  unfold gaussianBinomialC gaussianBinomialZ
  rw [show ((N : ℂ) - k + 1) = ((N - k + 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]

/-- At a natural upper parameter the complex coefficient is the Gaussian coefficient. -/
theorem gaussianBinomialC_natCast (hq0 : q ≠ 0) (n k : ℕ) (hk : finiteQPochhammerIn q q k ≠ 0) :
    gaussianBinomialC q n k = gaussianBinomial q n k := by
  rw [← Int.cast_natCast (R := ℂ) n, gaussianBinomialC_intCast, gaussianBinomialZ_natCast hq0 n k hk]

/-- **The upper-parameter series**: `(q^{α+1}z;q)_∞/(z;q)_∞ = ∑_k [α+k,k]_q z^k` for
`‖q‖ < 1`, `‖z‖ < 1`. -/
theorem hasSum_gaussianBinomialC_add (hq : ‖q‖ < 1) (α : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => gaussianBinomialC q (α + k) k * z ^ k)
      (qPochhammerInfIn (q ^ (α + 1) * z) q / qPochhammerInfIn z q) := by
  have h := hasSum_qBinomial_theorem hq (q ^ (α + 1)) hz
  have hterm : (fun k : ℕ =>
      finiteQPochhammerIn (q ^ (α + 1)) q k / finiteQPochhammerIn q q k * z ^ k) =
      fun k : ℕ => gaussianBinomialC q (α + k) k * z ^ k :=
    funext fun k => by
      simp only [gaussianBinomialC]
      rw [show (α + (k : ℂ) - k + 1) = α + 1 by ring]
  rw [hterm] at h
  exact h

/-- **The generalized reciprocal `q`-binomial theorem**:
`1/(z;q)_α = ∑_k [α+k-1,k]_q z^k` for `‖q‖ < 1`, `‖z‖ < 1`. -/
theorem hasSum_qPochhammerC_inv (hq : ‖q‖ < 1) (α : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => gaussianBinomialC q (α + k - 1) k * z ^ k) (qPochhammerC z q α)⁻¹ := by
  have h := hasSum_qBinomial_theorem hq (q ^ α) hz
  have hterm : (fun k : ℕ =>
      finiteQPochhammerIn (q ^ α) q k / finiteQPochhammerIn q q k * z ^ k) =
      fun k : ℕ => gaussianBinomialC q (α + k - 1) k * z ^ k :=
    funext fun k => by
      simp only [gaussianBinomialC]
      rw [show (α + (k : ℂ) - 1 - k + 1) = α by ring]
  rw [qPochhammerC, inv_div, mul_comm z (q ^ α)]
  rw [hterm] at h
  exact h

/-- **The generalized finite `q`-binomial theorem**:
`(z;q)_α = ∑_k (-1)^k q^{C(k,2)} [α,k]_q z^k` for `‖q‖ < 1`, `q ≠ 0`, `‖zq^α‖ < 1`. -/
theorem hasSum_qPochhammerC (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (α : ℂ) (hz : ‖z * q ^ α‖ < 1) :
    HasSum (fun k : ℕ => (-1) ^ k * q ^ k.choose 2 * gaussianBinomialC q α k * z ^ k)
      (qPochhammerC z q α) := by
  have hqa : q ^ α ≠ 0 := by
    intro h
    rw [Complex.cpow_eq_zero_iff] at h
    exact hq0 h.1
  have h := hasSum_qBinomial_theorem hq (q ^ (-α)) hz
  have hval : q ^ (-α) * (z * q ^ α) = z := by
    rw [Complex.cpow_neg, mul_comm, mul_assoc, mul_inv_cancel₀ hqa, mul_one]
  rw [hval] at h
  have hterm : (fun k : ℕ =>
      finiteQPochhammerIn (q ^ (-α)) q k / finiteQPochhammerIn q q k * (z * q ^ α) ^ k) =
      fun k : ℕ => (-1) ^ k * q ^ k.choose 2 * gaussianBinomialC q α k * z ^ k := by
    funext k
    rcases k with _ | k
    · simp [gaussianBinomialC]
    have hbase : q ^ α * q⁻¹ ^ (k + 1 - 1) = q ^ (α - ((k + 1 : ℕ) : ℂ) + 1) := by
      rw [Nat.add_sub_cancel, inv_pow, ← Complex.cpow_natCast, ← Complex.cpow_neg,
        ← Complex.cpow_add _ _ hq0]
      congr 1
      push_cast
      ring
    have hcancel : ((q ^ α) ^ (k + 1))⁻¹ * (q ^ α) ^ (k + 1) = 1 :=
      inv_mul_cancel₀ (pow_ne_zero _ hqa)
    simp only [gaussianBinomialC]
    rw [Complex.cpow_neg, finiteQPochhammerIn_base_reversal _ q (inv_ne_zero hqa) hq0, inv_inv,
      finiteQPochhammerIn_inv_base_eq hq0, hbase, neg_pow, inv_pow, mul_pow]
    linear_combination ((-1 : ℂ) ^ (k + 1) * q ^ (k + 1).choose 2 *
      (finiteQPochhammerIn (q ^ (α - ((k + 1 : ℕ) : ℂ) + 1)) q (k + 1) /
        finiteQPochhammerIn q q (k + 1)) * z ^ (k + 1)) * hcancel
  rw [qPochhammerC]
  rw [hterm] at h
  exact h

end Fabius

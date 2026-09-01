import FabiusFunction.JacobiTripleProduct
import FabiusFunction.PolynomialQDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The real q-gamma function

For `0 < q < 1` the `q`-gamma function is

`Γ_q(x) = (q;q)_∞ / (q^x;q)_∞ · (1-q)^{1-x}`, `x ∈ ℝ`.

Everything in this module is a direct consequence of the infinite
`q`-Pochhammer API: the functional equation `Γ_q(x+1) = [x]_q Γ_q(x)` with
`[x]_q = (1-q^x)/(1-q)` is the first-factor peeling
`(q^x;q)_∞ = (1-q^x)(q^{x+1};q)_∞`; the values `Γ_q(1) = 1` and
`Γ_q(n+1) = [n]_q!` follow; positivity on `(0,∞)` comes from the positivity
of the real products; the reflection product

`Γ_q(x) Γ_q(1-x) = (1-q) (q;q)_∞² / ((q^x;q)_∞ (q^{1-x};q)_∞)`

is immediate from the definition, and Jacobi's triple product at `z = q^x`
turns its denominator into the theta series `∑_n (-1)^n q^{C(n,2) + xn}`.

## Main declarations

* `qGamma`: the `q`-gamma function.
* `qGamma_pos`, `qGamma_one`, `qGamma_add_one`, `qGamma_nat_succ`.
* `qGamma_mul_qGamma_one_sub`: the reflection product.
* `hasSum_theta_qGamma_reflection`: its theta form.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The real `q`-gamma function `Γ_q(x) = (q;q)_∞ (1-q)^{1-x} / (q^x;q)_∞`. -/
def qGamma (q x : ℝ) : ℝ :=
  qPochhammerInfIn q q / qPochhammerInfIn (q ^ x) q * (1 - q) ^ (1 - x)

/-- The real `q`-number `[x]_q = (1 - q^x)/(1 - q)`. -/
def qNumber (q x : ℝ) : ℝ := (1 - q ^ x) / (1 - q)

variable {q : ℝ}

/-- `‖q‖ < 1` for `0 < q < 1`. -/
theorem norm_lt_one_of_pos_of_lt_one (hq0 : 0 < q) (hq1 : q < 1) : ‖q‖ < 1 := by
  rwa [Real.norm_of_nonneg hq0.le]

/-- `(q^x;q)_∞ > 0` for `x > 0` and `0 < q < 1`. -/
theorem qPochhammerInfIn_rpow_pos (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    0 < qPochhammerInfIn (q ^ x) q :=
  qPochhammerInfIn_pos_of_lt_one (Real.rpow_nonneg hq0.le x)
    (Real.rpow_lt_one hq0.le hq1 hx) hq0.le hq1

/-- `(q;q)_∞ > 0` for `0 < q < 1`. -/
theorem qPochhammerInfIn_self_pos (hq0 : 0 < q) (hq1 : q < 1) :
    0 < qPochhammerInfIn q q :=
  qPochhammerInfIn_pos_of_lt_one hq0.le hq1 hq0.le hq1

/-- **Positivity**: `Γ_q(x) > 0` for `x > 0`. -/
theorem qGamma_pos (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) : 0 < qGamma q x := by
  unfold qGamma
  exact mul_pos (div_pos (qPochhammerInfIn_self_pos hq0 hq1) (qPochhammerInfIn_rpow_pos hq0 hq1 hx))
    (Real.rpow_pos_of_pos (by linarith) _)

/-- `Γ_q(1) = 1`. -/
theorem qGamma_one (hq0 : 0 < q) (hq1 : q < 1) : qGamma q 1 = 1 := by
  unfold qGamma
  rw [Real.rpow_one, sub_self, Real.rpow_zero, mul_one,
    div_self (qPochhammerInfIn_self_pos hq0 hq1).ne']

/-- **The functional equation** `Γ_q(x+1) = [x]_q Γ_q(x)` for `x > 0`. -/
theorem qGamma_add_one (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    qGamma q (x + 1) = qNumber q x * qGamma q x := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hshift : qPochhammerInfIn (q ^ x) q = (1 - q ^ x) * qPochhammerInfIn (q ^ (x + 1)) q := by
    rw [qPochhammerInfIn_succ_shift (q ^ x) hq, Real.rpow_add_one hq0.ne']
  have hpow : (1 - q) ^ (1 - (x + 1)) = (1 - q) ^ (1 - x) / (1 - q) := by
    rw [show 1 - (x + 1) = 1 - x - 1 by ring, Real.rpow_sub_one h1q.ne']
  have hs : 1 - q ^ x ≠ 0 := (sub_pos.mpr (Real.rpow_lt_one hq0.le hq1 hx)).ne'
  have hs' : (1 - q ^ x) * (1 - q ^ x)⁻¹ = 1 := mul_inv_cancel₀ hs
  unfold qGamma qNumber
  rw [hshift, hpow, div_mul_eq_div_div]
  linear_combination (-(qPochhammerInfIn q q / qPochhammerInfIn (q ^ (x + 1)) q *
    ((1 - q) ^ (1 - x) / (1 - q)))) * hs'

/-- `Γ_q(n+1) = [n]_q!` for natural `n`. -/
theorem qGamma_nat_succ (hq0 : 0 < q) (hq1 : q < 1) (n : ℕ) :
    qGamma q (n + 1) = ∏ j ∈ Finset.range n, qNumber q (j + 1) := by
  induction n with
  | zero => simpa using qGamma_one hq0 hq1
  | succ n ih =>
      rw [Finset.prod_range_succ, ← ih, Nat.cast_succ, qGamma_add_one hq0 hq1 (by positivity),
        mul_comm]

/-- Over the reals, `[n]_q` (the `q`-number at a natural `n`) is the `q`-integer. -/
theorem qNumber_natCast (hq1 : q ≠ 1) (n : ℕ) : qNumber q n = qInt q n := by
  unfold qNumber
  rw [Real.rpow_natCast, div_eq_iff (sub_ne_zero.mpr (Ne.symm hq1)), mul_comm, one_sub_mul_qInt]

/-- **The reflection product**
`Γ_q(x) Γ_q(1-x) = (1-q) (q;q)_∞² / ((q^x;q)_∞ (q^{1-x};q)_∞)`, for every real
`x` and every `q < 1`. -/
theorem qGamma_mul_qGamma_one_sub (hq1 : q < 1) (x : ℝ) :
    qGamma q x * qGamma q (1 - x) =
      (1 - q) * qPochhammerInfIn q q ^ 2 /
        (qPochhammerInfIn (q ^ x) q * qPochhammerInfIn (q ^ (1 - x)) q) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  unfold qGamma
  have hpow : (1 - q) ^ (1 - x) * (1 - q) ^ (1 - (1 - x)) = 1 - q := by
    rw [← Real.rpow_add h1q, show 1 - x + (1 - (1 - x)) = 1 by ring, Real.rpow_one]
  calc qPochhammerInfIn q q / qPochhammerInfIn (q ^ x) q * (1 - q) ^ (1 - x) *
        (qPochhammerInfIn q q / qPochhammerInfIn (q ^ (1 - x)) q * (1 - q) ^ (1 - (1 - x)))
      = ((1 - q) ^ (1 - x) * (1 - q) ^ (1 - (1 - x))) * qPochhammerInfIn q q ^ 2 /
          (qPochhammerInfIn (q ^ x) q * qPochhammerInfIn (q ^ (1 - x)) q) := by
        rw [sq]
        ring
    _ = _ := by rw [hpow]

/-- **The theta form of the reflection product.**  For `0 < x < 1`,
`Γ_q(x) Γ_q(1-x) · ∑_n (-1)^n q^{C(n,2)+xn} = (1-q) (q;q)_∞³`, the series being
Jacobi's triple product at `z = q^x`. -/
theorem hasSum_theta_qGamma_reflection (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x < 1) :
    HasSum (fun n : ℤ => (-1 : ℝ) ^ n * q ^ thetaExponent n * (q ^ x) ^ n)
      ((1 - q) * qPochhammerInfIn q q ^ 3 / (qGamma q x * qGamma q (1 - x))) := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have hz : q ^ x ≠ 0 := (Real.rpow_pos_of_pos hq0 x).ne'
  have h := hasSum_jacobi_triple_product hq hz
  have hdiv : q / q ^ x = q ^ (1 - x) := by
    rw [Real.rpow_sub hq0, Real.rpow_one]
  rw [hdiv] at h
  have hA : 0 < qPochhammerInfIn (q ^ x) q := qPochhammerInfIn_rpow_pos hq0 hq1 hx0
  have hB : 0 < qPochhammerInfIn (q ^ (1 - x)) q := qPochhammerInfIn_rpow_pos hq0 hq1 (by linarith)
  have hC : 0 < qPochhammerInfIn q q := qPochhammerInfIn_self_pos hq0 hq1
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hval : qPochhammerInfIn (q ^ x) q * qPochhammerInfIn (q ^ (1 - x)) q * qPochhammerInfIn q q =
      (1 - q) * qPochhammerInfIn q q ^ 3 / (qGamma q x * qGamma q (1 - x)) := by
    rw [qGamma_mul_qGamma_one_sub hq1 x]
    field_simp
  rw [hval] at h
  exact h

end

end Fabius

import FabiusFunction.QGamma
import FabiusFunction.JacksonIntegral

/-!
# The Jackson `q`-beta integral

For `0 < q < 1` and `x, y > 0`, the Jackson `q`-beta function is

`B_q(x,y) = ∫₀¹ t^{x-1} (qt;q)_∞ / (q^y t;q)_∞ d_q t`.

Expanding the Jackson integral, the `n`-th term is
`(1-q) q^{nx} (q^{n+1};q)_∞ / (q^{n+y};q)_∞`, and tail cancellation rewrites it as
`(1-q) (q;q)_∞/(q^y;q)_∞ · (q^y;q)_n/(q;q)_n · (q^x)^n`.  The infinite `q`-binomial
theorem sums the series to `(q^{x+y};q)_∞ / (q^x;q)_∞`, which gives the product formula

`B_q(x,y) = (1-q) (q;q)_∞ (q^{x+y};q)_∞ / ((q^x;q)_∞ (q^y;q)_∞)`,

and this is `Γ_q(x) Γ_q(y) / Γ_q(x+y)` once the powers of `1-q` in the definition of `Γ_q`
are collected: `(1-q)^{1-x} (1-q)^{1-y} / (1-q)^{1-x-y} = 1-q`.

## Main declarations

* `qBeta`: the Jackson `q`-beta function.
* `qBeta_eq_prod`: the product evaluation.
* `qBeta_eq_qGamma`: `B_q(x,y) = Γ_q(x)Γ_q(y)/Γ_q(x+y)`.
* `qBeta_comm`, `qBeta_pos`, `qBeta_add_one_left`, `qBeta_add_one_right`: symmetry,
  positivity, and the two recurrences.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

noncomputable section

/-- The Jackson `q`-beta function `B_q(x,y) = ∫₀¹ t^{x-1} (qt;q)_∞/(q^y t;q)_∞ d_q t`. -/
def qBeta (q x y : ℝ) : ℝ :=
  jacksonIntegral q
    (fun t => t ^ (x - 1) * (qPochhammerInfIn (q * t) q / qPochhammerInfIn (q ^ y * t) q)) 1

variable {q : ℝ}

/-- `[z]_q > 0` for `0 < q < 1` and `z > 0`. -/
theorem qNumber_pos (hq0 : 0 < q) (hq1 : q < 1) {z : ℝ} (hz : 0 < z) : 0 < qNumber q z :=
  div_pos (sub_pos.mpr (Real.rpow_lt_one hq0.le hq1 hz)) (sub_pos.mpr hq1)

/-- The `n`-th Jackson term of the `q`-beta integrand, after tail cancellation:
`q^n (q^n)^{x-1} (q^{n+1};q)_∞/(q^{n+y};q)_∞ = (q;q)_∞/(q^y;q)_∞ · (q^y;q)_n/(q;q)_n · (q^x)^n`. -/
theorem qBeta_term_eq (hq0 : 0 < q) (hq1 : q < 1) {y : ℝ} (hy : 0 < y) (x : ℝ) (n : ℕ) :
    q ^ n * ((1 * q ^ n) ^ (x - 1) *
        (qPochhammerInfIn (q * (1 * q ^ n)) q / qPochhammerInfIn (q ^ y * (1 * q ^ n)) q)) =
      qPochhammerInfIn q q / qPochhammerInfIn (q ^ y) q *
        (finiteQPochhammerIn (q ^ y) q n / finiteQPochhammerIn q q n * (q ^ x) ^ n) := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have hP : qPochhammerInfIn q q = finiteQPochhammerIn q q n * qPochhammerInfIn (q * q ^ n) q :=
    qPochhammerInfIn_eq_finite_mul_shift q hq n
  have hPy : qPochhammerInfIn (q ^ y) q =
      finiteQPochhammerIn (q ^ y) q n * qPochhammerInfIn (q ^ y * q ^ n) q :=
    qPochhammerInfIn_eq_finite_mul_shift (q ^ y) hq n
  have hP0 : qPochhammerInfIn q q ≠ 0 := (qPochhammerInfIn_self_pos hq0 hq1).ne'
  have hPy0 : qPochhammerInfIn (q ^ y) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hy).ne'
  have hf0 : finiteQPochhammerIn q q n ≠ 0 := by
    intro h; rw [hP, h, zero_mul] at hP0; exact hP0 rfl
  have hfy0 : finiteQPochhammerIn (q ^ y) q n ≠ 0 := by
    intro h; rw [hPy, h, zero_mul] at hPy0; exact hPy0 rfl
  have hs0 : qPochhammerInfIn (q * q ^ n) q ≠ 0 := by
    intro h; rw [hP, h, mul_zero] at hP0; exact hP0 rfl
  have hsy0 : qPochhammerInfIn (q ^ y * q ^ n) q ≠ 0 := by
    intro h; rw [hPy, h, mul_zero] at hPy0; exact hPy0 rfl
  have hpow : q ^ n * (q ^ n) ^ (x - 1) = (q ^ x) ^ n := by
    rw [← Real.rpow_natCast q n, ← Real.rpow_natCast (q ^ x) n,
      ← Real.rpow_mul hq0.le (n : ℝ) (x - 1), ← Real.rpow_mul hq0.le x n, ← Real.rpow_add hq0]
    congr 1
    ring
  rw [one_mul]
  conv_lhs => rw [← mul_assoc, hpow]
  rw [hP, hPy]
  field_simp

/-- **The `q`-beta evaluation**, product form:
`B_q(x,y) = (1-q) (q;q)_∞ (q^{x+y};q)_∞ / ((q^x;q)_∞ (q^y;q)_∞)`. -/
theorem qBeta_eq_prod (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    qBeta q x y = (1 - q) * (qPochhammerInfIn q q * qPochhammerInfIn (q ^ (x + y)) q) /
      (qPochhammerInfIn (q ^ x) q * qPochhammerInfIn (q ^ y) q) := by
  have hq : ‖q‖ < 1 := norm_lt_one_of_pos_of_lt_one hq0 hq1
  have hz : ‖q ^ x‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hq0.le x)]
    exact Real.rpow_lt_one hq0.le hq1 hx
  have hsum := (hasSum_qBinomial_theorem hq (q ^ y) hz).mul_left
    (qPochhammerInfIn q q / qPochhammerInfIn (q ^ y) q)
  have key : ∑' n : ℕ, q ^ n * ((1 * q ^ n) ^ (x - 1) *
      (qPochhammerInfIn (q * (1 * q ^ n)) q / qPochhammerInfIn (q ^ y * (1 * q ^ n)) q)) =
      qPochhammerInfIn q q / qPochhammerInfIn (q ^ y) q *
        (qPochhammerInfIn (q ^ y * q ^ x) q / qPochhammerInfIn (q ^ x) q) := by
    rw [tsum_congr fun n => qBeta_term_eq hq0 hq1 hy x n]
    exact hsum.tsum_eq
  have hPy0 : qPochhammerInfIn (q ^ y) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hy).ne'
  have hPx0 : qPochhammerInfIn (q ^ x) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hx).ne'
  dsimp only [qBeta, jacksonIntegral]
  rw [key, Real.rpow_add hq0, mul_comm (q ^ x) (q ^ y)]
  field_simp

/-- **The `q`-beta evaluation**: `B_q(x,y) = Γ_q(x) Γ_q(y) / Γ_q(x+y)`. -/
theorem qBeta_eq_qGamma (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    qBeta q x y = qGamma q x * qGamma q y / qGamma q (x + y) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hP0 : qPochhammerInfIn q q ≠ 0 := (qPochhammerInfIn_self_pos hq0 hq1).ne'
  have hPx0 : qPochhammerInfIn (q ^ x) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hx).ne'
  have hPy0 : qPochhammerInfIn (q ^ y) q ≠ 0 := (qPochhammerInfIn_rpow_pos hq0 hq1 hy).ne'
  have hPxy0 : qPochhammerInfIn (q ^ (x + y)) q ≠ 0 :=
    (qPochhammerInfIn_rpow_pos hq0 hq1 (by positivity)).ne'
  have hA0 : (1 - q) ^ (1 - (x + y)) ≠ 0 := (Real.rpow_pos_of_pos h1q _).ne'
  have hA : (1 - q) ^ (1 - x) * (1 - q) ^ (1 - y) = (1 - q) ^ (1 - (x + y)) * (1 - q) := by
    rw [← Real.rpow_add h1q, ← Real.rpow_add_one h1q.ne']
    congr 1
    ring
  rw [qBeta_eq_prod hq0 hq1 hx hy]
  unfold qGamma
  rw [eq_div_iff (mul_ne_zero (div_ne_zero hP0 hPxy0) hA0)]
  have hre : qPochhammerInfIn q q / qPochhammerInfIn (q ^ x) q * (1 - q) ^ (1 - x) *
      (qPochhammerInfIn q q / qPochhammerInfIn (q ^ y) q * (1 - q) ^ (1 - y)) =
      qPochhammerInfIn q q / qPochhammerInfIn (q ^ x) q *
        (qPochhammerInfIn q q / qPochhammerInfIn (q ^ y) q) *
        ((1 - q) ^ (1 - x) * (1 - q) ^ (1 - y)) := by ring
  rw [hre, hA]
  field_simp

/-- `B_q` is symmetric. -/
theorem qBeta_comm (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    qBeta q x y = qBeta q y x := by
  rw [qBeta_eq_prod hq0 hq1 hx hy, qBeta_eq_prod hq0 hq1 hy hx, add_comm,
    mul_comm (qPochhammerInfIn (q ^ x) q)]

/-- `B_q(x,y) > 0`. -/
theorem qBeta_pos (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < qBeta q x y := by
  rw [qBeta_eq_qGamma hq0 hq1 hx hy]
  exact div_pos (mul_pos (qGamma_pos hq0 hq1 hx) (qGamma_pos hq0 hq1 hy))
    (qGamma_pos hq0 hq1 (by positivity))

/-- The recurrence `B_q(x+1,y) = [x]_q/[x+y]_q · B_q(x,y)`. -/
theorem qBeta_add_one_left (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    qBeta q (x + 1) y = qNumber q x / qNumber q (x + y) * qBeta q x y := by
  have hxy : 0 < x + y := by positivity
  have hΓ : qGamma q (x + y) ≠ 0 := (qGamma_pos hq0 hq1 hxy).ne'
  have hN : qNumber q (x + y) ≠ 0 := (qNumber_pos hq0 hq1 hxy).ne'
  rw [qBeta_eq_qGamma hq0 hq1 (by positivity) hy, qBeta_eq_qGamma hq0 hq1 hx hy,
    qGamma_add_one hq0 hq1 hx, show x + 1 + y = x + y + 1 by ring, qGamma_add_one hq0 hq1 hxy]
  field_simp

/-- The recurrence `B_q(x,y+1) = [y]_q/[x+y]_q · B_q(x,y)`. -/
theorem qBeta_add_one_right (hq0 : 0 < q) (hq1 : q < 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    qBeta q x (y + 1) = qNumber q y / qNumber q (x + y) * qBeta q x y := by
  rw [qBeta_comm hq0 hq1 hx (by positivity), qBeta_add_one_left hq0 hq1 hy hx,
    qBeta_comm hq0 hq1 hy hx, add_comm y x]

end

end Fabius

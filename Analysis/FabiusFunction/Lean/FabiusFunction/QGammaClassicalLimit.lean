import FabiusFunction.QBohrMollerup
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The monotone Artin bracket for the `q`-gamma function

For `0 < q < 1` write `[u]_q = (1 - q^u)/(1 - q)` (`qNumber`) and, for `m : ℕ` and `x > 0`,

`L_m(q,x) = [m]_q^x [1]_q⋯[m]_q / ([x]_q [x+1]_q ⋯ [x+m]_q)`  (`qGammaLowerSeq`),
`U_m(q,x) = [m+1]_q^x [1]_q⋯[m]_q / ([x]_q [x+1]_q ⋯ [x+m]_q)`  (`qGammaUpperSeq`).

`U_m → Γ_q(x)` is the `q`-analogue of Euler's limit formula, already available in the corpus as
`tendsto_qGamma_limit`.  This module proves the *two-sided* statement

`L_m(q,x) ≤ Γ_q(x) ≤ U_m(q,x)`

together with the fact that `U` is antitone and `L` is monotone in `m`, so that the bracket is a
genuinely nested one.

## Why this is new, and how it differs from the log-convexity bracket

The classical route to the same two-sided bound — Artin's, and the one taken in the source text and
in `qGamma_two_sided_bound` of the companion module `ComplexGaussianClassical` — applies the strict
log-convexity of `log Γ_q` (`strictConvexOn_log_qGamma`) to the four points `m < m+1 < m+1+x < m+2`.
Those four points must be strictly increasing and lie in `(0,∞)`, which forces `1 ≤ m` and
`0 < x < 1`, and the bound then rests on the whole second-derivative machinery of
`QGammaLogDerivative`.

Here the bound is obtained instead from the *exact product formula* plus weighted AM–GM.  The whole
argument rests on one scalar inequality (`one_sub_mul_rpow_le`): for `0 ≤ y ≤ 1`, `0 ≤ s ≤ 1`,
`0 ≤ r ≤ 1`,

`(1 - s r)^y (1 - s)^{1-y} ≤ 1 - s r^y`,

itself two applications of `Real.geom_mean_le_arith_mean2_weighted`.  Two rearrangements of it
(`one_sub_mul_rpow_le'`, `one_sub_mul_rpow_le''`) give the two elementary `q`-number steps
`qNumber_upper_step` and `qNumber_lower_step`, and those are exactly the successor steps of `U`
and of `L`.  Consequences:

* no dependence on `QGammaLogConvex` / `QGammaLogDerivative` at all — this module imports only
  `QBohrMollerup`, and in particular does not depend on `ComplexGaussianClassical`;
* the bounds hold for **every** `m`, including `m = 0`;
* the lower bound `qGammaLowerSeq_le_qGamma` needs only `x > 0` — no upper bound on `x`;
* the monotonicity of the two sequences in `m` (`qGammaUpperSeq_antitone`,
  `qGammaLowerSeq_monotone`) is new information: the source text records only that the two bounds
  hold for each fixed `m`, never that they are nested.

The exact ratio `L_m = ([m]_q/[m+1]_q)^x U_m` (`qGammaLowerSeq_eq_mul_qGammaUpperSeq`) then gives
`tendsto_qGammaLowerSeq` (the lower approximants converge to `Γ_q(x)` as well — in the corpus this
was only an anonymous `have` inside `qGamma_eq_of_logConvex`) and the explicit two-sided error
estimate `abs_qGamma_sub_qGammaUpperSeq_le`.

## Scope relative to `thm:qgamma-classical-limit`

The first sentence of that theorem, `lim_{q→1⁻} Γ_q(x) = Γ(x)` for every `x > 0`, is formalized in
the companion module `ComplexGaussianClassical` as `tendsto_qGamma_nhdsLT_one`, along the honest
one-sided filter `𝓝[<] (1 : ℝ)`; this module deliberately does not restate it, so that no name is
declared twice.  What it supplies is the strengthened, log-convexity-free form of the bracket that
is the substance of the proof.

The second sentence, "the convergence is locally uniform on `(0,∞)`", is **not** covered here and
is not covered anywhere in the corpus.  Local uniformity would need a uniform-on-compacts version
of Euler's classical limit `n^x n!/(x⋯(x+n)) → Γ(x)`, which Mathlib does not have (only the
pointwise `Real.GammaSeq_tendsto_Gamma`), together with a uniform-in-`x` version of each `q → 1⁻`
step.  Nothing is claimed for complex arguments (`qGammaC`) or for `q → 1⁺`.

## Main declarations

* `one_sub_mul_rpow_le`, `one_sub_mul_rpow_le'`, `one_sub_mul_rpow_le''`: the AM–GM engine.
* `qNumber_nonneg`, `qNumber_le_qNumber`: elementary facts about `[u]_q`.
* `qNumber_upper_step`, `qNumber_lower_step`: the two successor inequalities.
* `qGammaUpperSeq`, `qGammaLowerSeq`: the two approximating sequences.
* `qGammaUpperSeq_antitone`, `qGammaLowerSeq_monotone`: the bracket is nested.
* `qGamma_le_qGammaUpperSeq`, `qGammaLowerSeq_le_qGamma`: **the two-sided Artin bracket.**
* `tendsto_qGammaUpperSeq`, `tendsto_qGammaLowerSeq`: both ends converge to `Γ_q(x)`.
* `qGammaLowerSeq_eq_mul_qGammaUpperSeq`, `abs_qGamma_sub_qGammaUpperSeq_le`: the exact ratio and
  the resulting explicit error bound.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

/-! ### The scalar inequality behind the bracket -/

/-- **Weighted AM–GM in the form the bracket needs.**  For `0 ≤ y ≤ 1`, `0 ≤ s ≤ 1` and
`0 ≤ r ≤ 1`,

`(1 - s r)^y (1 - s)^{1-y} ≤ 1 - s r^y`.

Both steps are `Real.geom_mean_le_arith_mean2_weighted`: the left side is at most
`y(1 - sr) + (1-y)(1-s) = 1 - s(yr + (1-y))`, and `r^y ≤ yr + (1-y)` bounds `s r^y` by
`s(yr + (1-y))`. -/
theorem one_sub_mul_rpow_le {r s y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - s * r) ^ y * (1 - s) ^ (1 - y) ≤ 1 - s * r ^ y := by
  have hsr : s * r ≤ 1 := mul_le_one₀ hs1 hr0 hr1
  have h1 : (0 : ℝ) ≤ 1 - s * r := by linarith
  have h2 : (0 : ℝ) ≤ 1 - s := by linarith
  have hAM : (1 - s * r) ^ y * (1 - s) ^ (1 - y) ≤ y * (1 - s * r) + (1 - y) * (1 - s) :=
    Real.geom_mean_le_arith_mean2_weighted hy0 (by linarith) h1 h2 (by ring)
  have hAM2 : r ^ y * (1 : ℝ) ^ (1 - y) ≤ y * r + (1 - y) * 1 :=
    Real.geom_mean_le_arith_mean2_weighted hy0 (by linarith) hr0 zero_le_one (by ring)
  simp only [Real.one_rpow, mul_one] at hAM2
  have h3 : s * r ^ y ≤ s * (y * r + (1 - y)) := mul_le_mul_of_nonneg_left hAM2 hs0
  linarith [hAM, h3]

/-- A rearrangement of `one_sub_mul_rpow_le` obtained by multiplying through by `(1-s)^y`:
for `0 ≤ y ≤ 1`, `0 ≤ s < 1` and `0 ≤ r ≤ 1`,

`(1 - s r)^y (1 - s) ≤ (1 - s)^y (1 - s r^y)`.

This is the successor step of the *upper* approximants. -/
theorem one_sub_mul_rpow_le' {r s y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - s * r) ^ y * (1 - s) ≤ (1 - s) ^ y * (1 - s * r ^ y) := by
  have h2 : (0 : ℝ) < 1 - s := by linarith
  have hkey := one_sub_mul_rpow_le hy0 hy1 hs0 hs1.le hr0 hr1
  have hmul := mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg h2.le y)
  have hpow : (1 - s) ^ (1 - y) * (1 - s) ^ y = 1 - s := by
    rw [← Real.rpow_add h2, show (1 : ℝ) - y + y = 1 by ring, Real.rpow_one]
  calc (1 - s * r) ^ y * (1 - s)
      = (1 - s * r) ^ y * (1 - s) ^ (1 - y) * (1 - s) ^ y := by rw [mul_assoc, hpow]
    _ ≤ (1 - s * r ^ y) * (1 - s) ^ y := hmul
    _ = (1 - s) ^ y * (1 - s * r ^ y) := by ring

/-- A second rearrangement, obtained by applying `one_sub_mul_rpow_le` at the weight `(y+1)⁻¹`
and the base `r^{y+1}` and then raising to the power `y+1`: for `0 ≤ y`, `0 ≤ s ≤ 1` and
`0 ≤ r ≤ 1`,

`(1 - s)^y (1 - s r^{y+1}) ≤ (1 - s r)^{y+1}`.

Note that no upper bound on `y` is needed, and that `s = 1` is allowed.  This is the successor
step of the *lower* approximants. -/
theorem one_sub_mul_rpow_le'' {r s y : ℝ} (hy0 : 0 ≤ y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 - s) ^ y * (1 - s * r ^ (y + 1)) ≤ (1 - s * r) ^ (y + 1) := by
  have hy1 : (0 : ℝ) < y + 1 := by linarith
  have hyne : y + 1 ≠ 0 := hy1.ne'
  have hw0 : (0 : ℝ) ≤ (y + 1)⁻¹ := (inv_pos.mpr hy1).le
  have hw1 : (y + 1)⁻¹ ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ y + 1 by linarith) hw0
    rwa [mul_one, inv_mul_cancel₀ hyne] at h
  have hrp : (0 : ℝ) ≤ r ^ (y + 1) := Real.rpow_nonneg hr0 _
  have hrp1 : r ^ (y + 1) ≤ 1 := Real.rpow_le_one hr0 hr1 hy1.le
  have hsr : s * r ^ (y + 1) ≤ 1 := mul_le_one₀ hs1 hrp hrp1
  have hA : (0 : ℝ) ≤ 1 - s * r ^ (y + 1) := by linarith
  have h1s : (0 : ℝ) ≤ 1 - s := by linarith
  have hbase := one_sub_mul_rpow_le (r := r ^ (y + 1)) (s := s) (y := (y + 1)⁻¹)
    hw0 hw1 hs0 hs1 hrp hrp1
  have hcancel : (r ^ (y + 1)) ^ (y + 1)⁻¹ = r := by
    rw [← Real.rpow_mul hr0, mul_inv_cancel₀ hyne, Real.rpow_one]
  rw [hcancel] at hbase
  have hL0 : (0 : ℝ) ≤ (1 - s * r ^ (y + 1)) ^ (y + 1)⁻¹ * (1 - s) ^ (1 - (y + 1)⁻¹) :=
    mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg h1s _)
  have hraise := Real.rpow_le_rpow hL0 hbase hy1.le
  have hexp2 : (1 - (y + 1)⁻¹) * (y + 1) = y := by
    rw [sub_mul, one_mul, inv_mul_cancel₀ hyne]
    ring
  have hexp : ((1 - s * r ^ (y + 1)) ^ (y + 1)⁻¹ * (1 - s) ^ (1 - (y + 1)⁻¹)) ^ (y + 1)
      = (1 - s * r ^ (y + 1)) * (1 - s) ^ y := by
    rw [Real.mul_rpow (Real.rpow_nonneg hA _) (Real.rpow_nonneg h1s _),
      ← Real.rpow_mul hA, ← Real.rpow_mul h1s, inv_mul_cancel₀ hyne, Real.rpow_one, hexp2]
  rw [hexp] at hraise
  linarith [hraise]

/-! ### Two arithmetic helpers for comparing the approximants -/

/-- Comparing `A (P B)/(Q D)` with `C P / Q` reduces to comparing `A B` with `C D`. -/
private theorem div_le_div_of_mul_le_left {A B C D P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 < Q)
    (hD : 0 < D) (h : A * B ≤ C * D) : A * (P * B) / (Q * D) ≤ C * P / Q := by
  rw [div_le_div_iff₀ (mul_pos hQ hD) hQ]
  calc A * (P * B) * Q = A * B * (P * Q) := by ring
    _ ≤ C * D * (P * Q) := mul_le_mul_of_nonneg_right h (mul_nonneg hP hQ.le)
    _ = C * P * (Q * D) := by ring

/-- The mirror image of `div_le_div_of_mul_le_left`. -/
private theorem div_le_div_of_mul_le_right {A B C D P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 < Q)
    (hD : 0 < D) (h : C * D ≤ A * B) : C * P / Q ≤ A * (P * B) / (Q * D) := by
  rw [div_le_div_iff₀ hQ (mul_pos hQ hD)]
  calc C * P * (Q * D) = C * D * (P * Q) := by ring
    _ ≤ A * B * (P * Q) := mul_le_mul_of_nonneg_right h (mul_nonneg hP hQ.le)
    _ = A * (P * B) * Q := by ring

/-! ### The two approximating sequences -/

noncomputable section

/-- The upper Artin approximant `U_m(q,x) = [m+1]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q)`.  This is
the sequence of the `q`-analogue of Euler's limit formula (`tendsto_qGamma_limit`). -/
def qGammaUpperSeq (q x : ℝ) (m : ℕ) : ℝ :=
  qNumber q ((m : ℝ) + 1) ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
    ∏ j ∈ range (m + 1), qNumber q (x + j)

/-- The lower Artin approximant `L_m(q,x) = [m]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q)`, obtained from
`qGammaUpperSeq` by replacing `[m+1]_q^x` with `[m]_q^x`. -/
def qGammaLowerSeq (q x : ℝ) (m : ℕ) : ℝ :=
  qNumber q (m : ℝ) ^ x * (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) /
    ∏ j ∈ range (m + 1), qNumber q (x + j)

end

variable {q : ℝ}

/-! ### Elementary properties of `q`-numbers -/

/-- `[u]_q ≥ 0` for `0 < q < 1` and `u ≥ 0` (the strict version `qNumber_pos` needs `u > 0`). -/
theorem qNumber_nonneg (hq0 : 0 < q) (hq1 : q < 1) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ qNumber q u := by
  have h1 : q ^ u ≤ 1 := Real.rpow_le_one hq0.le hq1.le hu
  have h2 : (0 : ℝ) < 1 - q := by linarith
  unfold qNumber
  exact div_nonneg (show (0 : ℝ) ≤ 1 - q ^ u by linarith) h2.le

/-- `u ↦ [u]_q` is monotone for `0 < q < 1`, since `u ↦ q^u` is antitone there. -/
theorem qNumber_le_qNumber (hq0 : 0 < q) (hq1 : q < 1) {u v : ℝ} (huv : u ≤ v) :
    qNumber q u ≤ qNumber q v := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hpow : q ^ v ≤ q ^ u := Real.rpow_le_rpow_of_exponent_ge hq0 hq1.le huv
  unfold qNumber
  exact (div_le_div_iff_of_pos_right h1q).2 (show 1 - q ^ u ≤ 1 - q ^ v by linarith)

/-! ### The two successor steps -/

/-- **The successor step of the upper approximants.**  For `0 < q < 1`, `0 ≤ x ≤ 1` and `u > 0`,

`[u+1]_q^x [u]_q ≤ [u]_q^x [x+u]_q`.

Writing `s = q^u`, both sides carry the factor `(1-q)^{-x}(1-q)^{-1}`, and what remains is
`(1 - sq)^x (1-s) ≤ (1-s)^x (1 - s q^x)`, which is `one_sub_mul_rpow_le'`. -/
theorem qNumber_upper_step (hq0 : 0 < q) (hq1 : q < 1) {x u : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hu : 0 < u) :
    qNumber q (u + 1) ^ x * qNumber q u ≤ qNumber q u ^ x * qNumber q (x + u) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hs0 : (0 : ℝ) < q ^ u := Real.rpow_pos_of_pos hq0 u
  have hs1 : q ^ u < 1 := Real.rpow_lt_one hq0.le hq1 hu
  have hA : (0 : ℝ) ≤ 1 - q ^ u := by linarith
  have hqq : q ^ u * q ≤ 1 := mul_le_one₀ hs1.le hq0.le hq1.le
  have hB : (0 : ℝ) ≤ 1 - q ^ u * q := by linarith
  have hu1 : q ^ (u + 1) = q ^ u * q := Real.rpow_add_one hq0.ne' u
  have hxu : q ^ (x + u) = q ^ u * q ^ x := by
    rw [Real.rpow_add hq0, mul_comm (q ^ x) (q ^ u)]
  unfold qNumber
  rw [hu1, hxu, Real.div_rpow hB h1q.le, Real.div_rpow hA h1q.le,
    div_mul_div_comm, div_mul_div_comm]
  refine (div_le_div_iff_of_pos_right (mul_pos (Real.rpow_pos_of_pos h1q x) h1q)).2 ?_
  exact one_sub_mul_rpow_le' hx0 hx1 hs0.le hs1 hq0.le hq1.le

/-- **The successor step of the lower approximants.**  For `0 < q < 1`, `0 ≤ x` and `0 ≤ u`,

`[u]_q^x [x+u+1]_q ≤ [u+1]_q^x [u+1]_q`.

No upper bound on `x` is needed here, and `u = 0` is allowed.  Writing `s = q^u`, the common factor
`(1-q)^{-x}(1-q)^{-1}` cancels and what remains is
`(1-s)^x (1 - s q^{x+1}) ≤ (1 - sq)^{x+1}`, which is `one_sub_mul_rpow_le''`. -/
theorem qNumber_lower_step (hq0 : 0 < q) (hq1 : q < 1) {x u : ℝ} (hx0 : 0 ≤ x) (hu : 0 ≤ u) :
    qNumber q u ^ x * qNumber q (x + (u + 1)) ≤ qNumber q (u + 1) ^ x * qNumber q (u + 1) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hs0 : (0 : ℝ) < q ^ u := Real.rpow_pos_of_pos hq0 u
  have hs1 : q ^ u ≤ 1 := Real.rpow_le_one hq0.le hq1.le hu
  have hA : (0 : ℝ) ≤ 1 - q ^ u := by linarith
  have hqq : q ^ u * q ≤ q := by
    have h := mul_le_mul_of_nonneg_right hs1 hq0.le
    rwa [one_mul] at h
  have hBpos : (0 : ℝ) < 1 - q ^ u * q := by linarith
  have hu1 : q ^ (u + 1) = q ^ u * q := Real.rpow_add_one hq0.ne' u
  have hxu : q ^ (x + (u + 1)) = q ^ u * q ^ (x + 1) := by
    rw [show x + (u + 1) = u + (x + 1) by ring, Real.rpow_add hq0]
  unfold qNumber
  rw [hu1, hxu, Real.div_rpow hA h1q.le, Real.div_rpow hBpos.le h1q.le,
    div_mul_div_comm, div_mul_div_comm]
  refine (div_le_div_iff_of_pos_right (mul_pos (Real.rpow_pos_of_pos h1q x) h1q)).2 ?_
  rw [← Real.rpow_add_one hBpos.ne' x]
  exact one_sub_mul_rpow_le'' hx0 hs0.le hs1 hq0.le hq1.le

/-! ### The bracket is nested -/

/-- `U_m(q,x) → Γ_q(x)`: this is exactly the `q`-analogue of Euler's limit formula. -/
theorem tendsto_qGammaUpperSeq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx : 0 < x) :
    Tendsto (qGammaUpperSeq q x) atTop (𝓝 (qGamma q x)) :=
  tendsto_qGamma_limit hq0 hq1 hx

/-- **The upper approximants decrease.**  For `0 < q < 1` and `0 < x ≤ 1`, `m ↦ U_m(q,x)` is
antitone; the successor step is `qNumber_upper_step` at `u = m+1`. -/
theorem qGammaUpperSeq_antitone (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    Antitone (qGammaUpperSeq q x) := by
  have hP : ∀ n : ℕ, (0 : ℝ) < ∏ j ∈ range n, qNumber q ((j : ℝ) + 1) := fun n =>
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  have hQ : ∀ n : ℕ, (0 : ℝ) < ∏ j ∈ range n, qNumber q (x + j) := fun n =>
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  refine antitone_nat_of_succ_le fun m => ?_
  have hstep := qNumber_upper_step (u := (m : ℝ) + 1) hq0 hq1 hx0.le hx1 (by positivity)
  have hlast : (0 : ℝ) < qNumber q (x + ((m : ℝ) + 1)) := qNumber_pos hq0 hq1 (by positivity)
  have e1 : (∏ j ∈ range (m + 1), qNumber q ((j : ℝ) + 1))
      = (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) * qNumber q ((m : ℝ) + 1) :=
    prod_range_succ (fun j : ℕ => qNumber q ((j : ℝ) + 1)) m
  have e2 : (∏ j ∈ range (m + 1 + 1), qNumber q (x + (j : ℝ)))
      = (∏ j ∈ range (m + 1), qNumber q (x + (j : ℝ))) * qNumber q (x + ((m + 1 : ℕ) : ℝ)) :=
    prod_range_succ (fun j : ℕ => qNumber q (x + (j : ℝ))) (m + 1)
  have e3 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := Nat.cast_add_one m
  unfold qGammaUpperSeq
  rw [e1, e2, e3]
  exact div_le_div_of_mul_le_left (hP m).le (hQ (m + 1)) hlast hstep

/-- **The lower approximants increase.**  For `0 < q < 1` and `x > 0`, `m ↦ L_m(q,x)` is monotone;
the successor step is `qNumber_lower_step` at `u = m`, which is why that lemma was stated without
an upper bound on `x` and with `u = 0` allowed. -/
theorem qGammaLowerSeq_monotone (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x) :
    Monotone (qGammaLowerSeq q x) := by
  have hP : ∀ n : ℕ, (0 : ℝ) < ∏ j ∈ range n, qNumber q ((j : ℝ) + 1) := fun n =>
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  have hQ : ∀ n : ℕ, (0 : ℝ) < ∏ j ∈ range n, qNumber q (x + j) := fun n =>
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  refine monotone_nat_of_le_succ fun m => ?_
  have hstep := qNumber_lower_step (u := (m : ℝ)) hq0 hq1 hx0.le (Nat.cast_nonneg m)
  have hlast : (0 : ℝ) < qNumber q (x + ((m : ℝ) + 1)) := qNumber_pos hq0 hq1 (by positivity)
  have e1 : (∏ j ∈ range (m + 1), qNumber q ((j : ℝ) + 1))
      = (∏ j ∈ range m, qNumber q ((j : ℝ) + 1)) * qNumber q ((m : ℝ) + 1) :=
    prod_range_succ (fun j : ℕ => qNumber q ((j : ℝ) + 1)) m
  have e2 : (∏ j ∈ range (m + 1 + 1), qNumber q (x + (j : ℝ)))
      = (∏ j ∈ range (m + 1), qNumber q (x + (j : ℝ))) * qNumber q (x + ((m + 1 : ℕ) : ℝ)) :=
    prod_range_succ (fun j : ℕ => qNumber q (x + (j : ℝ))) (m + 1)
  have e3 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := Nat.cast_add_one m
  unfold qGammaLowerSeq
  rw [e1, e2, e3]
  exact div_le_div_of_mul_le_right (hP m).le (hQ (m + 1)) hlast hstep

/-- `L_m(q,x) ≤ U_m(q,x)`: only the leading factor differs, and `[m]_q ≤ [m+1]_q`. -/
theorem qGammaLowerSeq_le_qGammaUpperSeq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x)
    (m : ℕ) : qGammaLowerSeq q x m ≤ qGammaUpperSeq q x m := by
  have hP : (0 : ℝ) < ∏ j ∈ range m, qNumber q ((j : ℝ) + 1) :=
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  have hQ : (0 : ℝ) < ∏ j ∈ range (m + 1), qNumber q (x + j) :=
    prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)
  have hrp : qNumber q (m : ℝ) ^ x ≤ qNumber q ((m : ℝ) + 1) ^ x :=
    Real.rpow_le_rpow (qNumber_nonneg hq0 hq1 (Nat.cast_nonneg m))
      (qNumber_le_qNumber hq0 hq1 (show (m : ℝ) ≤ (m : ℝ) + 1 by linarith)) hx0.le
  unfold qGammaLowerSeq qGammaUpperSeq
  exact (div_le_div_iff_of_pos_right hQ).2 (mul_le_mul_of_nonneg_right hrp hP.le)

/-! ### Convergence of both ends, and the bracket -/

/-- **The exact ratio of the two approximants**: `L_m(q,x) = ([m]_q/[m+1]_q)^x U_m(q,x)`. -/
theorem qGammaLowerSeq_eq_mul_qGammaUpperSeq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x)
    (m : ℕ) :
    qGammaLowerSeq q x m
      = (qNumber q (m : ℝ) / qNumber q ((m : ℝ) + 1)) ^ x * qGammaUpperSeq q x m := by
  have hqm1 : 0 < qNumber q ((m : ℝ) + 1) := qNumber_pos hq0 hq1 (by positivity)
  have hqm1x : qNumber q ((m : ℝ) + 1) ^ x ≠ 0 := (Real.rpow_pos_of_pos hqm1 x).ne'
  have hP0 : (∏ j ∈ range (m + 1), qNumber q (x + j)) ≠ 0 :=
    (prod_pos fun j _ => qNumber_pos hq0 hq1 (by positivity)).ne'
  unfold qGammaLowerSeq qGammaUpperSeq
  rw [Real.div_rpow (qNumber_nonneg hq0 hq1 (Nat.cast_nonneg m)) hqm1.le]
  field_simp

/-- **The lower approximants converge to `Γ_q(x)` too.**  The ratio `[m]_q/[m+1]_q` tends to `1`,
so `L_m = ([m]_q/[m+1]_q)^x U_m` has the same limit as `U_m`. -/
theorem tendsto_qGammaLowerSeq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x) :
    Tendsto (qGammaLowerSeq q x) atTop (𝓝 (qGamma q x)) := by
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hratio : Tendsto (fun m : ℕ => (qNumber q m / qNumber q ((m : ℝ) + 1)) ^ x) atTop
      (𝓝 1) := by
    have hnum : Tendsto (fun m : ℕ => qNumber q m) atTop (𝓝 ((1 - 0) / (1 - q))) := by
      unfold qNumber
      simp_rw [Real.rpow_natCast]
      exact (tendsto_const_nhds.sub
        (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1)).div_const _
    have hden : Tendsto (fun m : ℕ => qNumber q ((m : ℝ) + 1)) atTop
        (𝓝 ((1 - 0) / (1 - q))) := by
      unfold qNumber
      simp_rw [← Nat.cast_succ, Real.rpow_natCast]
      exact (tendsto_const_nhds.sub
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1).comp
          (tendsto_add_atTop_nat 1))).div_const _
    have hne : (1 - 0) / (1 - q) ≠ 0 := by
      rw [sub_zero]
      exact (one_div_pos.mpr h1q).ne'
    have h := (hnum.div hden hne).rpow_const (Or.inr hx0.le)
    rwa [div_self hne, Real.one_rpow] at h
  have h := hratio.mul (tendsto_qGammaUpperSeq hq0 hq1 hx0)
  rw [one_mul] at h
  exact h.congr fun m => (qGammaLowerSeq_eq_mul_qGammaUpperSeq hq0 hq1 hx0 m).symm

/-- **The upper half of the Artin bracket**: `Γ_q(x) ≤ U_m(q,x)` for `0 < q < 1`, `0 < x ≤ 1` and
*every* `m` (including `m = 0`).  The upper approximants decrease to `Γ_q(x)`. -/
theorem qGamma_le_qGammaUpperSeq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1)
    (m : ℕ) : qGamma q x ≤ qGammaUpperSeq q x m :=
  (qGammaUpperSeq_antitone hq0 hq1 hx0 hx1).le_of_tendsto
    (tendsto_qGammaUpperSeq hq0 hq1 hx0) m

/-- **The lower half of the Artin bracket**: `L_m(q,x) ≤ Γ_q(x)` for `0 < q < 1`, *every* `x > 0`
and every `m`.  Unlike the upper bound this needs no upper bound on `x`: the lower approximants
increase to `Γ_q(x)`. -/
theorem qGammaLowerSeq_le_qGamma (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x) (m : ℕ) :
    qGammaLowerSeq q x m ≤ qGamma q x :=
  (qGammaLowerSeq_monotone hq0 hq1 hx0).ge_of_tendsto (tendsto_qGammaLowerSeq hq0 hq1 hx0) m

/-- **The two-sided Artin bracket for `Γ_q`, without log-convexity.**  For `0 < q < 1`,
`0 < x ≤ 1` and every `m : ℕ`,

`[m]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q) ≤ Γ_q(x) ≤ [m+1]_q^x [1]_q⋯[m]_q / ([x]_q⋯[x+m]_q)`.

Compare `qGamma_two_sided_bound`, which assumes `1 ≤ m` and `x < 1` and goes through the second
logarithmic derivative of `Γ_q`. -/
theorem qGammaLowerSeq_le_and_le_qGammaUpperSeq (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) (m : ℕ) :
    qGammaLowerSeq q x m ≤ qGamma q x ∧ qGamma q x ≤ qGammaUpperSeq q x m :=
  ⟨qGammaLowerSeq_le_qGamma hq0 hq1 hx0 m, qGamma_le_qGammaUpperSeq hq0 hq1 hx0 hx1 m⟩

/-- **An explicit error bound for the upper approximants.**  For `0 < q < 1`, `0 < x ≤ 1` and every
`m`, the error of `U_m(q,x)` as an approximation to `Γ_q(x)` is at most the width of the bracket:

`|Γ_q(x) - U_m(q,x)| ≤ (1 - ([m]_q/[m+1]_q)^x) U_m(q,x)`. -/
theorem abs_qGamma_sub_qGammaUpperSeq_le (hq0 : 0 < q) (hq1 : q < 1) {x : ℝ} (hx0 : 0 < x)
    (hx1 : x ≤ 1) (m : ℕ) :
    |qGamma q x - qGammaUpperSeq q x m|
      ≤ (1 - (qNumber q (m : ℝ) / qNumber q ((m : ℝ) + 1)) ^ x) * qGammaUpperSeq q x m := by
  have hupper := qGamma_le_qGammaUpperSeq hq0 hq1 hx0 hx1 m
  have hlower := qGammaLowerSeq_le_qGamma hq0 hq1 hx0 m
  rw [qGammaLowerSeq_eq_mul_qGammaUpperSeq hq0 hq1 hx0 m] at hlower
  have hle : qGamma q x - qGammaUpperSeq q x m ≤ 0 := by linarith
  rw [abs_of_nonpos hle]
  linarith

end Fabius

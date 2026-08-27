import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

/-!
# Finite products of integer powers, through the exponential

Every infinite product studied in the Thue–Morse atlas — Woods–Robbins, the
two-parameter master product, the dyadic block products, the quarter product —
is a limit of finite products `∏ f i ^ e i` with `f i > 0` and `e i : ℤ`, and
every one of them is evaluated by passing to the signed logarithm sum
`∑ (e i) · log (f i)`.  This module isolates that passage once and for all.

Nothing here mentions the Thue–Morse sequence: the exponent sequence `e` is
arbitrary, the index type is arbitrary, and the filter along which limits are
taken is arbitrary.

* `prod_zpow_eq_exp_sum` — `∏ i ∈ s, f i ^ e i = exp (∑ i ∈ s, e i · log (f i))`.
* `tendsto_prod_zpow_of_tendsto_sum` — the limit transfer: a limit of signed
  logarithm sums exponentiates to a limit of the products.
* `exp_neg_mul_log`, `exp_neg_log_div_two` — the two value computations that
  turn such a limit into a closed form.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- A finite product of integer powers of positive reals is the exponential of
the corresponding signed logarithm sum. -/
theorem prod_zpow_eq_exp_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) (e : ι → ℤ)
    (hf : ∀ i ∈ s, 0 < f i) :
    ∏ i ∈ s, f i ^ e i = Real.exp (∑ i ∈ s, (e i : ℝ) * Real.log (f i)) := by
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [← Real.rpow_intCast (f i) (e i), Real.rpow_def_of_pos (hf i hi)]
  congr 1
  ring

/-- **Limit transfer.**  If the signed logarithm sums converge, so do the
products, to the exponential of the limit. -/
theorem tendsto_prod_zpow_of_tendsto_sum {ι α : Type*} {l : Filter α}
    (s : α → Finset ι) (f : ι → ℝ) (e : ι → ℤ) (hf : ∀ i, 0 < f i) {L : ℝ}
    (h : Tendsto (fun m => ∑ i ∈ s m, (e i : ℝ) * Real.log (f i)) l (𝓝 L)) :
    Tendsto (fun m => ∏ i ∈ s m, f i ^ e i) l (𝓝 (Real.exp L)) :=
  Tendsto.congr
    (fun m => (prod_zpow_eq_exp_sum (s m) f e fun i _ => hf i).symm)
    ((Real.continuous_exp.tendsto _).comp h)

/-- `exp (-(c · log b)) = 1 / b ^ c` for positive `b`: the value computation
behind every closed form in the atlas's product row. -/
theorem exp_neg_mul_log {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Real.exp (-(c * Real.log b)) = 1 / b ^ c := by
  rw [Real.rpow_def_of_pos hb, one_div, ← Real.exp_neg]
  congr 1
  ring

/-- The half-power case: `exp (-log b / 2) = 1 / √b`. -/
theorem exp_neg_log_div_two {b : ℝ} (hb : 0 < b) :
    Real.exp (-Real.log b / 2) = 1 / Real.sqrt b := by
  rw [Real.sqrt_eq_rpow, ← exp_neg_mul_log hb]
  congr 1
  ring

/-- The three-halves-power case: `exp (-(3/2)·log b) = 1 / (b·√b)`. -/
theorem exp_neg_three_halves_log {b : ℝ} (hb : 0 < b) :
    Real.exp (-(3 / 2 * Real.log b)) = 1 / (b * Real.sqrt b) := by
  rw [exp_neg_mul_log hb, Real.sqrt_eq_rpow,
    show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hb, Real.rpow_one]

end Fabius

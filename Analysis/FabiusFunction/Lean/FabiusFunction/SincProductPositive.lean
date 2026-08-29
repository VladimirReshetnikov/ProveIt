import FabiusFunction.SincLowerBound
import FabiusFunction.WeakConvergence
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The infinite dyadic sinc product

`SincLowerBound` bounds every *finite* dyadic sinc product from
below: whenever `t² ≤ 6`,

`1 - 2t²/9 ≤ ∏_{n<N} sinc(t/2ⁿ)`,

uniformly in `N`.  This module passes to the limit.

Two separate things are needed.  First, genuine multipliability: the
factors are `1 + (sinc(t/2ⁿ) - 1)` with deficits controlled by the
two-sided estimate `|sinc x - 1| ≤ x²/6` — the upper bound
`Real.sinc_le_one` on one side, the corpus's quadratic lower bound on
the other — so the deficits are dominated by the geometric series
`t²/(6·4ⁿ)` and `Real.multipliable_one_add_of_summable` applies.  No
smallness of `t` enters here: the dyadic family is multipliable for
*every* real base argument, which is more than the finite bound
needs.  Second, the passage to the limit: multipliability makes the
`Finset.range` products converge to `∏'`, and a bound holding at
every `N` is inherited by the limit.

At `t = π/2` the bound reads `1 - π²/18 > 4/9`, and those are exactly
the factors of the corpus's `rvachevFourierProduct` at `z = 1/2`,
whose `n`-th factor is `sinc(π/2 / 2ⁿ) = sinc(π/2ⁿ⁺¹)`.  Casting the
real product along the ring hom `Complex.ofRealHom` identifies
`Φ(1/2)` as a real number exceeding `4/9`.  (That it is nonzero is
already known from `rvachevFourierProduct_eq_zero_iff`; what is new
is the explicit constant.)

## Main declarations

* `Fabius.multipliable_sinc_two_pow` — **the dyadic sinc family is
  multipliable**, for every real base argument.
* `Fabius.one_sub_le_tprod_sinc_two_pow` — **the infinite product
  bound** `1 - 2t²/9 ≤ ∏' n, sinc(t/2ⁿ)` for `t² ≤ 6`.
* `Fabius.tprod_sinc_two_pow_pos` — the infinite product is strictly
  positive as soon as `2t² < 9`.
* `Fabius.four_ninths_lt_tprod_sinc_pi_div_two` — at `t = π/2` the
  infinite product exceeds `4/9`.
* `Fabius.rvachevFourierProduct_half_eq_ofReal` — `Φ(1/2)` is the
  real dyadic sinc product at `π/2`, cast to `ℂ`.
* `Fabius.four_ninths_lt_re_rvachevFourierProduct_half` — hence
  `4/9 < Re Φ(1/2)`.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Fabius

/-! ## Multipliability of the dyadic sinc family -/

/-- The sinc deviation from one is quadratically small, in absolute
value: the upper side is `Real.sinc_le_one`, the lower side is the
corpus's `one_sub_sq_div_six_le_sinc`. -/
private theorem abs_sinc_sub_one_le (x : ℝ) :
    |Real.sinc x - 1| ≤ x ^ 2 / 6 := by
  have hle : Real.sinc x ≤ 1 := Real.sinc_le_one x
  have hge : 1 - x ^ 2 / 6 ≤ Real.sinc x :=
    one_sub_sq_div_six_le_sinc x
  have hpos : (0 : ℝ) ≤ x ^ 2 / 6 := by positivity
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The dyadic deficit majorant `t²/(6·4ⁿ)` is a geometric series. -/
private theorem summable_dyadic_deficit (t : ℝ) :
    Summable (fun n : ℕ => t ^ 2 / (6 * 4 ^ n)) := by
  have hgeom : Summable (fun n : ℕ => ((1 : ℝ) / 4) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (hgeom.mul_left (t ^ 2 / 6)).congr fun n => ?_
  rw [div_pow, one_pow, mul_one_div, div_div]

/-- **The dyadic sinc family is multipliable.**  Its factors are
`1 + (sinc(t/2ⁿ) - 1)` with `|sinc(t/2ⁿ) - 1| ≤ t²/(6·4ⁿ)`, a
summable majorant, so `Real.multipliable_one_add_of_summable`
applies.  No hypothesis on `t` is required: the estimate is
quadratic in the *scaled* argument, and the scaling alone already
forces the deficits to be summable. -/
theorem multipliable_sinc_two_pow (t : ℝ) :
    Multipliable (fun n : ℕ => Real.sinc (t / 2 ^ n)) := by
  have hbound : ∀ n : ℕ,
      ‖Real.sinc (t / 2 ^ n) - 1‖ ≤ t ^ 2 / (6 * 4 ^ n) := by
    intro n
    have h4 : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
      rw [pow_two, ← mul_pow]
      norm_num
    have harg : (t / 2 ^ n) ^ 2 / 6 = t ^ 2 / (6 * 4 ^ n) := by
      rw [div_pow, ← h4]
      ring
    have h := abs_sinc_sub_one_le (t / 2 ^ n)
    rw [harg] at h
    rw [Real.norm_eq_abs]
    exact h
  have hsum : Summable (fun n : ℕ => Real.sinc (t / 2 ^ n) - 1) :=
    Summable.of_norm_bounded (summable_dyadic_deficit t) hbound
  exact (Real.multipliable_one_add_of_summable hsum).congr
    fun n => by ring

/-! ## The infinite product bound -/

/-- **The infinite dyadic sinc product bound**: whenever the base
argument satisfies `t² ≤ 6`,

`1 - 2t²/9 ≤ ∏' n, sinc(t/2ⁿ)`.

The family is multipliable, so the `Finset.range` partial products
converge to the infinite product; each of them obeys the finite bound
`one_sub_le_prod_sinc_two_pow`, and a constant lower bound valid at
every `N` passes to the limit. -/
theorem one_sub_le_tprod_sinc_two_pow {t : ℝ} (ht : t ^ 2 ≤ 6) :
    1 - 2 * t ^ 2 / 9 ≤ ∏' n : ℕ, Real.sinc (t / 2 ^ n) :=
  ge_of_tendsto' (multipliable_sinc_two_pow t).tendsto_prod_tprod_nat
    fun N => one_sub_le_prod_sinc_two_pow ht N

/-- The infinite dyadic sinc product has no hidden zero once the
deficit budget `2t²` stays below `9`.  The hypothesis `t² < 9/2` is
strictly stronger than the `t² ≤ 6` of the bound itself, which at
`t² = 6` degenerates to the uninformative `-1/3 ≤ ∏'`. -/
theorem tprod_sinc_two_pow_pos {t : ℝ} (ht : 2 * t ^ 2 < 9) :
    0 < ∏' n : ℕ, Real.sinc (t / 2 ^ n) := by
  have ht6 : t ^ 2 ≤ 6 := by linarith
  have h := one_sub_le_tprod_sinc_two_pow ht6
  linarith

/-- **The half-integer dyadic sinc product exceeds `4/9`**: at
`t = π/2` the bound of `one_sub_le_tprod_sinc_two_pow` reads
`1 - π²/18`, and `π² < 10` puts that above `4/9`. -/
theorem four_ninths_lt_tprod_sinc_pi_div_two :
    4 / 9 < ∏' n : ℕ, Real.sinc (Real.pi / 2 / 2 ^ n) := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq : (Real.pi / 2) ^ 2 ≤ 6 := by nlinarith [hpi, hpi0]
  have h := one_sub_le_tprod_sinc_two_pow hsq
  have hlt : (4 : ℝ) / 9 < 1 - 2 * (Real.pi / 2) ^ 2 / 9 := by
    nlinarith [hpi, hpi0]
  exact hlt.trans_le h

/-! ## The Rvachev product at the half frequency -/

/-- **`Φ(1/2)` is a real dyadic sinc product.**  The corpus's
`rvachevFourierProduct` indexes its factors as `sinc(π z / 2ⁿ)`, so
at `z = 1/2` the `n`-th factor is `sinc(π/2 / 2ⁿ)`: exactly the real
family of `four_ninths_lt_tprod_sinc_pi_div_two`, transported into
`ℂ` by `complexSinc_ofReal`.  The whole product transports as well,
because `Complex.ofRealHom` is a continuous ring hom and the real
family is multipliable. -/
theorem rvachevFourierProduct_half_eq_ofReal :
    rvachevFourierProduct (1 / 2 : ℂ) =
      ((∏' n : ℕ, Real.sinc (Real.pi / 2 / 2 ^ n) : ℝ) : ℂ) := by
  have hmul : Multipliable
      (fun n : ℕ => Real.sinc (Real.pi / 2 / 2 ^ n)) :=
    multipliable_sinc_two_pow (Real.pi / 2)
  have hcont : Continuous (Complex.ofRealHom : ℝ → ℂ) :=
    Complex.continuous_ofReal
  have hmap : ((∏' n : ℕ, Real.sinc (Real.pi / 2 / 2 ^ n) : ℝ) : ℂ) =
      ∏' n : ℕ, ((Real.sinc (Real.pi / 2 / 2 ^ n) : ℝ) : ℂ) :=
    hmul.map_tprod Complex.ofRealHom hcont
  have hfac : ∀ n : ℕ,
      complexSinc ((Real.pi : ℂ) * (1 / 2 : ℂ) / (2 : ℂ) ^ n) =
        ((Real.sinc (Real.pi / 2 / 2 ^ n) : ℝ) : ℂ) := by
    intro n
    have harg : (Real.pi : ℂ) * (1 / 2 : ℂ) / (2 : ℂ) ^ n =
        ((Real.pi / 2 / 2 ^ n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, complexSinc_ofReal]
  rw [rvachevFourierProduct, hmap]
  exact tprod_congr hfac

/-- **The Rvachev sinc product at the half frequency exceeds `4/9`.**
Combining the identification of `Φ(1/2)` as a real product with the
quantitative bound.  The corpus already knows `Φ(1/2) ≠ 0` from
`rvachevFourierProduct_eq_zero_iff`; the content here is the explicit
constant, which is what a "the tail cannot eat the first harmonic"
argument actually consumes. -/
theorem four_ninths_lt_re_rvachevFourierProduct_half :
    4 / 9 < (rvachevFourierProduct (1 / 2 : ℂ)).re := by
  rw [rvachevFourierProduct_half_eq_ofReal, Complex.ofReal_re]
  exact four_ninths_lt_tprod_sinc_pi_div_two

/-! ## An explicit nonvanishing window -/

/-- **`Φ` at a real point is a real dyadic sinc product**, at every
real `x`.  The half-frequency identification is the case
`x = 1/2`. -/
theorem rvachevFourierProduct_ofReal_eq_tprod_sinc (x : ℝ) :
    rvachevFourierProduct ((x : ℝ) : ℂ) =
      ((∏' n : ℕ, Real.sinc (Real.pi * x / 2 ^ n) : ℝ) : ℂ) := by
  have hmul : Multipliable
      (fun n : ℕ => Real.sinc (Real.pi * x / 2 ^ n)) :=
    multipliable_sinc_two_pow (Real.pi * x)
  have hcont : Continuous (Complex.ofRealHom : ℝ → ℂ) :=
    Complex.continuous_ofReal
  have hmap : ((∏' n : ℕ, Real.sinc (Real.pi * x / 2 ^ n) : ℝ) : ℂ) =
      ∏' n : ℕ, ((Real.sinc (Real.pi * x / 2 ^ n) : ℝ) : ℂ) :=
    hmul.map_tprod Complex.ofRealHom hcont
  have hfac : ∀ n : ℕ,
      complexSinc ((Real.pi : ℂ) * ((x : ℝ) : ℂ) / (2 : ℂ) ^ n) =
        ((Real.sinc (Real.pi * x / 2 ^ n) : ℝ) : ℂ) := by
    intro n
    have harg : (Real.pi : ℂ) * ((x : ℝ) : ℂ) / (2 : ℂ) ^ n =
        ((Real.pi * x / 2 ^ n : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, complexSinc_ofReal]
  rw [rvachevFourierProduct, hmap]
  exact tprod_congr hfac

/-- The quantitative lower bound transported to the transform: for
`(πx)² ≤ 6`, `1 - 2(πx)²/9 ≤ Re Φ(x)`. -/
theorem one_sub_le_re_rvachevFourierProduct_ofReal {x : ℝ}
    (hx : (Real.pi * x) ^ 2 ≤ 6) :
    1 - 2 * (Real.pi * x) ^ 2 / 9 ≤
      (rvachevFourierProduct ((x : ℝ) : ℂ)).re := by
  rw [rvachevFourierProduct_ofReal_eq_tprod_sinc x, Complex.ofReal_re]
  exact one_sub_le_tprod_sinc_two_pow hx

/-- **The nonvanishing window**: whenever the deficit budget
`2(πx)²` stays below `9`, `Φ(x)` is real and strictly positive. -/
theorem re_rvachevFourierProduct_ofReal_pos {x : ℝ}
    (hx : 2 * (Real.pi * x) ^ 2 < 9) :
    0 < (rvachevFourierProduct ((x : ℝ) : ℂ)).re := by
  have hx6 : (Real.pi * x) ^ 2 ≤ 6 := by linarith
  have h := one_sub_le_re_rvachevFourierProduct_ofReal hx6
  linarith

/-- In particular `Φ` has no zero in that window. -/
theorem rvachevFourierProduct_ofReal_ne_zero {x : ℝ}
    (hx : 2 * (Real.pi * x) ^ 2 < 9) :
    rvachevFourierProduct ((x : ℝ) : ℂ) ≠ 0 := by
  intro h
  have hpos := re_rvachevFourierProduct_ofReal_pos hx
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- A concrete window: `Φ` is positive on `|x| ≤ 2/3`, since
`2(2π/3)² < 9` already follows from `π < 3.15`. -/
theorem re_rvachevFourierProduct_ofReal_pos_of_abs_le {x : ℝ}
    (hx : |x| ≤ 2 / 3) :
    0 < (rvachevFourierProduct ((x : ℝ) : ℂ)).re := by
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have hxsq : x ^ 2 ≤ (2 / 3) ^ 2 := by
    have habs : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x, hx]
  refine re_rvachevFourierProduct_ofReal_pos ?_
  have hmul : (Real.pi * x) ^ 2 = Real.pi ^ 2 * x ^ 2 := by ring
  nlinarith [hpi, hpi0, hxsq, sq_nonneg x]

/-! ## The window for the characteristic function -/

/-- The up-measure's characteristic function is the real dyadic sinc
product at the rescaled frequency: `charFun μ_up t = Φ(t/2π)`, and
`Φ` at a real point is real. -/
theorem charFun_rvachevMeasure_eq_ofReal (F : BoundedFabius)
    (hF : IsFabius F) (t : ℝ) :
    charFun (rvachevMeasure F) t =
      ((∏' n : ℕ, Real.sinc (Real.pi * (t / (2 * Real.pi)) / 2 ^ n) :
        ℝ) : ℂ) := by
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    simp [Complex.ofReal_ne_zero, Real.pi_ne_zero]
  rw [rvachevMeasure_charFun_pos F hF t, rvachevFourier_eq_product F hF]
  have harg : ((t : ℂ) / (2 * Real.pi)) =
      (((t / (2 * Real.pi) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [harg, rvachevFourierProduct_ofReal_eq_tprod_sinc]

/-- **The characteristic function does not vanish on `|t| < 3√2`**:
with `x = t/2π` the deficit budget is `2(t/2)² = t²/2`, so the window
`2(πx)² < 9` reads `t² < 18`.  In particular the up-law's
characteristic function is real and strictly positive there. -/
theorem re_charFun_rvachevMeasure_pos (F : BoundedFabius)
    (hF : IsFabius F) {t : ℝ} (ht : t ^ 2 < 18) :
    0 < (charFun (rvachevMeasure F) t).re := by
  have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
  have harg : Real.pi * (t / (2 * Real.pi)) = t / 2 := by
    field_simp
    ring
  have hbudget : 2 * (Real.pi * (t / (2 * Real.pi))) ^ 2 < 9 := by
    rw [harg]
    nlinarith [ht]
  have h := re_rvachevFourierProduct_ofReal_pos hbudget
  rw [rvachevMeasure_charFun_pos F hF t, rvachevFourier_eq_product F hF]
  have hcast : ((t : ℂ) / (2 * Real.pi)) =
      (((t / (2 * Real.pi) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hcast]
  exact h

/-- Consequently the characteristic function has no zero there. -/
theorem charFun_rvachevMeasure_ne_zero (F : BoundedFabius)
    (hF : IsFabius F) {t : ℝ} (ht : t ^ 2 < 18) :
    charFun (rvachevMeasure F) t ≠ 0 := by
  intro h
  have hpos := re_charFun_rvachevMeasure_pos F hF ht
  rw [h, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- The concrete form: no zero for `|t| ≤ 4`, since `16 < 18`. -/
theorem charFun_rvachevMeasure_ne_zero_of_abs_le_four
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : |t| ≤ 4) :
    charFun (rvachevMeasure F) t ≠ 0 := by
  refine charFun_rvachevMeasure_ne_zero F hF ?_
  have habs : |t| ^ 2 = t ^ 2 := sq_abs t
  nlinarith [abs_nonneg t, ht]

end Fabius

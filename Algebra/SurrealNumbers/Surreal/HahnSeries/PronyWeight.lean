import Surreal.HahnSeries.PronyLocalRoots
import Surreal.HahnSeries.PronyRows
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Tactic.LinearCombination

/-!
# Weight errors and affine normalization in Prony reconstruction

This file proves `prony:lem:weight`, with `prony:eq:qval` and `prony:eq:weightdd`, and the
affine normalization `prony:eq:affine` of
`docs/surcomplex/prony-reconstruction-at-surreal-scales/article.tex`.

## Divided differences

Over any commutative ring, `divDiff p x y` is the value at `y - x` of `divX (taylor x p)`. It
satisfies `p(y) = p(x) + (y - x) [x, y] p` (`eval_eq_add_mul_divDiff`), and at coincident
arguments it is the derivative, `[x, x] p = p'(x)` (`divDiff_self`). The product rule
`[x, y](p q) = [x, y] p · q(y) + p(x) · [x, y] q` (`divDiff_mul`) holds at all arguments.

## The weight estimate

Field part, over any field. Let `P = ∏ (X - a_j)` with cofactors `Q_i`, `A = ∑ w_j Q_j`,
`P̂ = ∏ (X - â_j)` with cofactors `Q̂_i`, `Â` any polynomial and `D = Â P - A P̂`. Put
`q = Q_i Q̂_i` (the source's `Q_i · P̂/(X - â_i)`) and `ŵ_i = Â(â_i)/Q̂_i(â_i)`. This is the
source's `Â(â_i)/P̂'(â_i)`, since `P̂'(â_i) = Q̂_i(â_i)` (`Surreal.Prony.eval_derivative_nodePoly`).

* `divDiff_cross`: `[a_i, â_i] D = Â(â_i) Q_i(â_i) - w_i q(a_i)`, and `eval_cross_node`:
  `D(a_i) = w_i (â_i - a_i) q(a_i)`.
* `weight_identity`: `(ŵ_i - w_i) q(a_i) q(â_i) = [a_i, â_i] D · q(a_i) - D(a_i) [a_i, â_i] q`.
  This is the source's quotient identity for `[a_i, â_i] F`, `F = D/q`, cleared of
  denominators. It holds for every `â_i` with `Q̂_i(â_i) ≠ 0`, coincident with `a_i` or not.
* `weightdd` (`prony:eq:weightdd`): for `â_i ≠ a_i` with `q(a_i), q(â_i) ≠ 0`,
  `ŵ_i - w_i = (F(â_i) - F(a_i))/(â_i - a_i)`. `weightdd_self`: for `â_i = a_i` with
  `q(a_i) ≠ 0`, `D(a_i) = 0` and `ŵ_i - w_i = D'(a_i)/q(a_i) = F'(a_i)`.
  `weightdd_derivative` restates `weightdd`, and `weightdd_self_derivative` restates the
  weight equality of `weightdd_self`, with the source's `ŵ_i = Â(â_i)/P̂'(â_i)`.

Hahn part, over `R((t^Γ))` with `R` any field and `Γ` any linearly ordered abelian group (the
source takes `R = ℝ` or `ℂ`).

* `le_orderTop_divDiff`: if every coefficient of `p` has valuation `≥ κ` and `x, y` are
  integral, then `v([x, y] p) ≥ κ`. `le_orderTop_eval_derivative` is the coincident case
  `v(p'(x)) ≥ κ`, and `le_orderTop_divDiff_prod` is the telescoping bound for a product of
  linear factors.
* `orderTop_eval_qval` (`prony:eq:qval`): `v(q(a_i)) = v(q(â_i)) = 2 d_i`, so
  `q(a_i) ≠ 0` and `q(â_i) ≠ 0` (`eval_qval_ne_zero`).
  `le_orderTop_divDiff_qval`: `v([a_i, â_i] q) ≥ 2 d_i - δ_i`.
* `weight_bound` (`prony:lem:weight`). Let the nodes `a_i` be integral, let `δ_i ≥ 0` bound
  `v(a_i - a_j)` for `j ≠ i`, let `v(â_i - a_i) > δ_i`, let `P̂ = ∏ (X - â_j)` satisfy
  `L̂(P̂ X^r) = 0` for `r < n`, with `Â` its Padé numerator, and let
  `v(m̂_k - m_k) ≥ κ` for `k < 2n`. Then `v(ŵ_i - w_i) ≥ κ - 2 d_i - δ_i` with
  `ŵ_i = Â(â_i)/P̂'(â_i)`. No hypothesis on the weights `w` is needed, and integrality of
  `P̂` follows from the ball condition. `weight_bound_sepMax` is the source's normalization
  `δ_i = max_{j ≠ i} d_ij` (`0` for `n = 1`), through `Surreal.PronyRows.sepMax`, and
  `weight_bound_of_isRoot` takes `P̂` as any monic polynomial of degree `n` with the roots
  `â_i`.

## Affine normalization

`normMoment c ρ m k = ρ^{-k} ∑_{l ≤ k} (k choose l) (-c)^{k-l} m_l` is the right-hand side of
`prony:eq:affine`, over any field.

* `normMoment_eq_momentLinear` and `momentLinear_normMoment`: the normalized functional is
  `f ↦ L(f((X - c)/ρ))`.
* `normMoment_moment`: the normalized moments of `(a, w)` are the moments of `(x, w)`,
  `x_i = (a_i - c)/ρ`. `normMoment_add`, `normMoment_sub`, `normMoment_sub_moment`: the same
  linear map is applied to the errors.
* `normMoment_normMoment` and `moment_affine_iff`: `(x̂, ŵ)` realizes the normalized perturbed
  moments `m̂_k`, `k < N`, if and only if `(c + ρ x̂, ŵ)` realizes the original ones.
* `le_orderTop_normMoment`: if `v(ε_l) ≥ κ_l` for `l ≤ k`, then
  `v(ε^norm_k) ≥ min (κ_l + (k - l) v(c) - k v(ρ))` over the `l ≤ k` whose coefficient
  `(k choose l) (-c)^{k-l}` is nonzero. `le_orderTop_normMoment_of_inf` is the unrestricted
  minimum, and `normMoment_zero_left`, `le_orderTop_normMoment_zero` treat `c = 0`, where only
  `l = k` contributes.
* `orderTop_translate_back`, `orderTop_node_error`: translating back adds `v(ρ)` to every
  node-error valuation; the weights are unchanged. `exists_integral_normalization`: every
  finite configuration becomes integral after a scaling.

Nothing in `prony:lem:weight`, `prony:eq:qval`, `prony:eq:weightdd` or `prony:eq:affine` is
pending. The assembly of the reconstruction assertions of `prony:thm:main` from these lemmas is
not done here.
-/

namespace Surreal.PronyWeight

open Polynomial Finset Surreal.Prony

noncomputable section

section DividedDifference

variable {K : Type*} [CommRing K]

/-- The divided difference `[x, y] p`, the value at `y - x` of `divX (taylor x p)`. It satisfies
`p(y) = p(x) + (y - x) [x, y] p`, and `[x, x] p = p'(x)`. -/
def divDiff (p : K[X]) (x y : K) : K :=
  (divX (taylor x p)).eval (y - x)

/-- The defining property of the divided difference: `p(y) = p(x) + (y - x) [x, y] p`. -/
theorem eval_eq_add_mul_divDiff (p : K[X]) (x y : K) :
    p.eval y = p.eval x + (y - x) * divDiff p x y := by
  have h := congrArg (eval (y - x)) (divX_mul_X_add (taylor x p))
  rw [eval_add, eval_mul, eval_X, eval_C, taylor_coeff_zero, taylor_eval, sub_add_cancel] at h
  rw [divDiff, ← h]
  ring

/-- At coincident arguments the divided difference is the derivative: `[x, x] p = p'(x)`. -/
theorem divDiff_self (p : K[X]) (x : K) : divDiff p x x = p.derivative.eval x := by
  rw [divDiff, sub_self, ← coeff_zero_eq_eval_zero, coeff_divX, zero_add, taylor_coeff_one]

theorem divX_sub_eq (p q : K[X]) : divX (p - q) = divX p - divX q := by
  ext k
  simp only [coeff_divX, coeff_sub]

theorem divDiff_sub (p q : K[X]) (x y : K) :
    divDiff (p - q) x y = divDiff p x y - divDiff q x y := by
  rw [divDiff, map_sub, divX_sub_eq, eval_sub, divDiff, divDiff]

/-- `divX` of a product: `divX (F G) = divX F · G + F(0) · divX G`. -/
theorem divX_mul_eq_add (F G : K[X]) :
    divX (F * G) = divX F * G + C (F.coeff 0) * divX G := by
  have hF := X_mul_divX_add F
  have hG := X_mul_divX_add G
  have hFG := X_mul_divX_add (F * G)
  rw [mul_coeff_zero, C_mul] at hFG
  have h : X * divX (F * G) = X * (divX F * G + C (F.coeff 0) * divX G) := by
    linear_combination hFG - G * hF - C (F.coeff 0) * hG
  ext k
  have hk := congrArg (fun p : K[X] => p.coeff (k + 1)) h
  simpa only [coeff_X_mul] using hk

/-- The product rule for divided differences, valid at all arguments:
`[x, y](p q) = [x, y] p · q(y) + p(x) · [x, y] q`. -/
theorem divDiff_mul (p q : K[X]) (x y : K) :
    divDiff (p * q) x y = divDiff p x y * q.eval y + p.eval x * divDiff q x y := by
  simp only [divDiff]
  rw [taylor_mul, divX_mul_eq_add, eval_add, eval_mul, eval_mul, eval_C, taylor_coeff_zero,
    taylor_eval, sub_add_cancel]

theorem divDiff_C (c x y : K) : divDiff (C c) x y = 0 := by
  rw [divDiff, taylor_C, divX_C, eval_zero]

theorem divDiff_one (x y : K) : divDiff 1 x y = 0 := by
  rw [← C_1, divDiff_C]

theorem divDiff_X_sub_C (c x y : K) : divDiff (X - C c) x y = 1 := by
  have h : divX (taylor x (X - C c)) = 1 := by
    ext k
    rw [coeff_divX, map_sub, taylor_X, taylor_C, coeff_sub, coeff_add, coeff_X, coeff_C, coeff_C,
      coeff_one]
    rcases k with _ | k <;> simp
  rw [divDiff, h, eval_one]

end DividedDifference

section WeightField

variable {K : Type*} [Field K] {n : ℕ}

theorem eval_cofactor (c : Fin n → K) (i : Fin n) (x : K) :
    (cofactor c i).eval x = ∏ j ∈ univ.erase i, (x - c j) := by
  rw [cofactor, eval_prod]
  simp only [eval_sub, eval_X, eval_C]

/-- The cross numerator `D = Â P - A P̂` at a node: `D(a_i) = w_i (â_i - a_i) Q_i(a_i) Q̂_i(a_i)`,
for every polynomial `Â`. -/
theorem eval_cross_node (a â w : Fin n → K) (Â : K[X]) (i : Fin n) :
    (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) =
      w i * (â i - a i) * ((cofactor a i).eval (a i) * (cofactor â i).eval (a i)) := by
  rw [eval_sub, eval_mul, eval_mul, (eval_nodePoly_eq_zero_iff a _).mpr ⟨i, rfl⟩,
    eval_sum_C_mul_cofactor, nodePoly_eq_mul_cofactor â i, eval_mul, eval_sub, eval_X, eval_C]
  ring

/-- The divided difference of the cross numerator between `a_i` and `â_i`:
`[a_i, â_i] D = Â(â_i) Q_i(â_i) - w_i Q_i(a_i) Q̂_i(a_i)`. It holds also when `â_i = a_i`. -/
theorem divDiff_cross (a â w : Fin n → K) (Â : K[X]) (i : Fin n) :
    divDiff (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â) (a i) (â i) =
      Â.eval (â i) * (cofactor a i).eval (â i) -
        w i * ((cofactor a i).eval (a i) * (cofactor â i).eval (a i)) := by
  have hÂ := eval_eq_add_mul_divDiff Â (a i) (â i)
  have hQ := eval_eq_add_mul_divDiff (cofactor â i) (a i) (â i)
  rw [divDiff_sub, nodePoly_eq_mul_cofactor a i, nodePoly_eq_mul_cofactor â i, divDiff_mul,
    divDiff_mul, divDiff_mul, divDiff_mul, divDiff_X_sub_C, divDiff_X_sub_C]
  simp only [eval_mul, eval_sub, eval_X, eval_C, eval_sum_C_mul_cofactor]
  linear_combination (-(cofactor a i).eval (â i)) * hÂ - (w i * (cofactor a i).eval (a i)) * hQ

/-- The identity behind `prony:eq:weightdd`, cleared of denominators. With `q = Q_i Q̂_i` and
`ŵ_i = Â(â_i)/Q̂_i(â_i)`,
`(ŵ_i - w_i) q(a_i) q(â_i) = [a_i, â_i] D · q(a_i) - D(a_i) · [a_i, â_i] q`.
It holds for every `â_i` with `Q̂_i(â_i) ≠ 0`, coincident with `a_i` or not; without that
hypothesis `ŵ_i` is not defined. -/
theorem weight_identity (a â w : Fin n → K) (Â : K[X]) (i : Fin n)
    (hQ : (cofactor â i).eval (â i) ≠ 0) :
    (Â.eval (â i) / (cofactor â i).eval (â i) - w i) *
        ((cofactor a i * cofactor â i).eval (a i) * (cofactor a i * cofactor â i).eval (â i)) =
      divDiff (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â) (a i) (â i) *
          (cofactor a i * cofactor â i).eval (a i) -
        (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) *
          divDiff (cofactor a i * cofactor â i) (a i) (â i) := by
  have hq := eval_eq_add_mul_divDiff (cofactor a i * cofactor â i) (a i) (â i)
  have hÂ : Â.eval (â i) =
      Â.eval (â i) / (cofactor â i).eval (â i) * (cofactor â i).eval (â i) :=
    (div_mul_cancel₀ _ hQ).symm
  rw [divDiff_cross, eval_cross_node]
  simp only [eval_mul] at hq ⊢
  linear_combination (-(w i) * ((cofactor a i).eval (a i) * (cofactor â i).eval (a i))) * hq -
    ((cofactor a i).eval (â i) * ((cofactor a i).eval (a i) * (cofactor â i).eval (a i))) * hÂ

/-- `prony:eq:weightdd`: for `â_i ≠ a_i` with `q(a_i), q(â_i) ≠ 0`, and `F = D/q`,
`ŵ_i - w_i = (F(â_i) - F(a_i))/(â_i - a_i)`. Here `ŵ_i = Â(â_i)/Q̂_i(â_i)`, which is the
source's `Â(â_i)/P̂'(â_i)` by `Surreal.Prony.eval_derivative_nodePoly`; see
`weightdd_derivative` for that form. -/
theorem weightdd (a â w : Fin n → K) (Â : K[X]) (i : Fin n) (hne : â i ≠ a i)
    (hqa : (cofactor a i * cofactor â i).eval (a i) ≠ 0)
    (hqb : (cofactor a i * cofactor â i).eval (â i) ≠ 0) :
    Â.eval (â i) / (cofactor â i).eval (â i) - w i =
      ((Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (â i) /
          (cofactor a i * cofactor â i).eval (â i) -
        (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) /
          (cofactor a i * cofactor â i).eval (a i)) / (â i - a i) := by
  have hQb : (cofactor â i).eval (â i) ≠ 0 := by
    rw [eval_mul] at hqb
    exact right_ne_zero_of_mul hqb
  have hDb : (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (â i) =
      (â i - a i) * (Â.eval (â i) / (cofactor â i).eval (â i)) *
        (cofactor a i * cofactor â i).eval (â i) := by
    have hc := div_mul_cancel₀ (Â.eval (â i)) hQb
    rw [eval_sub, eval_mul, eval_mul, (eval_nodePoly_eq_zero_iff â _).mpr ⟨i, rfl⟩, mul_zero,
      sub_zero, nodePoly_eq_mul_cofactor a i, eval_mul, eval_sub, eval_X, eval_C, eval_mul]
    linear_combination (-(â i - a i) * (cofactor a i).eval (â i)) * hc
  have hDa : (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) =
      w i * (â i - a i) * (cofactor a i * cofactor â i).eval (a i) := by
    rw [eval_cross_node, eval_mul]
  rw [hDb, hDa, mul_div_cancel_right₀ _ hqb, mul_div_cancel_right₀ _ hqa,
    eq_div_iff (sub_ne_zero.mpr hne)]
  ring

/-- `prony:eq:weightdd` at coincident arguments: if `â_i = a_i` and `q(a_i) ≠ 0`, then
`D(a_i) = 0` and `ŵ_i - w_i = D'(a_i)/q(a_i)`, which is `F'(a_i)` for `F = D/q`. Here
`ŵ_i = Â(â_i)/Q̂_i(â_i)`; see `weightdd_self_derivative` for the source's `Â(â_i)/P̂'(â_i)`. -/
theorem weightdd_self (a â w : Fin n → K) (Â : K[X]) (i : Fin n) (heq : â i = a i)
    (hqa : (cofactor a i * cofactor â i).eval (a i) ≠ 0) :
    (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) = 0 ∧
      Â.eval (â i) / (cofactor â i).eval (â i) - w i =
        (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).derivative.eval (a i) /
          (cofactor a i * cofactor â i).eval (a i) := by
  have hQb : (cofactor â i).eval (â i) ≠ 0 := by
    rw [heq]
    rw [eval_mul] at hqa
    exact right_ne_zero_of_mul hqa
  have hD0 : (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) = 0 := by
    rw [eval_cross_node, heq, sub_self, mul_zero, zero_mul]
  refine ⟨hD0, ?_⟩
  have hid := weight_identity a â w Â i hQb
  rw [hD0, zero_mul, sub_zero, heq, divDiff_self] at hid
  rw [heq, eq_div_iff hqa]
  refine mul_right_cancel₀ hqa ?_
  linear_combination hid

/-- `prony:eq:weightdd` with the source's `ŵ_i = Â(â_i)/P̂'(â_i)`: for `â_i ≠ a_i` with
`q(a_i), q(â_i) ≠ 0`, `ŵ_i - w_i = (F(â_i) - F(a_i))/(â_i - a_i)`. -/
theorem weightdd_derivative (a â w : Fin n → K) (Â : K[X]) (i : Fin n) (hne : â i ≠ a i)
    (hqa : (cofactor a i * cofactor â i).eval (a i) ≠ 0)
    (hqb : (cofactor a i * cofactor â i).eval (â i) ≠ 0) :
    Â.eval (â i) / (nodePoly â).derivative.eval (â i) - w i =
      ((Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (â i) /
          (cofactor a i * cofactor â i).eval (â i) -
        (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).eval (a i) /
          (cofactor a i * cofactor â i).eval (a i)) / (â i - a i) := by
  rw [eval_derivative_nodePoly]
  exact weightdd a â w Â i hne hqa hqb

/-- `prony:eq:weightdd` at coincident arguments with the source's `ŵ_i = Â(â_i)/P̂'(â_i)`: if
`â_i = a_i` and `q(a_i) ≠ 0`, then `ŵ_i - w_i = D'(a_i)/q(a_i)`. -/
theorem weightdd_self_derivative (a â w : Fin n → K) (Â : K[X]) (i : Fin n) (heq : â i = a i)
    (hqa : (cofactor a i * cofactor â i).eval (a i) ≠ 0) :
    Â.eval (â i) / (nodePoly â).derivative.eval (â i) - w i =
      (Â * nodePoly a - (∑ j, C (w j) * cofactor a j) * nodePoly â).derivative.eval (a i) /
        (cofactor a i * cofactor â i).eval (a i) := by
  rw [eval_derivative_nodePoly]
  exact (weightdd_self a â w Â i heq hqa).2

end WeightField

section Hahn

open scoped _root_.HahnSeries
open Surreal.PronyBound Surreal.PronyLocal Surreal.PronyRows

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

theorem orderTop_natCast_nonneg (m : ℕ) : 0 ≤ ((m : R⟦Γ⟧)).orderTop := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ]
    exact (le_min ih _root_.HahnSeries.orderTop_one.ge).trans
      _root_.HahnSeries.min_orderTop_le_orderTop_add

/-- Evaluation at an integral point keeps a lower bound on the coefficients. -/
theorem le_orderTop_eval_of_coeff {p : R⟦Γ⟧[X]} {κ : WithTop Γ}
    (hp : ∀ k, κ ≤ (p.coeff k).orderTop) {x : R⟦Γ⟧} (hx : 0 ≤ x.orderTop) :
    κ ≤ (p.eval x).orderTop :=
  (le_gaussVal_iff.mpr hp).trans (gaussVal_le_orderTop_eval p hx)

/-- The proof of `prony:lem:weight`: if every coefficient of `p` has valuation `≥ κ` and
`x, y` are integral, then `v([x, y] p) ≥ κ`. The coefficients of `taylor x p` are integral
combinations of those of `p`. -/
theorem le_orderTop_divDiff {p : R⟦Γ⟧[X]} {κ : WithTop Γ} (hp : ∀ k, κ ≤ (p.coeff k).orderTop)
    {x y : R⟦Γ⟧} (hx : 0 ≤ x.orderTop) (hy : 0 ≤ y.orderTop) :
    κ ≤ (divDiff p x y).orderTop := by
  refine le_orderTop_eval_of_coeff (fun k => ?_)
    ((le_min hy hx).trans _root_.HahnSeries.min_orderTop_le_orderTop_sub)
  rw [coeff_divX, taylor_coeff]
  refine le_orderTop_eval_of_coeff (fun j => ?_) hx
  rw [hasseDeriv_coeff, _root_.HahnSeries.orderTop_mul]
  calc κ = 0 + κ := (zero_add κ).symm
    _ ≤ _ := add_le_add (orderTop_natCast_nonneg _) (hp _)

/-- The coincident case of `le_orderTop_divDiff` (the source's "the same holds for `D'(a)`"):
if every coefficient of `p` has valuation `≥ κ` and `x` is integral, then `v(p'(x)) ≥ κ`. -/
theorem le_orderTop_eval_derivative {p : R⟦Γ⟧[X]} {κ : WithTop Γ}
    (hp : ∀ k, κ ≤ (p.coeff k).orderTop) {x : R⟦Γ⟧} (hx : 0 ≤ x.orderTop) :
    κ ≤ (p.derivative.eval x).orderTop := by
  rw [← divDiff_self]
  exact le_orderTop_divDiff hp hx hx

/-- The telescoping bound of the proof of `prony:lem:weight`: if `e_j ≤ δ`,
`v(x - c_j) ≥ e_j` and `v(y - c_j) ≥ e_j` for `j ∈ s`, then
`v([x, y] ∏_{j ∈ s} (X - c_j)) ≥ ∑_{j ∈ s} e_j - δ`. -/
theorem le_orderTop_divDiff_prod {ι : Type*} (s : Finset ι) (c : ι → R⟦Γ⟧) (e : ι → Γ)
    {δ : Γ} (he : ∀ j ∈ s, e j ≤ δ) {x y : R⟦Γ⟧}
    (hx : ∀ j ∈ s, (e j : WithTop Γ) ≤ (x - c j).orderTop)
    (hy : ∀ j ∈ s, (e j : WithTop Γ) ≤ (y - c j).orderTop) :
    (((∑ j ∈ s, e j) - δ : Γ) : WithTop Γ) ≤
      (divDiff (∏ j ∈ s, (X - C (c j))) x y).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [divDiff_one]
  | @insert k s hk ih =>
    have hks : k ∈ insert k s := mem_insert_self k s
    have ih' := ih (fun j hj => he j (mem_insert_of_mem hj))
      (fun j hj => hx j (mem_insert_of_mem hj)) (fun j hj => hy j (mem_insert_of_mem hj))
    have hprod : ((∑ j ∈ s, e j : Γ) : WithTop Γ) ≤
        ((∏ j ∈ s, (X - C (c j))).eval y).orderTop := by
      rw [eval_prod, Surreal.HahnSeries.orderTop_finset_prod, WithTop.coe_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      simpa only [eval_sub, eval_X, eval_C] using hy j (mem_insert_of_mem hj)
    rw [prod_insert hk, divDiff_mul, divDiff_X_sub_C, one_mul, sum_insert hk]
    refine (le_min ?_ ?_).trans _root_.HahnSeries.min_orderTop_le_orderTop_add
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) hprod
      have h := he k hks
      rw [sub_le_iff_le_add, add_comm (e k)]
      exact add_le_add le_rfl h
    · rw [eval_sub, eval_X, eval_C, _root_.HahnSeries.orderTop_mul]
      calc ((e k + (∑ j ∈ s, e j) - δ : Γ) : WithTop Γ) =
            (e k : WithTop Γ) + (((∑ j ∈ s, e j) - δ : Γ) : WithTop Γ) := by
            rw [← WithTop.coe_add, add_sub_assoc]
        _ ≤ _ := add_le_add (hx k hks) ih'

variable {n : ℕ} {a : Fin n → R⟦Γ⟧} {δ : Fin n → Γ}

omit [AddCommGroup Γ] [IsOrderedAddMonoid Γ] in
/-- Every node lies in its own strict ball `B_i = {x : v(x - a_i) > δ_i}`. -/
theorem mem_ball_self (i : Fin n) : (δ i : WithTop Γ) < (a i - a i).orderTop := by
  rw [sub_self, _root_.HahnSeries.orderTop_zero]
  exact WithTop.coe_lt_top _

/-- For points `c_j ∈ B_j` and `x ∈ B_i`, `v(Q^c_i(x)) = d_i`, where `Q^c_i = ∏_{j ≠ i} (X - c_j)`:
every factor keeps its separation valuation (`prony:eq:separation`). -/
theorem orderTop_eval_cofactor_of_mem_balls (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {c : Fin n → R⟦Γ⟧} (hc : ∀ j, (δ j : WithTop Γ) < (c j - a j).orderTop) {i : Fin n}
    {x : R⟦Γ⟧} (hx : (δ i : WithTop Γ) < (x - a i).orderTop) :
    ((cofactor c i).eval x).orderTop = sepSum a i := by
  rw [eval_cofactor, Surreal.HahnSeries.orderTop_finset_prod, sepSum, WithTop.coe_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≠ i := ne_of_mem_erase hj
  rw [(orderTop_leadingCoeff_sub_of_mem_balls hδ (Ne.symm hji) hx (hc j)).1,
    orderTop_sub_of_ne (injective_of_le_scale hδ) hji]

/-- For points `c_j ∈ B_j` and `x, y ∈ B_i`, `v([x, y] Q^c_i) ≥ d_i - δ_i`. -/
theorem le_orderTop_divDiff_cofactor (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {c : Fin n → R⟦Γ⟧} (hc : ∀ j, (δ j : WithTop Γ) < (c j - a j).orderTop) {i : Fin n}
    {x y : R⟦Γ⟧} (hx : (δ i : WithTop Γ) < (x - a i).orderTop)
    (hy : (δ i : WithTop Γ) < (y - a i).orderTop) :
    ((sepSum a i - δ i : Γ) : WithTop Γ) ≤ (divDiff (cofactor c i) x y).orderTop := by
  have ha := injective_of_le_scale hδ
  have hv : ∀ z, (δ i : WithTop Γ) < (z - a i).orderTop → ∀ j ∈ univ.erase i,
      (((a i - a j).order : Γ) : WithTop Γ) ≤ (z - c j).orderTop := by
    intro z hz j hj
    have hji : j ≠ i := ne_of_mem_erase hj
    rw [(orderTop_leadingCoeff_sub_of_mem_balls hδ (Ne.symm hji) hz (hc j)).1,
      orderTop_sub_of_ne ha hji]
  exact le_orderTop_divDiff_prod (univ.erase i) c (fun j => (a i - a j).order)
    (fun j hj => by
      have hji : j ≠ i := ne_of_mem_erase hj
      have h := hδ i j hji
      rwa [orderTop_sub_of_ne ha hji, WithTop.coe_le_coe] at h)
    (hv x hx) (hv y hy)

/-- `prony:eq:qval`: with `q = Q_i Q̂_i`, `v(q(a_i)) = v(q(â_i)) = 2 d_i`, whenever every
`â_j` lies in its ball `B_j`. -/
theorem orderTop_eval_qval (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {â : Fin n → R⟦Γ⟧} (hâ : ∀ j, (δ j : WithTop Γ) < (â j - a j).orderTop) (i : Fin n) :
    ((cofactor a i * cofactor â i).eval (a i)).orderTop = ((2 • sepSum a i : Γ) : WithTop Γ) ∧
      ((cofactor a i * cofactor â i).eval (â i)).orderTop =
        ((2 • sepSum a i : Γ) : WithTop Γ) := by
  have hself : ∀ j, (δ j : WithTop Γ) < (a j - a j).orderTop := mem_ball_self
  constructor
  · rw [eval_mul, _root_.HahnSeries.orderTop_mul,
      orderTop_eval_cofactor_of_mem_balls hδ hself (hself i),
      orderTop_eval_cofactor_of_mem_balls hδ hâ (hself i), two_nsmul, WithTop.coe_add]
  · rw [eval_mul, _root_.HahnSeries.orderTop_mul,
      orderTop_eval_cofactor_of_mem_balls hδ hself (hâ i),
      orderTop_eval_cofactor_of_mem_balls hδ hâ (hâ i), two_nsmul, WithTop.coe_add]

/-- The nonvanishing step of the proof of `prony:lem:weight`: with `q = Q_i Q̂_i`, `q(a_i) ≠ 0`
and `q(â_i) ≠ 0`, since both have the finite valuation `2 d_i` (`orderTop_eval_qval`). In
particular every factor of `q` is nonzero at `a_i` and at `â_i`. -/
theorem eval_qval_ne_zero (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {â : Fin n → R⟦Γ⟧} (hâ : ∀ j, (δ j : WithTop Γ) < (â j - a j).orderTop) (i : Fin n) :
    (cofactor a i * cofactor â i).eval (a i) ≠ 0 ∧
      (cofactor a i * cofactor â i).eval (â i) ≠ 0 := by
  obtain ⟨ha, hb⟩ := orderTop_eval_qval hδ hâ i
  refine ⟨fun h0 => ?_, fun h0 => ?_⟩
  · rw [h0, _root_.HahnSeries.orderTop_zero] at ha
    exact WithTop.top_ne_coe ha
  · rw [h0, _root_.HahnSeries.orderTop_zero] at hb
    exact WithTop.top_ne_coe hb

/-- The proof of `prony:lem:weight`: `v([a_i, â_i] q) ≥ 2 d_i - δ_i` for `q = Q_i Q̂_i`. -/
theorem le_orderTop_divDiff_qval (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    {â : Fin n → R⟦Γ⟧} (hâ : ∀ j, (δ j : WithTop Γ) < (â j - a j).orderTop) (i : Fin n) :
    ((2 • sepSum a i - δ i : Γ) : WithTop Γ) ≤
      (divDiff (cofactor a i * cofactor â i) (a i) (â i)).orderTop := by
  have hself : ∀ j, (δ j : WithTop Γ) < (a j - a j).orderTop := mem_ball_self
  have hsplit : ((2 • sepSum a i - δ i : Γ) : WithTop Γ) =
      ((sepSum a i - δ i : Γ) : WithTop Γ) + ((sepSum a i : Γ) : WithTop Γ) := by
    rw [← WithTop.coe_add]
    congr 1
    abel
  rw [divDiff_mul]
  refine (le_min ?_ ?_).trans _root_.HahnSeries.min_orderTop_le_orderTop_add
  · rw [_root_.HahnSeries.orderTop_mul, orderTop_eval_cofactor_of_mem_balls hδ hâ (hâ i), hsplit]
    exact add_le_add (le_orderTop_divDiff_cofactor hδ hself (hself i) (hâ i)) le_rfl
  · rw [_root_.HahnSeries.orderTop_mul, orderTop_eval_cofactor_of_mem_balls hδ hself (hself i),
      hsplit, add_comm]
    exact add_le_add le_rfl (le_orderTop_divDiff_cofactor hδ hâ (hself i) (hâ i))

/-- The final valuation step of `prony:lem:weight`: from
`(ŵ - w) q_a q_b = [a, b] D · q_a - D(a) [a, b] q` with `v(q_a) = v(q_b) = e`,
`v([a, b] D), v(D(a)) ≥ κ`, `v([a, b] q) ≥ e - δ` and `δ ≥ 0`, one gets
`v(ŵ - w) ≥ κ - e - δ`. -/
theorem le_orderTop_of_weight_identity {ŵ w qa qb dD Da dq : R⟦Γ⟧} {κ e δ : Γ}
    (hid : (ŵ - w) * (qa * qb) = dD * qa - Da * dq) (hqa : qa.orderTop = e)
    (hqb : qb.orderTop = e) (hdD : (κ : WithTop Γ) ≤ dD.orderTop)
    (hDa : (κ : WithTop Γ) ≤ Da.orderTop) (hdq : ((e - δ : Γ) : WithTop Γ) ≤ dq.orderTop)
    (hδ0 : 0 ≤ δ) : ((κ - e - δ : Γ) : WithTop Γ) ≤ (ŵ - w).orderTop := by
  have h1 : ((κ + e - δ : Γ) : WithTop Γ) ≤ (dD * qa).orderTop := by
    rw [_root_.HahnSeries.orderTop_mul, hqa]
    calc ((κ + e - δ : Γ) : WithTop Γ) ≤ ((κ + e : Γ) : WithTop Γ) :=
          WithTop.coe_le_coe.mpr (sub_le_self _ hδ0)
      _ = (κ : WithTop Γ) + e := WithTop.coe_add _ _
      _ ≤ _ := add_le_add hdD le_rfl
  have h2 : ((κ + e - δ : Γ) : WithTop Γ) ≤ (Da * dq).orderTop := by
    rw [_root_.HahnSeries.orderTop_mul]
    calc ((κ + e - δ : Γ) : WithTop Γ) = (κ : WithTop Γ) + ((e - δ : Γ) : WithTop Γ) := by
          rw [← WithTop.coe_add, add_sub_assoc]
      _ ≤ _ := add_le_add hDa hdq
  have h := (le_min h1 h2).trans _root_.HahnSeries.min_orderTop_le_orderTop_sub
  rw [← hid, _root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_mul, hqa, hqb,
    ← WithTop.coe_add] at h
  have h' := coe_sub_le_of_le_add h
  have heq : κ + e - δ - (e + e) = κ - e - δ := by abel
  rwa [heq] at h'

/-- `prony:lem:weight` (weight errors without a second conditioning loss). Let the nodes `a_i`
be integral, and let `δ_i ≥ 0` bound `v(a_i - a_j)` for every `j ≠ i`, which forces distinct
nodes. Let `P̂ = ∏ (X - â_j)` with `v(â_j - a_j) > δ_j`, annihilating the perturbed moments
(`L̂(P̂ X^r) = 0` for `r < n`), with Padé numerator `Â`, and let `v(m̂_k - m_k) ≥ κ` for
`k < 2n`, where `m_k = ∑ w_j a_j^k`. Then `ŵ_i = Â(â_i)/P̂'(â_i)` satisfies
`v(ŵ_i - w_i) ≥ κ - 2 d_i - δ_i`. -/
theorem weight_bound {a w â : Fin n → R⟦Γ⟧} {δ : Fin n → Γ} {mh : ℕ → R⟦Γ⟧} {κ : Γ}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hâ : ∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop)
    (hann : ∀ r < n, momentLinear mh (nodePoly â * X ^ r) = 0)
    (hε : ∀ k < 2 * n, (κ : WithTop Γ) ≤ (mh k - moment a w k).orderTop) (i : Fin n) :
    ((κ - 2 • sepSum a i - δ i : Γ) : WithTop Γ) ≤
      ((padeNumerator (2 * n) mh (nodePoly â)).eval (â i) /
        (nodePoly â).derivative.eval (â i) - w i).orderTop := by
  have hâ0 : ∀ j, 0 ≤ (â j).orderTop := by
    intro j
    have h1 : (0 : WithTop Γ) ≤ (â j - a j).orderTop :=
      (WithTop.coe_le_coe.mpr (hδ0 j)).trans (hâ j).le
    have h := (le_min h1 (ha0 j)).trans
      (_root_.HahnSeries.min_orderTop_le_orderTop_add (x := â j - a j) (y := a j))
    rwa [sub_add_cancel] at h
  have hD := le_orderTop_coeff_cross_nodePoly a w (natDegree_nodePoly â).le hann
    (coeff_orderTop_nonneg_prod ha0 univ) (coeff_orderTop_nonneg_prod hâ0 univ) hε
  obtain ⟨hqa, hqb⟩ := orderTop_eval_qval hδ hâ i
  have hQb : (cofactor â i).eval (â i) ≠ 0 := by
    intro h0
    have h := orderTop_eval_cofactor_of_mem_balls hδ hâ (hâ i)
    rw [h0, _root_.HahnSeries.orderTop_zero] at h
    exact WithTop.top_ne_coe h
  rw [eval_derivative_nodePoly]
  exact le_orderTop_of_weight_identity (weight_identity a â w _ i hQb) hqa hqb
    (le_orderTop_divDiff hD (ha0 i) (hâ0 i)) (le_orderTop_eval_of_coeff hD (ha0 i))
    (le_orderTop_divDiff_qval hδ hâ i) (hδ0 i)

/-- `prony:lem:weight` in the source's normalization: integral distinct nodes, and
`δ_i = max_{j ≠ i} v(a_i - a_j)` (`0` for `n = 1`), which is `Surreal.PronyRows.sepMax` for
integral distinct nodes (`sepMax_eq_sup'`, `sepMax_fin_one`). -/
theorem weight_bound_sepMax {a w â : Fin n → R⟦Γ⟧} {mh : ℕ → R⟦Γ⟧} {κ : Γ}
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (ha : Function.Injective a)
    (hâ : ∀ i, ((sepMax a i : Γ) : WithTop Γ) < (â i - a i).orderTop)
    (hann : ∀ r < n, momentLinear mh (nodePoly â * X ^ r) = 0)
    (hε : ∀ k < 2 * n, (κ : WithTop Γ) ≤ (mh k - moment a w k).orderTop) (i : Fin n) :
    ((κ - 2 • sepSum a i - sepMax a i : Γ) : WithTop Γ) ≤
      ((padeNumerator (2 * n) mh (nodePoly â)).eval (â i) /
        (nodePoly â).derivative.eval (â i) - w i).orderTop :=
  weight_bound ha0 (fun i j hji => by
      rw [orderTop_sub_of_ne ha hji]
      exact WithTop.coe_le_coe.mpr (order_sub_le_sepMax a hji))
    (sepMax_nonneg a) hâ hann hε i

/-- `prony:lem:weight` with `P̂` given as a monic polynomial of degree `n` whose roots are the
labelled points `â_i`: the balls are disjoint, so the `â_i` are distinct and `P̂ = ∏ (X - â_i)`. -/
theorem weight_bound_of_isRoot {a w â : Fin n → R⟦Γ⟧} {δ : Fin n → Γ} {mh : ℕ → R⟦Γ⟧} {κ : Γ}
    {F : R⟦Γ⟧[X]} (hF : F.Monic) (hFd : F.natDegree = n) (hroot : ∀ i, F.eval (â i) = 0)
    (ha0 : ∀ i, 0 ≤ (a i).orderTop) (hδ : ∀ i j, j ≠ i → (a i - a j).orderTop ≤ δ i)
    (hδ0 : ∀ i, 0 ≤ δ i) (hâ : ∀ i, (δ i : WithTop Γ) < (â i - a i).orderTop)
    (hann : ∀ r < n, momentLinear mh (F * X ^ r) = 0)
    (hε : ∀ k < 2 * n, (κ : WithTop Γ) ≤ (mh k - moment a w k).orderTop) (i : Fin n) :
    ((κ - 2 • sepSum a i - δ i : Γ) : WithTop Γ) ≤
      ((padeNumerator (2 * n) mh F).eval (â i) / F.derivative.eval (â i) - w i).orderTop := by
  have hinj : Function.Injective â := by
    intro j l hjl
    by_contra hne
    exact not_mem_ball_of_ne hδ hne (hâ j) (by rw [hjl]; exact hâ l)
  obtain rfl := eq_nodePoly_of_isRoot hF hFd hinj hroot
  exact weight_bound ha0 hδ hδ0 hâ hann hε i

end Hahn

section Affine

variable {K : Type*} [Field K]

/-- `prony:eq:affine`: the normalized moments
`m^norm_k = ρ^{-k} ∑_{l ≤ k} (k choose l) (-c)^{k-l} m_l` of the substitution
`x = (a - c)/ρ`. -/
def normMoment (c ρ : K) (m : ℕ → K) (k : ℕ) : K :=
  ρ⁻¹ ^ k * ∑ l ∈ range (k + 1), (k.choose l : K) * (-c) ^ (k - l) * m l

/-- The normalized moment is the original functional on `((X - c)/ρ)^k`. -/
theorem normMoment_eq_momentLinear (c ρ : K) (m : ℕ → K) (k : ℕ) :
    normMoment c ρ m k = momentLinear m ((C ρ⁻¹ * (X - C c)) ^ k) := by
  have hexp : (C ρ⁻¹ * (X - C c)) ^ k =
      ∑ l ∈ range (k + 1), C (ρ⁻¹ ^ k * ((k.choose l : K) * (-c) ^ (k - l))) * X ^ l := by
    rw [mul_pow, sub_eq_add_neg, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [map_mul, map_pow, map_natCast, map_neg]
    ring
  rw [hexp, map_sum, normMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [momentLinear_C_mul_X_pow]
  ring

/-- `prony:eq:affine`: the normalized moments of a configuration `(a, w)` are exactly the moments
of `(x, w)`, `x_i = (a_i - c)/ρ`. -/
theorem normMoment_moment {n : ℕ} (a w : Fin n → K) (c ρ : K) (k : ℕ) :
    normMoment c ρ (moment a w) k = moment (fun i => (a i - c) / ρ) w k := by
  rw [normMoment_eq_momentLinear, momentLinear_moment, momentFunctional, moment]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_pow, eval_mul, eval_C, eval_sub, eval_X, div_eq_inv_mul]

/-- The normalization is linear, so it is applied to the errors in the same way. -/
theorem normMoment_add (c ρ : K) (m ε : ℕ → K) :
    normMoment c ρ (m + ε) = normMoment c ρ m + normMoment c ρ ε := by
  funext k
  simp only [normMoment, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem normMoment_sub (c ρ : K) (m ε : ℕ → K) :
    normMoment c ρ (m - ε) = normMoment c ρ m - normMoment c ρ ε := by
  funext k
  simp only [normMoment, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- `prony:eq:affine`, error clause: the normalized perturbed moments differ from the moments of
the normalized configuration by the normalization of the moment errors. -/
theorem normMoment_sub_moment {n : ℕ} (a w : Fin n → K) (c ρ : K) (mh : ℕ → K) (k : ℕ) :
    normMoment c ρ mh k - moment (fun i => (a i - c) / ρ) w k =
      normMoment c ρ (mh - moment a w) k := by
  rw [normMoment_sub, Pi.sub_apply, normMoment_moment]

/-- The `k`-th normalized moment reads only the moments of index `≤ k`. -/
theorem normMoment_congr (c ρ : K) {m m' : ℕ → K} {k : ℕ} (h : ∀ l ≤ k, m l = m' l) :
    normMoment c ρ m k = normMoment c ρ m' k := by
  unfold normMoment
  congr 1
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [h l (Nat.lt_succ_iff.mp (mem_range.mp hl))]

/-- The normalized functional is `f ↦ L(f((X - c)/ρ))`. -/
theorem momentLinear_normMoment (c ρ : K) (m : ℕ → K) (f : K[X]) :
    momentLinear (normMoment c ρ m) f = momentLinear m (f.comp (C ρ⁻¹ * (X - C c))) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_comp, map_add, hp, hq]
  | monomial k b =>
    rw [← C_mul_X_pow_eq_monomial, momentLinear_C_mul_X_pow, mul_comp, C_comp, X_pow_comp,
      PronyBound.momentLinear_C_mul, normMoment_eq_momentLinear]

/-- The inverse normalization: `x ↦ c + ρ x` is `x ↦ (x - (-c/ρ))/ρ⁻¹`. -/
theorem normMoment_normMoment {ρ : K} (hρ : ρ ≠ 0) (c : K) (m : ℕ → K) :
    normMoment (-c / ρ) ρ⁻¹ (normMoment c ρ m) = m := by
  have hL : (C ρ⁻¹⁻¹ * (X - C (-c / ρ))).comp (C ρ⁻¹ * (X - C c)) = X := by
    have h1 : C ρ * C ρ⁻¹ = (1 : K[X]) := by rw [← C_mul, mul_inv_cancel₀ hρ, C_1]
    have h2 : C ρ * C (-c / ρ) = -C c := by rw [← C_mul, mul_div_cancel₀ _ hρ, C_neg]
    rw [inv_inv, mul_comp, sub_comp, C_comp, X_comp, C_comp]
    linear_combination (X - C c) * h1 - h2
  funext k
  rw [normMoment_eq_momentLinear, momentLinear_normMoment, pow_comp, hL]
  simpa using momentLinear_C_mul_X_pow m 1 k

/-- `prony:eq:affine`, realizations: `(x̂, ŵ)` realizes the normalized perturbed moments
`m̂^norm_k`, `k < N`, if and only if `(c + ρ x̂, ŵ)` realizes the original perturbed moments
`m̂_k`, `k < N`. -/
theorem moment_affine_iff {ρ : K} (hρ : ρ ≠ 0) (c : K) {n N : ℕ} (xh ŵ : Fin n → K)
    (mh : ℕ → K) :
    (∀ k < N, moment xh ŵ k = normMoment c ρ mh k) ↔
      ∀ k < N, moment (fun i => c + ρ * xh i) ŵ k = mh k := by
  have hx : ∀ i, (c + ρ * xh i - c) / ρ = xh i := fun i => by
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hρ]
  have hy : ∀ i, (xh i - -c / ρ) / ρ⁻¹ = c + ρ * xh i := fun i => by
    rw [div_inv_eq_mul, sub_mul, div_mul_cancel₀ _ hρ]
    ring
  constructor
  · intro h k hk
    calc moment (fun i => c + ρ * xh i) ŵ k = moment (fun i => (xh i - -c / ρ) / ρ⁻¹) ŵ k := by
          simp only [hy]
      _ = normMoment (-c / ρ) ρ⁻¹ (moment xh ŵ) k := (normMoment_moment _ _ _ _ _).symm
      _ = normMoment (-c / ρ) ρ⁻¹ (normMoment c ρ mh) k :=
          normMoment_congr _ _ fun l hl => h l (by omega)
      _ = mh k := by rw [normMoment_normMoment hρ]
  · intro h k hk
    calc moment xh ŵ k = moment (fun i => (c + ρ * xh i - c) / ρ) ŵ k := by simp only [hx]
      _ = normMoment c ρ (moment (fun i => c + ρ * xh i) ŵ) k :=
          (normMoment_moment _ _ _ _ _).symm
      _ = normMoment c ρ mh k := normMoment_congr _ _ fun l hl => h l (by omega)

/-- `prony:eq:affine` for `c = 0`: only `l = k` contributes, `m^norm_k = ρ^{-k} m_k`. -/
theorem normMoment_zero_left (ρ : K) (m : ℕ → K) (k : ℕ) :
    normMoment 0 ρ m k = ρ⁻¹ ^ k * m k := by
  rw [normMoment, Finset.sum_eq_single k]
  · rw [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul, one_mul]
  · intro l hl hlk
    have hlt : l < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hl)) hlk
    rw [neg_zero, zero_pow (Nat.sub_ne_zero_of_lt hlt), mul_zero, zero_mul]
  · intro hk
    exact absurd (mem_range.mpr (Nat.lt_succ_self k)) hk

end Affine

section AffineHahn

open scoped _root_.HahnSeries
open Surreal.PronyLocal Surreal.PronyRows

variable {Γ R : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field R]

theorem orderTop_inv_of_ne_zero {ρ : R⟦Γ⟧} (hρ : ρ ≠ 0) :
    ρ⁻¹.orderTop = ((-ρ.order : Γ) : WithTop Γ) :=
  orderTop_inv_eq (_root_.HahnSeries.order_eq_orderTop_of_ne_zero hρ).symm

open Classical in
/-- `prony:eq:affine`, error bound. If `v(ε_l) ≥ κ_l` for `l ≤ k` and `ρ ≠ 0`, then
`v(ε^norm_k) ≥ min (κ_l + (k - l) v(c) - k v(ρ))`, the minimum taken over the `l ≤ k` whose
coefficient `(k choose l) (-c)^{k-l}` is nonzero (zero coefficients omitted). -/
theorem le_orderTop_normMoment {c ρ : R⟦Γ⟧} (hρ : ρ ≠ 0) {ε : ℕ → R⟦Γ⟧}
    {κ : ℕ → WithTop Γ} {k : ℕ} (hε : ∀ l ≤ k, κ l ≤ (ε l).orderTop) :
    ((range (k + 1)).filter fun l => (k.choose l : R⟦Γ⟧) * (-c) ^ (k - l) ≠ 0).inf
        (fun l => κ l + (k - l) • c.orderTop + ((-(k • ρ.order) : Γ) : WithTop Γ)) ≤
      (normMoment c ρ ε k).orderTop := by
  rw [normMoment, Finset.mul_sum]
  refine Surreal.ChartIsometry.le_orderTop_finset_sum _ _ fun l hl => ?_
  by_cases h0 : (k.choose l : R⟦Γ⟧) * (-c) ^ (k - l) = 0
  · rw [h0, zero_mul, mul_zero, _root_.HahnSeries.orderTop_zero]
    exact le_top
  refine le_trans (Finset.inf_le (mem_filter.mpr ⟨hl, h0⟩)) ?_
  rw [_root_.HahnSeries.orderTop_mul, _root_.HahnSeries.orderTop_mul,
    _root_.HahnSeries.orderTop_mul, Surreal.HahnSeries.orderTop_pow,
    Surreal.HahnSeries.orderTop_pow, _root_.HahnSeries.orderTop_neg, orderTop_inv_of_ne_zero hρ,
    ← WithTop.coe_nsmul, smul_neg]
  calc κ l + (k - l) • c.orderTop + ((-(k • ρ.order) : Γ) : WithTop Γ) =
        ((-(k • ρ.order) : Γ) : WithTop Γ) + (0 + (k - l) • c.orderTop + κ l) := by
        abel
    _ ≤ _ := add_le_add le_rfl (add_le_add (add_le_add (orderTop_natCast_nonneg _) le_rfl)
        (hε l (Nat.lt_succ_iff.mp (mem_range.mp hl))))

open Classical in
/-- `prony:eq:affine`, error bound with the minimum over all `l ≤ k`, as displayed in the
source. For `c = 0` the terms `l < k` are `⊤`, since `(k - l) • ⊤ = ⊤`. -/
theorem le_orderTop_normMoment_of_inf {c ρ : R⟦Γ⟧} (hρ : ρ ≠ 0) {ε : ℕ → R⟦Γ⟧}
    {κ : ℕ → WithTop Γ} {k : ℕ} (hε : ∀ l ≤ k, κ l ≤ (ε l).orderTop) :
    (range (k + 1)).inf
        (fun l => κ l + (k - l) • c.orderTop + ((-(k • ρ.order) : Γ) : WithTop Γ)) ≤
      (normMoment c ρ ε k).orderTop :=
  le_trans (Finset.inf_mono (filter_subset _ _)) (le_orderTop_normMoment hρ hε)

/-- `prony:eq:affine` for `c = 0`: `v(ε^norm_k) ≥ κ_k - k v(ρ)`. -/
theorem le_orderTop_normMoment_zero {ρ : R⟦Γ⟧} (hρ : ρ ≠ 0) {ε : ℕ → R⟦Γ⟧} {κ : WithTop Γ}
    {k : ℕ} (hε : κ ≤ (ε k).orderTop) :
    κ + ((-(k • ρ.order) : Γ) : WithTop Γ) ≤ (normMoment 0 ρ ε k).orderTop := by
  rw [normMoment_zero_left, _root_.HahnSeries.orderTop_mul, Surreal.HahnSeries.orderTop_pow,
    orderTop_inv_of_ne_zero hρ, ← WithTop.coe_nsmul, smul_neg, add_comm]
  exact add_le_add le_rfl hε

/-- `prony:eq:affine`, translating back: the node `c + ρ x̂` differs from `c + ρ x` by
`ρ (x̂ - x)`, so every node-error valuation increases by `v(ρ)`. The weights are unchanged. -/
theorem orderTop_translate_back (c ρ x xh : R⟦Γ⟧) :
    ((c + ρ * xh) - (c + ρ * x)).orderTop = ρ.orderTop + (xh - x).orderTop := by
  rw [show c + ρ * xh - (c + ρ * x) = ρ * (xh - x) by ring, _root_.HahnSeries.orderTop_mul]

/-- `prony:eq:affine`, translating back against the original node `a = c + ρ x`,
`x = (a - c)/ρ`: `v((c + ρ x̂) - a) = v(ρ) + v(x̂ - x)`. -/
theorem orderTop_node_error {ρ : R⟦Γ⟧} (hρ : ρ ≠ 0) (c a xh : R⟦Γ⟧) :
    ((c + ρ * xh) - a).orderTop = ρ.orderTop + (xh - (a - c) / ρ).orderTop := by
  have ha : a = c + ρ * ((a - c) / ρ) := by rw [mul_div_cancel₀ _ hρ, add_sub_cancel]
  conv_lhs => rw [ha]
  exact orderTop_translate_back c ρ _ xh

/-- The normalization of `prony:eq:affine` always exists: for finitely many nodes there is a
nonzero `ρ` with every `a_i/ρ` integral. -/
theorem exists_integral_normalization {n : ℕ} (a : Fin n → R⟦Γ⟧) :
    ∃ ρ : R⟦Γ⟧, ρ ≠ 0 ∧ ∀ i, 0 ≤ (a i / ρ).orderTop := by
  set γ : Γ := univ.fold min 0 fun i => (a i).order
  have hρv : (_root_.HahnSeries.single γ (1 : R)).orderTop = γ :=
    _root_.HahnSeries.orderTop_single one_ne_zero
  have hρ : _root_.HahnSeries.single γ (1 : R) ≠ 0 := by
    intro h
    rw [h, _root_.HahnSeries.orderTop_zero] at hρv
    exact WithTop.top_ne_coe hρv
  refine ⟨_, hρ, fun i => orderTop_div_nonneg hρ ?_⟩
  rw [hρv]
  by_cases hai : a i = 0
  · rw [hai, _root_.HahnSeries.orderTop_zero]
    exact le_top
  rw [← _root_.HahnSeries.order_eq_orderTop_of_ne_zero hai, WithTop.coe_le_coe]
  exact (Finset.fold_min_le _).mpr (Or.inr ⟨i, mem_univ i, le_rfl⟩)

end AffineHahn

end

end Surreal.PronyWeight

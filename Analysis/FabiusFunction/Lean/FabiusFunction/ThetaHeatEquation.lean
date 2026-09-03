import FabiusFunction.JacobiImaginaryTransform
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Convex

/-!
# The heat equation for the Jacobi theta functions `ϑ₂`, `ϑ₃`, `ϑ₄`

This module formalizes the proposition `qg:prop-theta-heat` of the `q`-Pochhammer /
`q`-binomial monograph (chapter 10, *Theta modularity and sums of squares*):

> Each `ϑ_j`, for `j = 2, 3, 4`, satisfies `∂ϑ_j/∂τ = (1/(4π i)) ∂²ϑ_j/∂z²`.

The three theta functions are the corpus's own `Fabius.thetaTwo`, `Fabius.thetaThree`,
`Fabius.thetaFour` of `FabiusFunction.JacobiImaginaryTransform`, whose normalization
bridges (`hasSum_thetaTwo`, `hasSum_thetaThree`, `hasSum_thetaFour`) identify them with the
monograph's three series. So `thetaTwo_heat`, `thetaThree_heat`, `thetaFour_heat` are the
printed statement, for `j = 2, 3, 4` respectively.

## Reading of the printed statement

Two things the source leaves implicit are made explicit here, and both are the obvious
intended readings.

* **Domain.** The hypothesis `0 < τ.im` is carried everywhere. Off the upper half-plane the
  defining series diverges (Mathlib's `summable_jacobiTheta₂_term_iff`), so there is nothing
  to differentiate; the source never states a region.
* **Differentiation.** `∂/∂τ` and `∂/∂z` are the *complex* (holomorphic) derivatives, i.e.
  Mathlib's `deriv` in each variable separately. Wirtinger operators are not discussed, in
  the source or here.

## Main results

* `thetaThree_heat`, `thetaFour_heat`, `thetaTwo_heat`: `eq:qg-theta-heat` for `j = 3, 4, 2`,
  in the form `deriv (ϑ_j z) τ = deriv (deriv fun w => ϑ_j w τ) z / (4 π i)`.
* `thetaThree_heat_iteratedDeriv`, `thetaFour_heat_iteratedDeriv`,
  `thetaTwo_heat_iteratedDeriv`: the same with `∂²/∂z²` written as `iteratedDeriv 2`.
* `jacobiTheta₂_heat` and `jacobiTheta₂_heat_iteratedDeriv`: the `j = 3` case stated directly
  for Mathlib's `jacobiTheta₂` (`thetaThree` is definitionally `jacobiTheta₂`).
* `jacobiTheta₂_zz`, `jacobiTheta₂_tau`: the two termwise-differentiated series, which
  Mathlib does not have. Mathlib supplies only the first `z`-derivative `jacobiTheta₂'` and
  the joint Fréchet derivative `jacobiTheta₂_fderiv`.
* `jacobiTheta₂_zz_eq`: `jacobiTheta₂_zz z τ = 4 π i * jacobiTheta₂_tau z τ`, **with no
  hypothesis at all** (see below).
* `jacobiTheta₂_fderiv_apply`: an evaluation of Mathlib's opaque Fréchet derivative,
  `jacobiTheta₂_fderiv z τ (a, b) = a * jacobiTheta₂' z τ + b * jacobiTheta₂_tau z τ`.
* `hasDerivAt_jacobiTheta₂_snd`, `hasDerivAt_jacobiTheta₂'_fst`: the two genuinely analytic
  inputs — the `τ`-derivative and the second `z`-derivative, each identified with its
  termwise series.
* `iteratedDeriv_two_eq`: `iteratedDeriv 2 f = deriv (deriv f)`. This one is stated in full
  generality — for `f : 𝕜 → F` with `𝕜` a nontrivially normed field and `F` a normed
  `𝕜`-space — because nothing about `ℂ` enters it.

## What is proved here that is stronger than the printed statement

1. **`HasDerivAt` forms, not just `deriv` equations.** An equation `deriv f x = c` is
   vacuously true wherever `f` fails to be differentiable, so the literal transcription is
   weaker than the intended claim. Every `deriv` statement below is derived from an exported
   `HasDerivAt` statement, which asserts differentiability as well: `hasDerivAt_thetaTwo_snd`
   and `hasDerivAt_deriv_thetaTwo_fst` for `j = 2`, `hasDerivAt_thetaFour_snd` and
   `hasDerivAt_deriv_thetaFour_fst` for `j = 4`, and — since `thetaThree` *is*
   `jacobiTheta₂` — `hasDerivAt_jacobiTheta₂_snd` and `hasDerivAt_deriv_jacobiTheta₂_fst`
   for `j = 3`.
2. **The series-level heat relation is unconditional.** `jacobiTheta₂_zz_eq` needs neither
   `0 < τ.im` nor any summability: it is `tsum_congr` on the pure ring identity
   `(2π i n)² = 4π i · (π i n²)` — no use of `i² = -1` — followed by `tsum_mul_left`, which
   in a division semiring carries no summability hypothesis. The monograph has no analogue.
3. **All `z ∈ ℂ`.** The `ϑ₂` and `ϑ₄` laws are proved at every `z`, as printed.

## What is NOT covered

* **No generalization beyond `ℂ`.** The theta statements live on the complex upper half-plane
  and use `ℂ`-holomorphy; there is no free `CommRing` or normed-field version of them, and
  none should be looked for. (Same choice as `GaussianFourierTheta` and
  `JacobiImaginaryTransform`.) The one lemma with free generality, `iteratedDeriv_two_eq`, is
  stated at that generality.
* **No mixed or higher derivatives, no smoothness, no PDE theory.** Only the identity itself
  is proved: no `ContDiff` statement, no heat kernel, no uniqueness.
* **The route differs from the source's.** The monograph justifies termwise differentiation
  by an unproved remark ("normal convergence justifies both differentiations"); that remark
  is in fact the entire analytic content of the proposition, and it is what
  `hasDerivAt_jacobiTheta₂'_fst` supplies here, via
  `hasDerivAt_tsum_of_isPreconnected` on a horizontal strip `|Im w| < S` with the dominating
  bound `4π²|n|² exp(-π(Im τ · n² - 2S|n|))`. The `τ`-derivative comes from Mathlib's
  `hasFDerivAt_jacobiTheta₂`. The `ϑ₂` and `ϑ₄` cases are then obtained from `ϑ₃` by the
  chain and product rules rather than by rerunning the termwise argument with shift
  `α = 1/2`; the identity proved is the printed one either way. Nothing in the printed
  argument is wrong: its constant `1/(4π i)` is correct (`-4π²/(4π i) = π i`), and its
  omission is of detail only.
* **Nothing else in chapter 10** is touched.

## Naming

The second `z`-derivative series is called `jacobiTheta₂_zz`, *not* `jacobiTheta₂''`: the
latter root name is already taken by `Mathlib/NumberTheory/LSeries/HurwitzZetaOdd.lean` for a
different function.
-/

set_option autoImplicit false

open Complex Real

namespace Fabius

/-! ## The constant `4π i` -/

/-- The constant appearing in the heat equation is nonzero. -/
theorem four_pi_mul_I_ne_zero : (4 * (π : ℂ) * I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

/-- `‖2π i n‖ = 2π|n|`, the norm computation behind every bound in this file. -/
theorem norm_two_pi_mul_I_mul_intCast (n : ℤ) :
    ‖2 * (π : ℂ) * I * (n : ℂ)‖ = 2 * π * |(n : ℝ)| := by
  simp only [norm_mul, Complex.norm_two, norm_I, Complex.norm_of_nonneg pi_pos.le,
    norm_intCast, mul_one, Int.cast_abs]

/-! ## Termwise derivatives of the summands

`jacobiTheta₂_term n z τ = exp (2π i n z + π i n² τ)`, so `∂/∂z` multiplies the summand by
`2π i n` and `∂²/∂z²` by `(2π i n)²`. -/

/-- The `z`-derivative of the `n`-th summand of `jacobiTheta₂` is the `n`-th summand of
`jacobiTheta₂'`. -/
theorem hasDerivAt_jacobiTheta₂_term_fst (n : ℤ) (z τ : ℂ) :
    HasDerivAt (fun w : ℂ => jacobiTheta₂_term n w τ) (jacobiTheta₂'_term n z τ) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * (π : ℂ) * I * (n : ℂ) * w)
      (2 * (π : ℂ) * I * (n : ℂ)) z := by
    have h := (hasDerivAt_id' z).const_mul (2 * (π : ℂ) * I * (n : ℂ))
    rwa [mul_one] at h
  have h2 : HasDerivAt
      (fun w : ℂ => 2 * (π : ℂ) * I * (n : ℂ) * w + (π : ℂ) * I * (n : ℂ) ^ 2 * τ)
      (2 * (π : ℂ) * I * (n : ℂ)) z := h1.add_const ((π : ℂ) * I * (n : ℂ) ^ 2 * τ)
  have hfun : (fun w : ℂ => jacobiTheta₂_term n w τ)
      = fun w : ℂ => cexp (2 * (π : ℂ) * I * (n : ℂ) * w + (π : ℂ) * I * (n : ℂ) ^ 2 * τ) := rfl
  have hval : jacobiTheta₂'_term n z τ
      = cexp (2 * (π : ℂ) * I * (n : ℂ) * z + (π : ℂ) * I * (n : ℂ) ^ 2 * τ)
        * (2 * (π : ℂ) * I * (n : ℂ)) := by
    rw [jacobiTheta₂'_term, jacobiTheta₂_term]
    ring
  rw [hfun, hval]
  exact h2.cexp

/-- The `z`-derivative of the `n`-th summand of `jacobiTheta₂'` is `(2π i n)²` times the
`n`-th summand of `jacobiTheta₂`. -/
theorem hasDerivAt_jacobiTheta₂'_term_fst (n : ℤ) (z τ : ℂ) :
    HasDerivAt (fun w : ℂ => jacobiTheta₂'_term n w τ)
      ((2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ) z := by
  have h := (hasDerivAt_jacobiTheta₂_term_fst n z τ).const_mul (2 * (π : ℂ) * I * (n : ℂ))
  have hfun : (fun w : ℂ => jacobiTheta₂'_term n w τ)
      = fun w : ℂ => 2 * (π : ℂ) * I * (n : ℂ) * jacobiTheta₂_term n w τ := rfl
  have hval : (2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ
      = 2 * (π : ℂ) * I * (n : ℂ) * jacobiTheta₂'_term n z τ := by
    rw [jacobiTheta₂'_term]
    ring
  rw [hfun, hval]
  exact h

/-- Mathlib's summand-level Fréchet derivative, evaluated at an arbitrary tangent vector
`(a, b)`. -/
theorem jacobiTheta₂_term_fderiv_apply (n : ℤ) (z τ a b : ℂ) :
    jacobiTheta₂_term_fderiv n z τ (a, b)
      = (a * (2 * (π : ℂ) * I * (n : ℂ)) + b * ((π : ℂ) * I * (n : ℂ) ^ 2))
        * jacobiTheta₂_term n z τ := by
  simp only [jacobiTheta₂_term_fderiv, jacobiTheta₂_term, smul_add, smul_apply, add_apply,
    FunLike.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-! ## The two termwise-differentiated series

Mathlib has the first `z`-derivative `jacobiTheta₂'` but neither the second `z`-derivative nor
the `τ`-derivative as named series. Both are introduced here. -/

/-- The termwise second `z`-derivative of the Jacobi theta function,
`∑' n : ℤ, (2π i n)² exp (2π i n z + π i n² τ)`. For `0 < Im τ` this is the honest second
`z`-derivative (`hasDerivAt_jacobiTheta₂'_fst`); off the half-plane it is defined by the same
`tsum`, hence is `0` wherever the series fails to converge, exactly as for Mathlib's
`jacobiTheta₂`. -/
noncomputable def jacobiTheta₂_zz (z τ : ℂ) : ℂ :=
  ∑' n : ℤ, (2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ

/-- The termwise `τ`-derivative of the Jacobi theta function,
`∑' n : ℤ, π i n² exp (2π i n z + π i n² τ)`. For `0 < Im τ` this is the honest
`τ`-derivative (`hasDerivAt_jacobiTheta₂_snd`); off the half-plane it is defined by the same
`tsum`, hence is `0` wherever the series fails to converge. -/
noncomputable def jacobiTheta₂_tau (z τ : ℂ) : ℂ :=
  ∑' n : ℤ, (π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ

/-- The termwise second `z`-derivative series converges on the upper half-plane. -/
theorem summable_jacobiTheta₂_zz_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => (2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ := by
  refine ((summable_pow_mul_jacobiTheta₂_term_bound |z.im| hτ 2).mul_left
    (4 * π ^ 2)).of_norm_bounded fun n => ?_
  rw [norm_mul, ← mul_assoc, norm_pow, norm_two_pi_mul_I_mul_intCast]
  refine mul_le_mul (le_of_eq ?_) (norm_jacobiTheta₂_term_le hτ le_rfl le_rfl n)
    (norm_nonneg _) (by positivity)
  rw [Int.cast_abs]
  ring

/-- `HasSum` form of `summable_jacobiTheta₂_zz_term`. -/
theorem hasSum_jacobiTheta₂_zz_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => (2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ)
      (jacobiTheta₂_zz z τ) :=
  (summable_jacobiTheta₂_zz_term z hτ).hasSum

/-- The termwise `τ`-derivative series converges on the upper half-plane. It is the previous
one divided by the constant `4π i`. -/
theorem summable_jacobiTheta₂_tau_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ => (π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ := by
  refine ((summable_jacobiTheta₂_zz_term z hτ).div_const (4 * (π : ℂ) * I)).congr fun n => ?_
  rw [div_eq_iff four_pi_mul_I_ne_zero]
  ring

/-- `HasSum` form of `summable_jacobiTheta₂_tau_term`. -/
theorem hasSum_jacobiTheta₂_tau_term (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun n : ℤ => (π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ)
      (jacobiTheta₂_tau z τ) :=
  (summable_jacobiTheta₂_tau_term z hτ).hasSum

/-- **The heat relation at the level of the series.** `jacobiTheta₂_zz = 4π i · jacobiTheta₂_tau`
holds for *all* `z, τ : ℂ`: no half-plane hypothesis, no summability. It is the ring identity
`(2π i n)² = 4π i · (π i n²)` — which does not even use `i² = -1` — together with
`tsum_mul_left`, which in a division semiring needs no summability hypothesis. -/
theorem jacobiTheta₂_zz_eq (z τ : ℂ) :
    jacobiTheta₂_zz z τ = 4 * (π : ℂ) * I * jacobiTheta₂_tau z τ := by
  have h : ∀ n : ℤ, (2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ
      = 4 * (π : ℂ) * I * ((π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ) := fun n => by
    ring
  calc jacobiTheta₂_zz z τ
      = ∑' n : ℤ, 4 * (π : ℂ) * I * ((π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ) :=
        tsum_congr h
    _ = 4 * (π : ℂ) * I * ∑' n : ℤ, (π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ :=
        tsum_mul_left
    _ = 4 * (π : ℂ) * I * jacobiTheta₂_tau z τ := rfl

/-- The heat relation at the level of the series, solved for the `τ`-derivative. Also
unconditional. -/
theorem jacobiTheta₂_tau_eq (z τ : ℂ) :
    jacobiTheta₂_tau z τ = jacobiTheta₂_zz z τ / (4 * (π : ℂ) * I) := by
  rw [jacobiTheta₂_zz_eq, eq_div_iff four_pi_mul_I_ne_zero]
  ring

/-! ## Mathlib's Fréchet derivative, evaluated -/

/-- Mathlib's `jacobiTheta₂_fderiv` is opaque (a `tsum` of continuous linear maps). Here it is
evaluated at an arbitrary tangent vector: the `z`-component contributes `jacobiTheta₂'` and the
`τ`-component contributes `jacobiTheta₂_tau`. -/
theorem jacobiTheta₂_fderiv_apply (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) (a b : ℂ) :
    jacobiTheta₂_fderiv z τ (a, b) = a * jacobiTheta₂' z τ + b * jacobiTheta₂_tau z τ := by
  let ev : (ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
    { toFun := fun f => f (a, b)
      map_add' := by simp
      map_smul' := by simp }
  have h1 : HasSum (fun n : ℤ => (jacobiTheta₂_term_fderiv n z τ) (a, b))
      ((jacobiTheta₂_fderiv z τ) (a, b)) := by
    apply ev.hasSum (hasSum_jacobiTheta₂_term_fderiv z hτ)
  have hA : HasSum (fun n : ℤ => a * jacobiTheta₂'_term n z τ) (a * jacobiTheta₂' z τ) :=
    (hasSum_jacobiTheta₂'_term z hτ).mul_left a
  have hB : HasSum (fun n : ℤ => b * ((π : ℂ) * I * (n : ℂ) ^ 2 * jacobiTheta₂_term n z τ))
      (b * jacobiTheta₂_tau z τ) := (hasSum_jacobiTheta₂_tau_term z hτ).mul_left b
  have h2 : HasSum (fun n : ℤ => (jacobiTheta₂_term_fderiv n z τ) (a, b))
      (a * jacobiTheta₂' z τ + b * jacobiTheta₂_tau z τ) := by
    refine (hA.add hB).congr_fun fun n => ?_
    rw [jacobiTheta₂_term_fderiv_apply, jacobiTheta₂'_term]
    ring
  exact h1.unique h2

/-! ## The two partial derivatives of `jacobiTheta₂`

The `τ`-derivative is read off Mathlib's Fréchet derivative along the vertical direction; the
second `z`-derivative is the one genuinely analytic step, and is obtained by differentiating
the series for `jacobiTheta₂'` term by term on a horizontal strip. -/

/-- The `τ`-derivative of `jacobiTheta₂` is the termwise series `jacobiTheta₂_tau`. -/
theorem hasDerivAt_jacobiTheta₂_snd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (jacobiTheta₂ z) (jacobiTheta₂_tau z τ) τ := by
  have step : HasDerivAt (jacobiTheta₂ z) ((jacobiTheta₂_fderiv z τ) ((0 : ℂ), (1 : ℂ))) τ :=
    (((hasFDerivAt_jacobiTheta₂ z hτ).comp τ (hasFDerivAt_prodMk_right z τ)).hasDerivAt :)
  rwa [jacobiTheta₂_fderiv_apply z hτ 0 1, zero_mul, one_mul, zero_add] at step

/-- **The termwise differentiation step.** The `z`-derivative of `jacobiTheta₂'` is the
termwise series `jacobiTheta₂_zz`. This is the one place where the monograph's unproved
"normal convergence justifies both differentiations" is actually discharged: the summands are
dominated on the strip `|Im w| < S` by `4π²|n|² exp(-π(Im τ · n² - 2S|n|))`, which is summable
by Mathlib's `summable_pow_mul_jacobiTheta₂_term_bound`. -/
theorem hasDerivAt_jacobiTheta₂'_fst (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w : ℂ => jacobiTheta₂' w τ) (jacobiTheta₂_zz z τ) z := by
  obtain ⟨S, hS⟩ := exists_gt |im z|
  have hTopen : IsOpen {w : ℂ | |im w| < S} :=
    (_root_.continuous_abs.comp continuous_im).isOpen_preimage _ isOpen_Iio
  have hconv : Convex ℝ {w : ℂ | |im w| < S} := by
    have hEq : {w : ℂ | |im w| < S} = {c : ℂ | -S < c.im} ∩ {c : ℂ | c.im < S} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    rw [hEq]
    exact (convex_halfSpace_im_gt (-S)).inter (convex_halfSpace_im_lt S)
  have hmem : z ∈ {w : ℂ | |im w| < S} := hS
  have hu := (summable_pow_mul_jacobiTheta₂_term_bound S hτ 2).mul_left (4 * π ^ 2)
  have hg : ∀ (n : ℤ) (w : ℂ), w ∈ {v : ℂ | |im v| < S} →
      HasDerivAt (fun v : ℂ => jacobiTheta₂'_term n v τ)
        ((2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n w τ) w :=
    fun n w _ => hasDerivAt_jacobiTheta₂'_term_fst n w τ
  have hg0 : Summable fun n : ℤ => jacobiTheta₂'_term n z τ :=
    (summable_jacobiTheta₂'_term_iff z τ).mpr hτ
  have main : HasDerivAt (fun w : ℂ => ∑' n : ℤ, jacobiTheta₂'_term n w τ)
      (∑' n : ℤ, (2 * (π : ℂ) * I * (n : ℂ)) ^ 2 * jacobiTheta₂_term n z τ) z := by
    refine hasDerivAt_tsum_of_isPreconnected hu hTopen hconv.isPreconnected hg ?_ hmem hg0 hmem
    intro n w hw
    have hw' : |im w| ≤ S := le_of_lt hw
    rw [norm_mul, ← mul_assoc, norm_pow, norm_two_pi_mul_I_mul_intCast]
    refine mul_le_mul (le_of_eq ?_) (norm_jacobiTheta₂_term_le hτ hw' le_rfl n)
      (norm_nonneg _) (by positivity)
    rw [Int.cast_abs]
    ring
  -- `jacobiTheta₂'` and `jacobiTheta₂_zz` are the two `tsum`s of `main`, by definition.
  exact main

/-! ## The heat equation for `jacobiTheta₂` (equivalently `ϑ₃`) -/

/-- The first `z`-derivative of `jacobiTheta₂`, as a function. -/
theorem deriv_jacobiTheta₂_fst {τ : ℂ} (hτ : 0 < τ.im) :
    (deriv fun w : ℂ => jacobiTheta₂ w τ) = fun w : ℂ => jacobiTheta₂' w τ :=
  funext fun w => (hasDerivAt_jacobiTheta₂_fst w hτ).deriv

/-- The second `z`-derivative of `jacobiTheta₂`, in `HasDerivAt` form. -/
theorem hasDerivAt_deriv_jacobiTheta₂_fst (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (deriv fun w : ℂ => jacobiTheta₂ w τ) (jacobiTheta₂_zz z τ) z := by
  rw [deriv_jacobiTheta₂_fst hτ]
  exact hasDerivAt_jacobiTheta₂'_fst z hτ

/-- **The heat equation, `j = 3`, stated for Mathlib's `jacobiTheta₂`.** -/
theorem jacobiTheta₂_heat (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (jacobiTheta₂ z) τ
      = deriv (deriv fun w : ℂ => jacobiTheta₂ w τ) z / (4 * (π : ℂ) * I) := by
  rw [(hasDerivAt_jacobiTheta₂_snd z hτ).deriv, (hasDerivAt_deriv_jacobiTheta₂_fst z hτ).deriv,
    jacobiTheta₂_zz_eq, eq_div_iff four_pi_mul_I_ne_zero]
  ring

/-- `iteratedDeriv 2 f = deriv (deriv f)`, the reading of `∂²/∂z²` used below. Nothing about
`ℂ` enters, so this is stated for any map from a nontrivially normed field to a normed
space over it. -/
theorem iteratedDeriv_two_eq {𝕜 : Type*} [NontriviallyNormedField 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : 𝕜 → F) :
    iteratedDeriv 2 f = deriv (deriv f) := by
  have h1 : iteratedDeriv (1 + 1) f = deriv (iteratedDeriv 1 f) := iteratedDeriv_succ
  rw [iteratedDeriv_one] at h1
  exact h1

/-- The heat equation for `jacobiTheta₂` with `∂²/∂z²` written as `iteratedDeriv 2`. -/
theorem jacobiTheta₂_heat_iteratedDeriv (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (jacobiTheta₂ z) τ
      = iteratedDeriv 2 (fun w : ℂ => jacobiTheta₂ w τ) z / (4 * (π : ℂ) * I) := by
  rw [iteratedDeriv_two_eq (fun w : ℂ => jacobiTheta₂ w τ)]
  exact jacobiTheta₂_heat z hτ

/-- **`eq:qg-theta-heat` for `j = 3`**, in the monograph's own name for the function. -/
theorem thetaThree_heat (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (thetaThree z) τ
      = deriv (deriv fun w : ℂ => thetaThree w τ) z / (4 * (π : ℂ) * I) :=
  jacobiTheta₂_heat z hτ

/-- `eq:qg-theta-heat` for `j = 3`, with `∂²/∂z²` as `iteratedDeriv 2`. -/
theorem thetaThree_heat_iteratedDeriv (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (thetaThree z) τ
      = iteratedDeriv 2 (fun w : ℂ => thetaThree w τ) z / (4 * (π : ℂ) * I) := by
  rw [iteratedDeriv_two_eq (fun w : ℂ => thetaThree w τ)]
  exact thetaThree_heat z hτ

/-! ## Shifted arguments

`ϑ₄(z ∣ τ) = ϑ₃(z + 1/2 ∣ τ)` and `ϑ₂(z ∣ τ) = e^{π i τ/4 + π i z} ϑ₃(z + τ/2 ∣ τ)`, so both
need the `z`-derivatives of `w ↦ ϑ₃(w + c ∣ τ)` for a constant `c`. The chain factor is `1`. -/

/-- `z`-derivative of `w ↦ jacobiTheta₂ (w + c) τ`. -/
theorem hasDerivAt_jacobiTheta₂_fst_add_const (c z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w : ℂ => jacobiTheta₂ (w + c) τ) (jacobiTheta₂' (z + c) τ) z := by
  have hshift : HasDerivAt (fun w : ℂ => w + c) 1 z := (hasDerivAt_id' z).add_const c
  have h := (hasDerivAt_jacobiTheta₂_fst (z + c) hτ).comp z hshift
  rw [mul_one] at h
  exact h

/-- `z`-derivative of `w ↦ jacobiTheta₂' (w + c) τ`. -/
theorem hasDerivAt_jacobiTheta₂'_fst_add_const (c z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w : ℂ => jacobiTheta₂' (w + c) τ) (jacobiTheta₂_zz (z + c) τ) z := by
  have hshift : HasDerivAt (fun w : ℂ => w + c) 1 z := (hasDerivAt_id' z).add_const c
  have h := (hasDerivAt_jacobiTheta₂'_fst (z + c) hτ).comp z hshift
  rw [mul_one] at h
  exact h

/-! ## The heat equation for `ϑ₄` -/

/-- The `τ`-derivative of `ϑ₄`. -/
theorem hasDerivAt_thetaFour_snd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (thetaFour z) (jacobiTheta₂_tau (z + 1 / 2) τ) τ :=
  hasDerivAt_jacobiTheta₂_snd (z + 1 / 2) hτ

/-- The first `z`-derivative of `ϑ₄`. -/
theorem hasDerivAt_thetaFour_fst (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w : ℂ => thetaFour w τ) (jacobiTheta₂' (z + 1 / 2) τ) z :=
  hasDerivAt_jacobiTheta₂_fst_add_const (1 / 2) z hτ

/-- The first `z`-derivative of `ϑ₄`, as a function. -/
theorem deriv_thetaFour_fst {τ : ℂ} (hτ : 0 < τ.im) :
    (deriv fun w : ℂ => thetaFour w τ) = fun w : ℂ => jacobiTheta₂' (w + 1 / 2) τ :=
  funext fun w => (hasDerivAt_thetaFour_fst w hτ).deriv

/-- The second `z`-derivative of `ϑ₄`, in `HasDerivAt` form. -/
theorem hasDerivAt_deriv_thetaFour_fst (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (deriv fun w : ℂ => thetaFour w τ) (jacobiTheta₂_zz (z + 1 / 2) τ) z := by
  rw [deriv_thetaFour_fst hτ]
  exact hasDerivAt_jacobiTheta₂'_fst_add_const (1 / 2) z hτ

/-- **`eq:qg-theta-heat` for `j = 4`.** -/
theorem thetaFour_heat (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (thetaFour z) τ
      = deriv (deriv fun w : ℂ => thetaFour w τ) z / (4 * (π : ℂ) * I) := by
  rw [(hasDerivAt_thetaFour_snd z hτ).deriv, (hasDerivAt_deriv_thetaFour_fst z hτ).deriv,
    jacobiTheta₂_zz_eq, eq_div_iff four_pi_mul_I_ne_zero]
  ring

/-- `eq:qg-theta-heat` for `j = 4`, with `∂²/∂z²` as `iteratedDeriv 2`. -/
theorem thetaFour_heat_iteratedDeriv (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (thetaFour z) τ
      = iteratedDeriv 2 (fun w : ℂ => thetaFour w τ) z / (4 * (π : ℂ) * I) := by
  rw [iteratedDeriv_two_eq (fun w : ℂ => thetaFour w τ)]
  exact thetaFour_heat z hτ

/-! ## The heat equation for `ϑ₂`

`ϑ₂(z ∣ τ) = e^{π i τ/4 + π i z} ϑ₃(z + τ/2 ∣ τ)`, so both differentiations pick up
contributions from the exponential prefactor and, in the `τ` direction, from the `τ` inside the
first argument of `ϑ₃`. The gauge computation closes because `(π i)²/(4π i) = π i/4` and
`2π i/(4π i) = 1/2`, matching the coefficients `π i/4` and `1/2` produced by `∂/∂τ`. -/

/-- The `z`-derivative of the exponential prefactor of `ϑ₂`. -/
theorem hasDerivAt_thetaTwo_prefactor_fst (z τ : ℂ) :
    HasDerivAt (fun w : ℂ => cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * w))
      (cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) * ((π : ℂ) * I)) z := by
  have h1 : HasDerivAt (fun w : ℂ => (π : ℂ) * I * w) ((π : ℂ) * I) z := by
    have h := (hasDerivAt_id' z).const_mul ((π : ℂ) * I)
    rwa [mul_one] at h
  have h2 : HasDerivAt (fun w : ℂ => (π : ℂ) * I * τ / 4 + (π : ℂ) * I * w) ((π : ℂ) * I) z :=
    h1.const_add ((π : ℂ) * I * τ / 4)
  exact h2.cexp

/-- The `τ`-derivative of the exponential prefactor of `ϑ₂`. -/
theorem hasDerivAt_thetaTwo_prefactor_snd (z τ : ℂ) :
    HasDerivAt (fun s : ℂ => cexp ((π : ℂ) * I * s / 4 + (π : ℂ) * I * z))
      (cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) * ((π : ℂ) * I / 4)) τ := by
  have h1 : HasDerivAt (fun s : ℂ => (π : ℂ) * I * s) ((π : ℂ) * I) τ := by
    have h := (hasDerivAt_id' τ).const_mul ((π : ℂ) * I)
    rwa [mul_one] at h
  have h2 : HasDerivAt (fun s : ℂ => (π : ℂ) * I * s / 4) ((π : ℂ) * I / 4) τ := h1.div_const 4
  have h3 : HasDerivAt (fun s : ℂ => (π : ℂ) * I * s / 4 + (π : ℂ) * I * z) ((π : ℂ) * I / 4) τ :=
    h2.add_const ((π : ℂ) * I * z)
  exact h3.cexp

/-- The first `z`-derivative of `ϑ₂`. -/
theorem hasDerivAt_thetaTwo_fst (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (fun w : ℂ => thetaTwo w τ)
      (cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        ((π : ℂ) * I * jacobiTheta₂ (z + τ / 2) τ + jacobiTheta₂' (z + τ / 2) τ)) z := by
  have hE := hasDerivAt_thetaTwo_prefactor_fst z τ
  have hJ := hasDerivAt_jacobiTheta₂_fst_add_const (τ / 2) z hτ
  have hval : cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) * ((π : ℂ) * I) *
        jacobiTheta₂ (z + τ / 2) τ
      + cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) * jacobiTheta₂' (z + τ / 2) τ
      = cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        ((π : ℂ) * I * jacobiTheta₂ (z + τ / 2) τ + jacobiTheta₂' (z + τ / 2) τ) := by
    ring
  rw [← hval]
  exact hE.mul hJ

/-- The first `z`-derivative of `ϑ₂`, as a function. -/
theorem deriv_thetaTwo_fst {τ : ℂ} (hτ : 0 < τ.im) :
    (deriv fun w : ℂ => thetaTwo w τ) = fun w : ℂ =>
      cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * w) *
        ((π : ℂ) * I * jacobiTheta₂ (w + τ / 2) τ + jacobiTheta₂' (w + τ / 2) τ) :=
  funext fun w => (hasDerivAt_thetaTwo_fst w hτ).deriv

/-- The second `z`-derivative of `ϑ₂`, in `HasDerivAt` form. -/
theorem hasDerivAt_deriv_thetaTwo_fst (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (deriv fun w : ℂ => thetaTwo w τ)
      (cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        (((π : ℂ) * I) ^ 2 * jacobiTheta₂ (z + τ / 2) τ
          + 2 * ((π : ℂ) * I) * jacobiTheta₂' (z + τ / 2) τ
          + jacobiTheta₂_zz (z + τ / 2) τ)) z := by
  rw [deriv_thetaTwo_fst hτ]
  have hE := hasDerivAt_thetaTwo_prefactor_fst z τ
  have hJ := hasDerivAt_jacobiTheta₂_fst_add_const (τ / 2) z hτ
  have hJ' := hasDerivAt_jacobiTheta₂'_fst_add_const (τ / 2) z hτ
  have hG : HasDerivAt (fun w : ℂ => (π : ℂ) * I * jacobiTheta₂ (w + τ / 2) τ
        + jacobiTheta₂' (w + τ / 2) τ)
      ((π : ℂ) * I * jacobiTheta₂' (z + τ / 2) τ + jacobiTheta₂_zz (z + τ / 2) τ) z :=
    (hJ.const_mul ((π : ℂ) * I)).add hJ'
  have hval : cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) * ((π : ℂ) * I) *
        ((π : ℂ) * I * jacobiTheta₂ (z + τ / 2) τ + jacobiTheta₂' (z + τ / 2) τ)
      + cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        ((π : ℂ) * I * jacobiTheta₂' (z + τ / 2) τ + jacobiTheta₂_zz (z + τ / 2) τ)
      = cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        (((π : ℂ) * I) ^ 2 * jacobiTheta₂ (z + τ / 2) τ
          + 2 * ((π : ℂ) * I) * jacobiTheta₂' (z + τ / 2) τ
          + jacobiTheta₂_zz (z + τ / 2) τ) := by
    ring
  rw [← hval]
  exact hE.mul hG

/-- The `τ`-derivative of `ϑ₂`. Here `τ` occurs three times — in the prefactor, in the first
argument of `ϑ₃`, and as the modulus — so the chain rule runs along the curve
`s ↦ (z + s/2, s)`, whose tangent is `(1/2, 1)`. -/
theorem hasDerivAt_thetaTwo_snd (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (thetaTwo z)
      (cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        ((π : ℂ) * I / 4 * jacobiTheta₂ (z + τ / 2) τ
          + 1 / 2 * jacobiTheta₂' (z + τ / 2) τ
          + jacobiTheta₂_tau (z + τ / 2) τ)) τ := by
  have hE := hasDerivAt_thetaTwo_prefactor_snd z τ
  have hp : HasDerivAt (fun s : ℂ => ((z + s / 2 : ℂ), s)) ((1 / 2 : ℂ), (1 : ℂ)) τ :=
    (((hasDerivAt_id' τ).div_const 2).const_add z).prodMk (hasDerivAt_id' τ)
  have hB : HasDerivAt (fun s : ℂ => jacobiTheta₂ (z + s / 2) s)
      (1 / 2 * jacobiTheta₂' (z + τ / 2) τ + 1 * jacobiTheta₂_tau (z + τ / 2) τ) τ := by
    have h := (hasFDerivAt_jacobiTheta₂ (z + τ / 2) hτ).comp_hasDerivAt_of_eq τ hp rfl
    rw [jacobiTheta₂_fderiv_apply (z + τ / 2) hτ (1 / 2) 1] at h
    exact h
  have hval : cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) * ((π : ℂ) * I / 4) *
        jacobiTheta₂ (z + τ / 2) τ
      + cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        (1 / 2 * jacobiTheta₂' (z + τ / 2) τ + 1 * jacobiTheta₂_tau (z + τ / 2) τ)
      = cexp ((π : ℂ) * I * τ / 4 + (π : ℂ) * I * z) *
        ((π : ℂ) * I / 4 * jacobiTheta₂ (z + τ / 2) τ
          + 1 / 2 * jacobiTheta₂' (z + τ / 2) τ
          + jacobiTheta₂_tau (z + τ / 2) τ) := by
    ring
  rw [← hval]
  exact hE.mul hB

/-- **`eq:qg-theta-heat` for `j = 2`.** -/
theorem thetaTwo_heat (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (thetaTwo z) τ
      = deriv (deriv fun w : ℂ => thetaTwo w τ) z / (4 * (π : ℂ) * I) := by
  rw [(hasDerivAt_thetaTwo_snd z hτ).deriv, (hasDerivAt_deriv_thetaTwo_fst z hτ).deriv,
    jacobiTheta₂_zz_eq, eq_div_iff four_pi_mul_I_ne_zero]
  ring

/-- `eq:qg-theta-heat` for `j = 2`, with `∂²/∂z²` as `iteratedDeriv 2`. -/
theorem thetaTwo_heat_iteratedDeriv (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    deriv (thetaTwo z) τ
      = iteratedDeriv 2 (fun w : ℂ => thetaTwo w τ) z / (4 * (π : ℂ) * I) := by
  rw [iteratedDeriv_two_eq (fun w : ℂ => thetaTwo w τ)]
  exact thetaTwo_heat z hτ

end Fabius

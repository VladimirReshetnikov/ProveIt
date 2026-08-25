import FabiusFunction.LaplaceTransform
import FabiusFunction.QuantitativeSaddle
import FabiusFunction.FourierAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

set_option autoImplicit false

open scoped BigOperators FourierTransform Interval Topology
open Filter Set MeasureTheory

namespace Fabius

/-!
# The negative Laplace product on vertical lines

This file supplies the analytic input needed to use a Bromwich contour for the
Fabius function.  It proves the canonical complex dyadic product for the
negative generating function, then extracts finitely many factors to obtain
an explicit polynomial minor-arc bound of arbitrary order.

For `w = 1 + iθ` and `r > 0`, the main estimate is

`‖P(-rw)‖ / P(-r) ≤ C(r, N) ‖w‖ / ‖w‖ ^ N`,

where `C(r, N)` is a finite product of elementary hyperbolic-cotangent
factors.  Taking `N = 2` proves integrability of the natural vertical-line
kernel `P(-rw) / w` without any unproved analytic hypotheses.
-/

/-- The elementary factor `(1 - exp (-z)) / z` of the negative dyadic
product, packaged as the entire function `complexExpm1Div (-z)` so that the
removable singularity at `z = 0` is filled in with the value `1`. -/
noncomputable def negativeLaplaceComplexFactor (z : ℂ) : ℂ :=
  complexExpm1Div (-z)

/-- The real version `(1 - exp (-x)) / x` of `negativeLaplaceComplexFactor`,
written as a raw quotient.  It matches the complex factor only away from the
origin: at `x = 0` Lean's `0 / 0 = 0` convention gives `0` here, whereas
`negativeLaplaceComplexFactor 0 = 1`. -/
noncomputable def negativeLaplaceRealFactor (x : ℝ) : ℝ :=
  (1 - Real.exp (-x)) / x

/-- For `x ≠ 0` the complex factor at a real argument is the cast of the real
factor.  The hypothesis cannot be dropped: the two definitions disagree at the
origin.  This is the bridge used to descend the complex dyadic identities to
the real axis. -/
lemma negativeLaplaceComplexFactor_ofReal (x : ℝ) (hx : x ≠ 0) :
    negativeLaplaceComplexFactor (x : ℂ) =
      (negativeLaplaceRealFactor x : ℂ) := by
  rw [negativeLaplaceComplexFactor, complexExpm1Div_of_ne]
  · rw [negativeLaplaceRealFactor]
    push_cast
    ring
  · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hx)

/-- The real factor is positive on the positive axis.  This supplies the
nonzero denominators for all the ratio bounds `‖·‖ / real factor` below. -/
lemma negativeLaplaceRealFactor_pos (x : ℝ) (hx : 0 < x) :
    0 < negativeLaplaceRealFactor x := by
  rw [negativeLaplaceRealFactor]
  exact div_pos (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) hx

/-- The hyperbolic-cotangent factor `(1 + exp (-x)) / (1 - exp (-x))`, that
is `coth (x / 2)`.  It is the price of trading one factor of the negative
Laplace product for one power of `‖1 + iθ‖` of decay; the finite products of
these over dyadic scales form `negativeLaplaceMinorArcConstant`. -/
noncomputable def negativeLaplaceCothFactor (x : ℝ) : ℝ :=
  (1 + Real.exp (-x)) / (1 - Real.exp (-x))

/-- The `coth` factor is positive for `x > 0`.  Used here for
`negativeLaplaceMinorArcConstant_pos`, and again in `NegativeLaplaceMinorArc`
when the constant is bounded uniformly in `N`. -/
lemma negativeLaplaceCothFactor_pos (x : ℝ) (hx : 0 < x) :
    0 < negativeLaplaceCothFactor x := by
  rw [negativeLaplaceCothFactor]
  exact div_pos (by positivity)
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))

/-- The vertical-line direction `1 + iθ` never vanishes, so its norm is
positive.  Every division by `‖1 + iθ‖` in this file rests on this. -/
lemma norm_one_add_mul_I_pos (θ : ℝ) :
    0 < ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ := by
  rw [norm_pos_iff]
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

/-- `‖1 + iθ‖ ^ 2 = 1 + θ ^ 2`.  This is what turns the `N = 2` minor-arc
bound into the integrable Cauchy weight `(1 + θ ^ 2)⁻¹`. -/
lemma sq_norm_one_add_mul_I (θ : ℝ) :
    ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ ^ 2 = 1 + θ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

/-- On the ray `x (1 + iθ)` with `x > 0`, the factor has modulus at most
`(1 + exp (-x)) / (x ‖1 + iθ‖)`.  The numerator is the triangle-inequality
bound on `‖exp (-x (1 + iθ)) - 1‖`; the gain over the real axis is the single
power of `‖1 + iθ‖` in the denominator. -/
theorem norm_negativeLaplaceComplexFactor_vertical_le
    (x θ : ℝ) (hx : 0 < x) :
    ‖negativeLaplaceComplexFactor
        ((x : ℂ) * (1 + (θ : ℂ) * Complex.I))‖ ≤
      (1 + Real.exp (-x)) /
        (x * ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖) := by
  let w : ℂ := 1 + (θ : ℂ) * Complex.I
  have hw : w ≠ 0 := (norm_one_add_mul_I_pos θ).ne' |>.comp norm_eq_zero.mpr
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  rw [negativeLaplaceComplexFactor, complexExpm1Div_of_ne]
  · rw [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hx]
    have hnum : ‖Complex.exp (-((x : ℂ) * w)) - 1‖ ≤
        1 + Real.exp (-x) := by
      calc
        ‖Complex.exp (-((x : ℂ) * w)) - 1‖ ≤
            ‖Complex.exp (-((x : ℂ) * w))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + Real.exp (-x) := by
          rw [Complex.norm_exp]
          dsimp [w]
          norm_num
          ring
    dsimp [w] at hnum ⊢
    exact div_le_div_of_nonneg_right hnum (mul_nonneg hx.le (norm_nonneg _))
  · exact neg_ne_zero.mpr (mul_ne_zero hxC hw)

/-- Ratio form of the previous bound, for `x > 0`: the modulus of the factor
at `x (1 + iθ)`, divided by its real value `negativeLaplaceRealFactor x`, is at
most `negativeLaplaceCothFactor x / ‖1 + iθ‖`.  One extracted factor buys one
power of decay in `‖1 + iθ‖` at the cost of one `coth` factor. -/
theorem norm_negativeLaplaceComplexFactor_vertical_div_le
    (x θ : ℝ) (hx : 0 < x) :
    ‖negativeLaplaceComplexFactor
        ((x : ℂ) * (1 + (θ : ℂ) * Complex.I))‖ /
          negativeLaplaceRealFactor x ≤
      negativeLaplaceCothFactor x /
        ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ := by
  have hf := norm_negativeLaplaceComplexFactor_vertical_le x θ hx
  have hreal := negativeLaplaceRealFactor_pos x hx
  have hnorm := norm_one_add_mul_I_pos θ
  rw [div_le_iff₀ hreal]
  refine hf.trans_eq ?_
  rw [negativeLaplaceRealFactor, negativeLaplaceCothFactor]
  have he : 1 - Real.exp (-x) ≠ 0 :=
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).ne'
  field_simp [he, hnorm.ne']

/-- The integral representation `negativeLaplaceComplexFactor z =
∫ t in 0..1, exp (-z t)`, valid for every `z`, the case `z = 0` included.
It is the route to the small-argument estimate
`norm_negativeLaplaceComplexFactor_sub_one_le`. -/
theorem negativeLaplaceComplexFactor_eq_integral (z : ℂ) :
    negativeLaplaceComplexFactor z =
      ∫ t in (0 : ℝ)..1, Complex.exp (-z * t) := by
  by_cases hz : z = 0
  · subst z
    simp [negativeLaplaceComplexFactor]
  · rw [negativeLaplaceComplexFactor, complexExpm1Div_of_ne
      (neg_ne_zero.mpr hz)]
    rw [integral_exp_mul_complex (c := -z) (neg_ne_zero.mpr hz)]
    norm_num

/-- Small-argument estimate: for `‖z‖ ≤ 1`, the factor deviates from `1` by at
most `2 ‖z‖`.  The restriction to the closed unit disc is essential.  Applied
to the dyadic arguments `z / 2 ^ (n + 1)` it gives the geometric majorant that
makes the product converge. -/
theorem norm_negativeLaplaceComplexFactor_sub_one_le
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖negativeLaplaceComplexFactor z - 1‖ ≤ 2 * ‖z‖ := by
  rw [negativeLaplaceComplexFactor_eq_integral]
  simp only [neg_mul]
  have hexp : IntervalIntegrable (fun t : ℝ => Complex.exp (-z * t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-z * t)).intervalIntegrable 0 1
  have hone : IntervalIntegrable (fun _t : ℝ => (1 : ℂ)) volume 0 1 :=
    intervalIntegrable_const
  have hsub :
      (∫ t in (0 : ℝ)..1, Complex.exp (-z * t) - 1) =
        (∫ t in (0 : ℝ)..1, Complex.exp (-z * t)) -
          ∫ _t in (0 : ℝ)..1, (1 : ℂ) :=
    intervalIntegral.integral_sub hexp hone
  norm_num at hsub
  rw [← hsub]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (C := 2 * ‖z‖)
    (f := fun t : ℝ => Complex.exp (-(z * t)) - 1) (by
      intro t ht
      have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact ⟨ht.1.le, ht.2⟩
      have harg : ‖-(z * (t : ℂ))‖ ≤ 1 := by
        rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ht01.1]
        calc
          ‖z‖ * t ≤ ‖z‖ * 1 :=
            mul_le_mul_of_nonneg_left ht01.2 (norm_nonneg z)
          _ ≤ 1 := by simpa using hz
      calc
        ‖Complex.exp (-(z * (t : ℂ))) - 1‖ ≤
            2 * ‖-(z * (t : ℂ))‖ := Complex.norm_exp_sub_one_le harg
        _ ≤ 2 * ‖z‖ := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg ht01.1]
          calc
            2 * (‖z‖ * t) ≤ 2 * (‖z‖ * 1) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left ht01.2 (norm_nonneg z)) (by norm_num)
            _ = 2 * ‖z‖ := by ring)
  simpa using hbound

/-- The `n`-th factor of the canonical dyadic product for
`complexGeneratingFunction F (-z)`: the elementary factor at the halved
argument `z / 2 ^ (n + 1)`.  Indexing starts at `n = 0` with the scale `z / 2`,
hence the exponent `n + 1` rather than `n`. -/
noncomputable def negativeLaplaceDyadicFactor (z : ℂ) (n : ℕ) : ℂ :=
  negativeLaplaceComplexFactor (z / (2 : ℂ) ^ (n + 1))

/-- The real counterpart of `negativeLaplaceDyadicFactor`, at the scale
`r / 2 ^ (n + 1)`.  Finite products of these are the normalizing denominators
in the minor-arc ratio bounds. -/
noncomputable def negativeLaplaceRealDyadicFactor (r : ℝ) (n : ℕ) : ℝ :=
  negativeLaplaceRealFactor (r / (2 : ℝ) ^ (n + 1))

/-- The minor-arc constant `C(r, N)`: the product of the `coth` factors at the
first `N` dyadic scales `r / 2 ^ (n + 1)`, `n < N`.  It is the constant paid
for extracting `N` factors.  The product is over `Finset.range N`, so `N = 0`
gives the empty product `1`. -/
noncomputable def negativeLaplaceMinorArcConstant (r : ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.range N,
    negativeLaplaceCothFactor (r / (2 : ℝ) ^ (n + 1))

/-- Positivity of the real dyadic factors for `r > 0`, so their finite
products can serve as denominators. -/
lemma negativeLaplaceRealDyadicFactor_pos (r : ℝ) (hr : 0 < r) (n : ℕ) :
    0 < negativeLaplaceRealDyadicFactor r n := by
  apply negativeLaplaceRealFactor_pos
  positivity

/-- For `r > 0` the complex dyadic factor at the real point `r` is the cast of
the real dyadic factor.  This is the step that turns the complex finite
refinement into `generatingFunction_neg_finite_refinement`. -/
lemma negativeLaplaceDyadicFactor_ofReal
    (r : ℝ) (hr : 0 < r) (n : ℕ) :
    negativeLaplaceDyadicFactor (r : ℂ) n =
      (negativeLaplaceRealDyadicFactor r n : ℂ) := by
  rw [negativeLaplaceDyadicFactor, negativeLaplaceRealDyadicFactor]
  have hscale :
      (r : ℂ) / (2 : ℂ) ^ (n + 1) =
        ((r / (2 : ℝ) ^ (n + 1) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hscale, negativeLaplaceComplexFactor_ofReal]
  positivity

/-- Rewrites the `n`-th dyadic factor at `r (1 + iθ)` as the plain complex
factor at `(r / 2 ^ (n + 1)) (1 + iθ)`, moving the dyadic scaling onto the real
parameter.  No hypothesis on `r` or `θ` is needed. -/
lemma negativeLaplaceDyadicFactor_vertical
    (r θ : ℝ) (n : ℕ) :
    negativeLaplaceDyadicFactor
        ((r : ℂ) * (1 + (θ : ℂ) * Complex.I)) n =
      negativeLaplaceComplexFactor
        (((r / (2 : ℝ) ^ (n + 1) : ℝ) : ℂ) *
          (1 + (θ : ℂ) * Complex.I)) := by
  unfold negativeLaplaceDyadicFactor
  congr 1
  push_cast
  field_simp

/-- The per-factor ratio bound transported to the `n`-th dyadic scale, for
`r > 0`: one power of `‖1 + iθ‖` of decay against the `coth` factor at
`r / 2 ^ (n + 1)`. -/
theorem norm_negativeLaplaceDyadicFactor_vertical_div_le
    (r θ : ℝ) (hr : 0 < r) (n : ℕ) :
    ‖negativeLaplaceDyadicFactor
        ((r : ℂ) * (1 + (θ : ℂ) * Complex.I)) n‖ /
          negativeLaplaceRealDyadicFactor r n ≤
      negativeLaplaceCothFactor (r / (2 : ℝ) ^ (n + 1)) /
        ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ := by
  rw [negativeLaplaceDyadicFactor_vertical,
    negativeLaplaceRealDyadicFactor]
  exact norm_negativeLaplaceComplexFactor_vertical_div_le _ θ (by positivity)

/-- The minor-arc constant is positive for `r > 0`, being a finite product of
positive `coth` factors.  Also used by the saddle-point files downstream. -/
lemma negativeLaplaceMinorArcConstant_pos
    (r : ℝ) (hr : 0 < r) (N : ℕ) :
    0 < negativeLaplaceMinorArcConstant r N := by
  unfold negativeLaplaceMinorArcConstant
  apply Finset.prod_pos
  intro n _hn
  exact negativeLaplaceCothFactor_pos _ (by positivity)

/-- Multiplying the per-factor bounds over `n < N`, for `r > 0`: the modulus of
the first `N` dyadic factors at `r (1 + iθ)`, divided by the corresponding real
product, is at most `C(r, N) / ‖1 + iθ‖ ^ N`.  This is where the arbitrary
prescribed polynomial order of the minor-arc bound comes from. -/
theorem norm_negativeLaplaceDyadicFactor_prod_vertical_div_le
    (r θ : ℝ) (hr : 0 < r) (N : ℕ) :
    ‖∏ n ∈ Finset.range N,
        negativeLaplaceDyadicFactor
          ((r : ℂ) * (1 + (θ : ℂ) * Complex.I)) n‖ /
        (∏ n ∈ Finset.range N,
          negativeLaplaceRealDyadicFactor r n) ≤
      negativeLaplaceMinorArcConstant r N /
        ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ ^ N := by
  rw [norm_prod]
  rw [← Finset.prod_div_distrib]
  calc
    (∏ n ∈ Finset.range N,
        ‖negativeLaplaceDyadicFactor
          ((r : ℂ) * (1 + (θ : ℂ) * Complex.I)) n‖ /
            negativeLaplaceRealDyadicFactor r n) ≤
        ∏ n ∈ Finset.range N,
          negativeLaplaceCothFactor (r / (2 : ℝ) ^ (n + 1)) /
            ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ := by
      exact Finset.prod_le_prod
        (fun n _hn => div_nonneg (norm_nonneg _)
          (negativeLaplaceRealDyadicFactor_pos r hr n).le)
        (fun n _hn =>
          norm_negativeLaplaceDyadicFactor_vertical_div_le r θ hr n)
    _ = negativeLaplaceMinorArcConstant r N /
          ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ ^ N := by
      rw [Finset.prod_div_distrib]
      simp [negativeLaplaceMinorArcConstant]

/-- For every `z` the deviations `negativeLaplaceDyadicFactor z n - 1` are
summable, since eventually `‖z / 2 ^ (n + 1)‖ ≤ 1` and the small-argument
estimate then majorizes them by a geometric series.  This is the hypothesis of
`Complex.multipliable_one_add_of_summable`. -/
lemma summable_negativeLaplaceDyadicFactor_sub_one (z : ℂ) :
    Summable (fun n : ℕ => negativeLaplaceDyadicFactor z n - 1) := by
  have harg : Tendsto
      (fun n : ℕ => ‖z / (2 : ℂ) ^ (n + 1)‖) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => ((2 : ℂ)⁻¹) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    have hm := hp.const_mul (z / 2)
    convert hm.norm using 1
    · funext n
      rw [pow_succ, div_eq_mul_inv, inv_pow]
      simp only [norm_mul, norm_div]
      norm_num
      ring
    · simp
  have hsmall : ∀ᶠ n : ℕ in atTop, ‖z / (2 : ℂ) ^ (n + 1)‖ ≤ 1 :=
    (tendsto_order.1 harg).2 1 zero_lt_one |>.mono fun _ h => h.le
  have hmajor : Summable (fun n : ℕ => ‖z‖ / 2 ^ n) := by
    convert summable_geometric_two' (2 * ‖z‖) using 1
    funext n
    ring
  apply hmajor.of_norm_bounded_eventually
  have hsmallCofinite :
      ∀ᶠ n : ℕ in cofinite, ‖z / (2 : ℂ) ^ (n + 1)‖ ≤ 1 :=
    Nat.cofinite_eq_atTop ▸ hsmall
  filter_upwards [hsmallCofinite] with n hn
  dsimp [negativeLaplaceDyadicFactor]
  refine (norm_negativeLaplaceComplexFactor_sub_one_le _ hn).trans_eq ?_
  rw [norm_div, norm_pow]
  norm_num
  rw [pow_succ]
  field_simp

/-- The dyadic factors are multipliable for every `z`, so the infinite product
`∏' n, negativeLaplaceDyadicFactor z n` converges.  This is what lets the
finite refinement be passed to the limit in
`complexGeneratingFunction_neg_eq_tprod`. -/
lemma negativeLaplaceDyadicFactor_multipliable (z : ℂ) :
    Multipliable (negativeLaplaceDyadicFactor z) := by
  have h := Complex.multipliable_one_add_of_summable
    (summable_negativeLaplaceDyadicFactor_sub_one z)
  convert h using 1
  funext n
  ring

/-- Iterating the functional equation `proposition_two_formula` `N` times:
`complexGeneratingFunction F (-z)` equals the product of the first `N` dyadic
factors of `z` times the value at the remaining scale `-(z / 2 ^ N)`.  An exact
identity for every `N`, holding for all `z`. -/
theorem complexGeneratingFunction_neg_finite_refinement
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (N : ℕ) :
    complexGeneratingFunction F (-z) =
      (∏ n ∈ Finset.range N, negativeLaplaceDyadicFactor z n) *
        complexGeneratingFunction F (-(z / (2 : ℂ) ^ N)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [ih, Finset.prod_range_succ]
      have hrefine := proposition_two_formula F hF
        (-(z / (2 : ℂ) ^ (N + 1)))
      have harg : 2 * (-(z / (2 : ℂ) ^ (N + 1))) =
          -(z / (2 : ℂ) ^ N) := by
        rw [pow_succ]
        ring
      rw [harg] at hrefine
      rw [hrefine]
      have hfactor :
          complexExpm1Div (-(z / (2 : ℂ) ^ (N + 1))) =
            negativeLaplaceDyadicFactor z N := by
        rfl
      have htail :
          -(z / (2 : ℂ) ^ (N + 1)) =
            -(z / (2 : ℂ) ^ (N + 1)) := rfl
      rw [hfactor]
      ring

/-- Deprecated compatibility alias for `complexGeneratingFunction_ofReal`. -/
@[deprecated complexGeneratingFunction_ofReal (since := "2026-08-24")]
alias complexGeneratingFunction_ofReal_vertical :=
  complexGeneratingFunction_ofReal

/-- The real form of the finite refinement on the negative axis: for `r > 0`,
`generatingFunction F (-r)` is the product of the first `N` real dyadic factors
times `generatingFunction F (-(r / 2 ^ N))`.  The hypothesis `0 < r` is what
lets the complex and real factors be identified. -/
theorem generatingFunction_neg_finite_refinement
    (F : BoundedFabius) (hF : IsFabius F)
    (r : ℝ) (hr : 0 < r) (N : ℕ) :
    generatingFunction F (-r) =
      (∏ n ∈ Finset.range N, negativeLaplaceRealDyadicFactor r n) *
        generatingFunction F (-(r / (2 : ℝ) ^ N)) := by
  have hc := complexGeneratingFunction_neg_finite_refinement F hF (r : ℂ) N
  have hleft : -(r : ℂ) = ((-r : ℝ) : ℂ) := by
    push_cast
    rfl
  have htail :
      -((r : ℂ) / (2 : ℂ) ^ N) =
        ((-(r / (2 : ℝ) ^ N) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hleft, complexGeneratingFunction_ofReal,
    htail, complexGeneratingFunction_ofReal] at hc
  simp_rw [negativeLaplaceDyadicFactor_ofReal r hr] at hc
  exact_mod_cast hc

/-- The entire negative generating function is its canonical dyadic product. -/
theorem complexGeneratingFunction_neg_eq_tprod
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F (-z) =
      ∏' n : ℕ, negativeLaplaceDyadicFactor z n := by
  have harg : Tendsto (fun N : ℕ => -(z / (2 : ℂ) ^ N)) atTop (𝓝 0) := by
    have hp : Tendsto (fun N : ℕ => ((2 : ℂ)⁻¹) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    have hm := hp.const_mul z
    convert hm.neg using 1
    · funext N
      rw [div_eq_mul_inv, inv_pow]
    · simp
  have hcgContinuousAt : ContinuousAt (complexGeneratingFunction F) 0 := by
    have heq : complexGeneratingFunction F = fun w : ℂ =>
        Complex.exp (w / 2) *
          rvachevFourier F (Complex.I * w / (4 * Real.pi)) := by
      funext w
      exact complexGeneratingFunction_eq_fourier_analytic F hF w
    rw [heq]
    have hrv : Continuous (rvachevFourier F) :=
      (rvachevFourier_differentiable_analytic F hF).continuous
    apply Continuous.continuousAt
    fun_prop
  have htail : Tendsto
      (fun N : ℕ => complexGeneratingFunction F (-(z / (2 : ℂ) ^ N)))
      atTop (𝓝 1) := by
    have h := hcgContinuousAt.tendsto.comp harg
    have hzero : complexGeneratingFunction F 0 = 1 := by
      simp [complexGeneratingFunction]
    rw [hzero] at h
    simpa only [Function.comp_def] using h
  have hmult := negativeLaplaceDyadicFactor_multipliable z
  have hprod := hmult.tendsto_prod_tprod_nat
  have hboth := hprod.mul htail
  have hconst : Tendsto (fun _N : ℕ => complexGeneratingFunction F (-z))
      atTop (𝓝 (complexGeneratingFunction F (-z))) := tendsto_const_nhds
  have heq : (fun _N : ℕ => complexGeneratingFunction F (-z)) =
      fun N : ℕ =>
        (∏ n ∈ Finset.range N, negativeLaplaceDyadicFactor z n) *
          complexGeneratingFunction F (-(z / (2 : ℂ) ^ N)) := by
    funext N
    exact complexGeneratingFunction_neg_finite_refinement F hF z N
  rw [heq] at hconst
  simpa only [mul_one] using tendsto_nhds_unique hconst hboth

/-- The modulus of the complex Laplace transform on a vertical line is
bounded by its positive-real-axis value. -/
theorem norm_complexGeneratingFunction_neg_div_le_real
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) (hz : 0 < z.re) :
    ‖complexGeneratingFunction F (-z) / z‖ ≤
      generatingFunction F (-z.re) / z.re := by
  let g : ℝ → ℝ := fun t => fabiusReal F t * Real.exp (-z.re * t)
  have hg : IntegrableOn g (Ioi 0) := by
    simpa [g] using integrableOn_fabiusReal_mul_exp_neg F hF hz
  have hpoint : ∀ t : ℝ,
      ‖(fabiusReal F t : ℂ) * Complex.exp (-z * t)‖ = g t := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fabiusReal_nonneg F t), Complex.norm_exp]
    dsimp [g]
    congr 2
    norm_num
  have hnorm :
      ‖∫ t : ℝ in Ioi 0,
          (fabiusReal F t : ℂ) * Complex.exp (-z * t)‖ ≤
        ∫ t : ℝ in Ioi 0, g t := by
    exact norm_integral_le_of_norm_le hg
      (Filter.Eventually.of_forall fun t => (hpoint t).le)
  rw [← complexGeneratingFunction_neg_div_eq_laplace F hF hz] at hnorm
  have hrealEq : generatingFunction F (-z.re) / z.re =
      ∫ t : ℝ in Ioi 0, g t := by
    simpa [g] using generatingFunction_neg_div_eq_laplace F hF hz
  rwa [hrealEq]

/-- Tail factor bound used after finite dyadic refinement. -/
theorem norm_complexGeneratingFunction_neg_le_real_mul_verticalNorm
    (F : BoundedFabius) (hF : IsFabius F) (r θ : ℝ) (hr : 0 < r) :
    ‖complexGeneratingFunction F
        (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))‖ ≤
      generatingFunction F (-r) *
        ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ := by
  let w : ℂ := 1 + (θ : ℂ) * Complex.I
  let z : ℂ := (r : ℂ) * w
  have hzre : z.re = r := by
    dsimp [z, w]
    norm_num
  have hz : 0 < z.re := by rw [hzre]; exact hr
  have h := norm_complexGeneratingFunction_neg_div_le_real F hF z hz
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, hzre] at h
  rw [div_le_iff₀ (mul_pos hr (norm_one_add_mul_I_pos θ))] at h
  dsimp [z, w] at h ⊢
  calc
    ‖complexGeneratingFunction F
        (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))‖ ≤
        generatingFunction F (-r) / r *
          (r * ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖) := h
    _ = generatingFunction F (-r) *
        ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ := by
      field_simp [hr.ne']

/-- For `r > 0` the value `generatingFunction F (-r)` is positive, being the
exponential of the negative Laplace logarithm.  It is the denominator of the
normalized bound `norm_complexGeneratingFunction_neg_vertical_div_le`, and is
reused in `FabiusBromwichInput` and `FabiusSaddleTail`. -/
lemma generatingFunction_neg_pos
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) (hr : 0 < r) :
    0 < generatingFunction F (-r) := by
  rw [← exp_negativeLaplaceLog_eq_generatingFunction_neg F hF r hr]
  exact Real.exp_pos _

/-- A fully explicit global minor-arc bound.  Extracting `N` dyadic
factors gives polynomial decay of arbitrary prescribed order; the remaining
tail costs just one power of the vertical norm. -/
theorem norm_complexGeneratingFunction_neg_vertical_div_le
    (F : BoundedFabius) (hF : IsFabius F)
    (r θ : ℝ) (hr : 0 < r) (N : ℕ) :
    ‖complexGeneratingFunction F
        (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I)))‖ /
          generatingFunction F (-r) ≤
      negativeLaplaceMinorArcConstant r N *
          ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ /
        ‖(1 : ℂ) + (θ : ℂ) * Complex.I‖ ^ N := by
  let w : ℂ := 1 + (θ : ℂ) * Complex.I
  let s : ℝ := r / (2 : ℝ) ^ N
  let complexProd : ℂ := ∏ n ∈ Finset.range N,
    negativeLaplaceDyadicFactor ((r : ℂ) * w) n
  let realProd : ℝ := ∏ n ∈ Finset.range N,
    negativeLaplaceRealDyadicFactor r n
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hw : 0 < ‖w‖ := by
    dsimp [w]
    exact norm_one_add_mul_I_pos θ
  have hrealProd : 0 < realProd := by
    dsimp [realProd]
    apply Finset.prod_pos
    intro n _hn
    exact negativeLaplaceRealDyadicFactor_pos r hr n
  have hscale :
      ((r : ℂ) * w) / (2 : ℂ) ^ N = (s : ℂ) * w := by
    dsimp [s]
    push_cast
    field_simp
  have hcomplex := complexGeneratingFunction_neg_finite_refinement
    F hF ((r : ℂ) * w) N
  change complexGeneratingFunction F (-((r : ℂ) * w)) =
    complexProd * complexGeneratingFunction F
      (-(((r : ℂ) * w) / (2 : ℂ) ^ N)) at hcomplex
  rw [hscale] at hcomplex
  have hreal := generatingFunction_neg_finite_refinement F hF r hr N
  change generatingFunction F (-r) =
    realProd * generatingFunction F (-s) at hreal
  have htail :=
    norm_complexGeneratingFunction_neg_le_real_mul_verticalNorm
      F hF s θ hs
  change ‖complexGeneratingFunction F (-((s : ℂ) * w))‖ ≤
    generatingFunction F (-s) * ‖w‖ at htail
  have hprod :=
    norm_negativeLaplaceDyadicFactor_prod_vertical_div_le r θ hr N
  change ‖complexProd‖ / realProd ≤
    negativeLaplaceMinorArcConstant r N / ‖w‖ ^ N at hprod
  have htailReal : 0 < generatingFunction F (-s) :=
    generatingFunction_neg_pos F hF s hs
  have htailRatio :
      ‖complexGeneratingFunction F (-((s : ℂ) * w))‖ /
          generatingFunction F (-s) ≤ ‖w‖ := by
    rw [div_le_iff₀ htailReal]
    simpa [mul_comm] using htail
  have hmul := mul_le_mul hprod htailRatio
    (div_nonneg (norm_nonneg _ ) htailReal.le)
    (div_nonneg (negativeLaplaceMinorArcConstant_pos r hr N).le
      (pow_nonneg (norm_nonneg _) N))
  have hdecomp :
      ‖complexGeneratingFunction F (-((r : ℂ) * w))‖ /
          generatingFunction F (-r) =
        (‖complexProd‖ / realProd) *
          (‖complexGeneratingFunction F (-((s : ℂ) * w))‖ /
            generatingFunction F (-s)) := by
    rw [hcomplex, hreal, norm_mul]
    field_simp [hrealProd.ne', htailReal.ne']
  dsimp [w] at hdecomp hmul ⊢
  rw [hdecomp]
  exact hmul.trans_eq (by
    field_simp [(norm_one_add_mul_I_pos θ).ne'])

/-- The vertical-line kernel after the natural change of variables
`z = r(1+iθ)`. -/
noncomputable def negativeLaplaceVerticalKernel
    (F : BoundedFabius) (r θ : ℝ) : ℂ :=
  complexGeneratingFunction F
      (-((r : ℂ) * (1 + (θ : ℂ) * Complex.I))) /
    (1 + (θ : ℂ) * Complex.I)

/-- The `N = 2` case of the minor-arc bound, rewritten with
`‖1 + iθ‖ ^ 2 = 1 + θ ^ 2`: the vertical kernel is dominated by
`generatingFunction F (-r) * C(r, 2) * (1 + θ ^ 2)⁻¹` for `r > 0`.  The
constant is explicit; no claim of optimality is made or proved. -/
theorem norm_negativeLaplaceVerticalKernel_le
    (F : BoundedFabius) (hF : IsFabius F)
    (r θ : ℝ) (hr : 0 < r) :
    ‖negativeLaplaceVerticalKernel F r θ‖ ≤
      generatingFunction F (-r) *
        negativeLaplaceMinorArcConstant r 2 * (1 + θ ^ 2)⁻¹ := by
  have h := norm_complexGeneratingFunction_neg_vertical_div_le
    F hF r θ hr 2
  have hreal := generatingFunction_neg_pos F hF r hr
  have hw := norm_one_add_mul_I_pos θ
  rw [div_le_iff₀ hreal] at h
  rw [negativeLaplaceVerticalKernel, norm_div]
  refine (div_le_div_of_nonneg_right h hw.le).trans_eq ?_
  rw [← sq_norm_one_add_mul_I θ]
  field_simp [hw.ne']

/-- For `r > 0` the vertical-line kernel is integrable over all of `ℝ`, by
continuity together with the `(1 + θ ^ 2)⁻¹` domination above.  This is the
analytic input the Bromwich contour needs, and is consumed by
`FabiusBromwichInput` and `FabiusSaddleTail`. -/
theorem integrable_negativeLaplaceVerticalKernel
    (F : BoundedFabius) (hF : IsFabius F)
    (r : ℝ) (hr : 0 < r) :
    Integrable (negativeLaplaceVerticalKernel F r) := by
  have hdom : Integrable (fun θ : ℝ =>
      (generatingFunction F (-r) *
        negativeLaplaceMinorArcConstant r 2) * (1 + θ ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  have hcg : Continuous (complexGeneratingFunction F) := by
    have heq : complexGeneratingFunction F = fun z : ℂ =>
        Complex.exp (z / 2) *
          rvachevFourier F (Complex.I * z / (4 * Real.pi)) := by
      funext z
      exact complexGeneratingFunction_eq_fourier_analytic F hF z
    rw [heq]
    have hrv : Continuous (rvachevFourier F) :=
      (rvachevFourier_differentiable_analytic F hF).continuous
    fun_prop
  have hcont : Continuous (negativeLaplaceVerticalKernel F r) := by
    unfold negativeLaplaceVerticalKernel
    apply Continuous.div
    · exact hcg.comp (by fun_prop)
    · fun_prop
    · intro θ
      exact (norm_one_add_mul_I_pos θ).ne' |>.comp norm_eq_zero.mpr
  apply hdom.mono' hcont.aestronglyMeasurable
  filter_upwards [] with θ
  simpa [mul_assoc] using norm_negativeLaplaceVerticalKernel_le F hF r θ hr

end Fabius

import Lib.CM.Sigma.Basic

/-!
# Circle means, Taylor series at zero, a power bound, and smooth matrix operations

This file proves mean value facts for circle averages and a halving criterion for upper bounds. It
develops the algebra of Taylor series at 0 of analytic functions and proves an elementary bound of
x^l by a factorial and exponentials. It also gives smoothness rules for matrix operations and
extends analytic germs to globally smooth maps.

The imported notion `New.taylorAtZero f` is the formal power series whose `n`-th coefficient is
`iteratedDeriv n f 0 / n !`, the Taylor series of `f : ℂ → ℂ` at 0.

## Main definitions and results

* `New.taylorAtZero_mul`, `New.taylorAtZero_comp_mul`, `New.eq_of_taylorAtZero_eq`: Taylor series
  at 0 of products and of `z ↦ f (a * z)`; such a series determines an entire function.
* `New.integral_eq_of_circle_mean`: an integral is unchanged when the integrand is replaced by its
  mean over a family of measure preserving maps indexed by the circle `ℝ / ℤ`.
* `New.integral_comp_toCircle_eq_apply_zero`: the mean value property over the unit circle of a
  function holomorphic on the closed unit disc, for the Haar probability measure of `ℝ / ℤ`.
* `New.le_of_halving`: let `c ≥ 0`. A function bounded above is at most `c` if each of its bounds
  can be halved at the points where it exceeds `c`.
* `New.exists_contDiff_eventuallyEq`: a map on a finite-dimensional space that is of class `C^ω`
  at a point agrees near it with a globally smooth map.

## Relation to the literature

The results of this file include the mean value property of holomorphic functions and the fact that
an entire function is determined by its Taylor series at 0.
-/

/-! ## Circle averages, the mean value property and a halving criterion for upper bounds -/

section CircleMean

open MeasureTheory Real AddCircle

/-- Averaging over a family of measure preserving maps. Let `μ` be s-finite. Let `T θ`, for `θ` in
`ℝ / ℤ`, be jointly measurable maps that preserve `μ`. If `f` is integrable and the mean of
`f (T θ x)` over `θ` is `g x` for every `x`, then `f` and `g` have the same integral. -/
theorem New.integral_eq_of_circle_mean {G : Type*} [MeasurableSpace G] {μ : Measure G} [SFinite μ]
    {f g : G → ℂ} {T : UnitAddCircle → G → G} (hT_meas : Measurable T.uncurry)
    (hT : ∀ θ : UnitAddCircle, MeasurePreserving (T θ) μ μ) (hf : Integrable f μ)
    (h_mean : ∀ x : G, ∫ θ : UnitAddCircle, f (T θ x) = g x) :
    ∫ x : G, f x ∂μ = ∫ x : G, g x ∂μ := by
  -- Fubini's theorem: average over `θ` last; each `T θ` preserves `μ`, so the inner integral is
  -- then the integral of `f`.
  calc ∫ x : G, f x ∂μ = ∫ _ : UnitAddCircle, ∫ x : G, f x ∂μ := by simp [Measure.real]
    _ = ∫ x : G, (∫ θ : UnitAddCircle, f (T θ x)) ∂μ :=
      (integral_integral_skew_product (fun θ ↦ (hT θ).map_eq) (hf.comp_snd _) hT_meas).symm
    _ = ∫ x : G, g x ∂μ := by simp only [h_mean]

/-- The mean value property: the mean over the unit circle of a function holomorphic on the closed
unit disc is its value at the centre. -/
theorem New.integral_comp_toCircle_eq_apply_zero {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.closedBall 0 1)) :
    ∫ θ : UnitAddCircle, f θ.toCircle = f 0 := by
  -- Mathlib's mean value property, with the period of the angle rescaled from `2π` to `1`.
  calc ∫ θ : UnitAddCircle, f θ.toCircle
      = ∫ t in (0 : ℝ)..1, f (Circle.exp (2 * π * t)) := by
        simp [← AddCircle.intervalIntegral_preimage 1 0, toCircle, -Circle.coe_exp]
    _ = circleAverage f 0 1 := by
        rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ ↦ f (Circle.exp t)) (by positivity)]
        simp [circleAverage, circleMap]
    _ = f 0 := (hf.diffContOnCl_ball (by rw [abs_one])).circleAverage

/-- Halving criterion: let `f` be a real function bounded above and `c ≥ 0`. If for every upper
bound `M ≥ 0` of `f` each value is at most `M / 2` or at most `c`, then `f ≤ c`. -/
lemma New.le_of_halving {X : Sort*} {f : X → ℝ} {c B : ℝ} (hB : ∀ x : X, f x ≤ B) (hc : 0 ≤ c)
    (h_halve : ∀ M ≥ (0 : ℝ), (∀ x : X, f x ≤ M) → ∀ x : X, f x ≤ M / 2 ∨ f x ≤ c) (x : X) :
    f x ≤ c := by
  -- Let `s` be the supremum of `f`. Halving the bound `|s|` gives `s ≤ max (|s| / 2) c`, which
  -- forces `s ≤ c`: if `s ≤ |s| / 2`, then `s ≤ 0 ≤ c`.
  have h_le_sup : ∀ y : X, f y ≤ iSup f := le_ciSup ⟨B, Set.forall_mem_range.2 hB⟩
  have h_sup : iSup f ≤ max (|iSup f| / 2) c :=
    Real.iSup_le (fun y ↦ le_max_iff.2 <| h_halve |iSup f| (abs_nonneg _)
      (fun z ↦ (h_le_sup z).trans (le_abs_self _)) y) (le_max_of_le_right hc)
  have h_sup_le : iSup f ≤ c := by grind
  exact (h_le_sup x).trans h_sup_le

end CircleMean

/-!
## Algebra of one-variable Taylor series at 0

For functions analytic at 0 the Taylor series `New.taylorAtZero` respects sums, products, powers and
polynomial expressions (`New.taylorAtZero_add`, `New.taylorAtZero_mul`, `New.taylorAtZero_pow`,
`New.taylorAtZero_eval`); by `New.taylorAtZero_comp_mul` the series of z ↦ f (a z) is the series of
f rescaled by a, and `New.eq_of_taylorAtZero_eq` says that the Taylor series at 0 determines an
entire function.
-/

section TaylorSeries

open PowerSeries Finset Nat AnalyticAt Complex

attribute [fun_prop] Differentiable.analyticAt

namespace New

@[simp]
lemma coeff_taylorAtZero {f : ℂ → ℂ} (n : ℕ) :
    coeff n (taylorAtZero f) = iteratedDeriv n f 0 / n ! :=
  coeff_mk n _

@[simp]
lemma constantCoeff_taylorAtZero {f : ℂ → ℂ} : constantCoeff (taylorAtZero f) = f 0 := by
  simp [taylorAtZero]

@[simp]
lemma taylorAtZero_const (c : ℂ) : (taylorAtZero fun _ : ℂ ↦ c) = C c := by
  ext ⟨_ | n⟩ <;> simp [iteratedDeriv_const]

/-- The Taylor series `taylorAtZero` at 0 of `z ↦ f (a * z)` is that of `f` with the `n`-th
coefficient multiplied by `a ^ n` (`PowerSeries.rescale a`). No analyticity is needed. -/
@[simp]
lemma taylorAtZero_comp_mul (a : ℂ) (f : ℂ → ℂ) :
    taylorAtZero (fun z : ℂ ↦ f (a * z)) = rescale a (taylorAtZero f) := by
  -- each derivative of `z ↦ f (a * z)` brings out one factor `a`
  have h_deriv (n : ℕ) : iteratedDeriv n (fun z : ℂ ↦ f (a * z)) =
      fun z : ℂ ↦ a ^ n * iteratedDeriv n f (a * z) := by
    induction n with
    | zero => simp
    | succ n ih =>
      ext z
      simp [iteratedDeriv_succ, ih, deriv_comp_mul_left, _root_.pow_succ, mul_assoc]
  ext n
  simp [h_deriv, mul_div_assoc]

/-- Two entire functions with the same Taylor series at 0 are equal. -/
lemma eq_of_taylorAtZero_eq {f g : ℂ → ℂ} (hf_diff : Differentiable ℂ f)
    (hg_diff : Differentiable ℂ g) (h_eq : taylorAtZero f = taylorAtZero g) : f = g := by
  ext z
  -- an entire function is the sum of its Taylor series
  rw [← taylorSeries_eq_of_entire' 0 z hf_diff, ← taylorSeries_eq_of_entire' 0 z hg_diff]
  simp [inv_mul_eq_div, ← coeff_taylorAtZero, h_eq]

/-- The Taylor series at 0 of a sum of two functions analytic at 0 is the sum of their Taylor
series. -/
@[simp]
lemma taylorAtZero_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (fun z : ℂ ↦ f z + g z) = taylorAtZero f + taylorAtZero g := by
  ext n
  simp [iteratedDeriv_fun_add, hf.contDiffAt, hg.contDiffAt, add_div]

/-- The Taylor series at 0 of a product of two functions analytic at 0 is the product of their
Taylor series. -/
@[simp]
lemma taylorAtZero_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylorAtZero (fun z : ℂ ↦ f z * g z) = taylorAtZero f * taylorAtZero g := by
  ext n
  -- Leibniz's rule for `(f g)⁽ⁿ⁾`, with `n.choose i / n ! = 1 / (i ! * (n - i)!)` in each term
  simp only [coeff_mul, coeff_taylorAtZero, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt,
    sum_div, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun i hi ↦ ?_
  rw [cast_choose ℂ (mem_range_succ_iff.1 hi)]
  field [factorial_ne_zero]

/-- Let `f` be analytic at 0 and `P` a polynomial. Then the Taylor series of `P ∘ f` is `P`
evaluated at the Taylor series of `f`. -/
@[simp]
lemma taylorAtZero_eval {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (P : Polynomial ℂ) :
    taylorAtZero (fun z : ℂ ↦ P.eval (f z)) = Polynomial.aeval (taylorAtZero f) P := by
  -- build `P` by adding constants and multiplying by `X`; `taylorAtZero` respects both
  induction P using Polynomial.recOnHorner with
  | M0 => simp
  | MC P c _ _ ih => simp (disch := fun_prop) [ih]
  | MX P _ ih => simp (disch := fun_prop) [ih]

/-- The Taylor series at 0 of `f ^ n` is the `n`-th power of that of `f`, for `f` analytic
at 0. -/
@[simp]
lemma taylorAtZero_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    taylorAtZero (fun z : ℂ ↦ f z ^ n) = taylorAtZero f ^ n := by
  simpa using taylorAtZero_eval hf (Polynomial.X ^ n)

end New

end TaylorSeries

/-! ## A bound of x^l by a factorial and an exponential -/

section PowerExpBound

open Real

/-- For a natural number `l`, a real `x ≥ 0` and a real `v`:
`x ^ l ≤ exp (log l! + l v + x / exp v)`. This is `t ^ l / l! ≤ exp t` at `t = x / exp v`. -/
lemma New.pow_le_exp_log_factorial_add (l : ℕ) (x : NNReal) (v : ℝ) :
    (x : ℝ) ^ l ≤ exp (log l.factorial + l * v + x / exp v) := by
  calc (x : ℝ) ^ l = l.factorial * exp v ^ l * ((x / exp v) ^ l / l.factorial) := by
        simp [field, div_pow]
    _ ≤ l.factorial * exp v ^ l * exp (x / exp v) := by
        gcongr
        exact pow_div_factorial_le_exp _ (by positivity) l
    _ = exp (log l.factorial + l * v + x / exp v) := by
        simp [exp_add, exp_log, l.factorial_pos, exp_nat_mul]

end PowerExpBound

/-!
## Smoothness of matrix operations and extension of analytic germs

Matrices carry the elementwise sup norm. The exponent `N` is any order of smoothness, finite, `∞`
or analytic (`ω`).
-/

section SmoothMatrices

open Matrix ContDiff Norms.Elementwise NormedSpace

namespace New

variable {X l m o : Type*}
  {N : ℕ∞ω} [NormedAddCommGroup X] [NormedSpace ℝ X] [Fintype l] [Fintype m]

/-- A map from a finite-dimensional real normed space to a real normed space that is of class
`C^ω` at `x` (analytic, if the target is complete) agrees near `x` with a globally smooth map. -/
lemma exists_contDiff_eventuallyEq {Y : Type*} [FiniteDimensional ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {f : X → Y} {x : X} (hf : ContDiffAt ℝ ω f x) :
    ∃ g : X → Y, ContDiff ℝ ∞ g ∧ g =ᶠ[nhds x] f := by
  -- Multiply `f` by a bump function supported in the neighbourhood of `x` where `f` is analytic.
  have h_near : {y : X | ContDiffAt ℝ ω f y} ∈ nhds x := hf.eventually (by simp)
  obtain ⟨b, -, (h_supp : tsupport b ⊆ {y : X | ContDiffAt ℝ ω f y})⟩ :=
    (SmoothBumpFunction.nhds_basis_tsupport (I := modelWithCornersSelf ℝ X) x).mem_iff.1 h_near
  refine ⟨fun y ↦ b y • f y, ?_, b.eventuallyEq_one.mono fun y (hy : b y = 1) ↦ by simp [hy]⟩
  refine (contMDiff_of_tsupport fun y hy ↦ ?_).contDiff
  have hf_y : ContDiffAt ℝ ω f y := h_supp (tsupport_smul_subset_left _ _ hy)
  exact b.contMDiffAt.smul (hf_y.contMDiffAt.of_le le_top)

/-- Complex conjugation is smooth over `ℝ`, of every order `N`. -/
@[fun_prop]
lemma contDiff_conj : ContDiff ℝ N (starRingEnd ℂ) := Complex.conjCLE.contDiff

/-- Matrix multiplication of complex matrices is smooth over `ℝ` for the elementwise norm. -/
@[fun_prop]
lemma contDiff_matrix_mul [Fintype o] :
    ContDiff ℝ N fun p : Matrix l m ℂ × Matrix m o ℂ ↦ p.1 * p.2 := by
  refine contDiff_pi' fun i ↦ contDiff_pi' fun j ↦ ?_
  simp only [Matrix.mul_apply]
  fun_prop

/-- The conjugate transpose of complex matrices is smooth over `ℝ` for the elementwise norm. -/
@[fun_prop]
lemma contDiff_conjTranspose : ContDiff ℝ N (conjTranspose : Matrix l m ℂ → Matrix m l ℂ) := by
  refine contDiff_pi' fun i ↦ contDiff_pi' fun j ↦ ?_
  simp only [conjTranspose_apply, ← starRingEnd_apply]
  fun_prop

/-- The exponential of complex square matrices is smooth over `ℝ` for the elementwise norm. -/
@[fun_prop]
lemma contDiff_matrix_exp [DecidableEq m] : ContDiff ℝ N (NormedSpace.exp (𝔸 := Matrix m m ℂ)) := by
  -- The goal uses the elementwise norm, but `exp` is known to be analytic for the operator norm.
  -- The identity `e` from the first normed space to the second is a continuous linear
  -- equivalence, so smoothness carries over.
  open Norms.Operator in
    let e : (m → m → ℂ) ≃L[ℝ] Matrix m m ℂ := .refl ..
    have h_exp : ContDiff ℝ N (exp (𝔸 := Matrix m m ℂ)) :=
      AnalyticOnNhd.contDiff fun A _ ↦ exp_analytic A
    -- `e` is the identity map, so `e.symm ∘ exp ∘ e` is `exp` itself, now for the elementwise norm
    have h_conj : ContDiff ℝ N (e.symm ∘ exp (𝔸 := Matrix m m ℂ) ∘ e) :=
      e.symm.contDiff.comp (h_exp.comp e.contDiff)
    exact h_conj

end New

end SmoothMatrices

import IntegerPoints.IwaniecMozzochi
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Carlson's inequality and Iwaniec--Mozzochi (11.4)

This file isolates the elementary real-analysis argument behind (11.4).  For
`lambda > 0`, Cauchy--Schwarz applied to

```
  |g y| = (|g y| * sqrt (y^2 + lambda^2)) /
    sqrt (y^2 + lambda^2)
```

and

```
  integral y, (y^2 + lambda^2)⁻¹ = pi / lambda
```

give the scaled estimate

```
  (integral y, |g y|)^2 <=
    pi * ((integral y, y^2 * g y^2) / lambda +
      lambda * integral y, g y^2).
```

Optimising in `lambda`, including the two zero-moment cases, gives Carlson's
inequality with the classical constant `sqrt (2 * pi)`.

The final theorem packages the only Fourier-specific input still needed for
Iwaniec--Mozzochi (11.4): the order-four and order-six Plancherel bounds.  With
Mathlib's Fourier normalisation the corresponding exact factors are
`(2 * pi)⁻⁴` and `(2 * pi)⁻⁶`, so the deliberately weaker bounds used here
are enough for the printed constant.
-/

open scoped FourierTransform
open Real MeasureTheory

namespace LeanProofs.IntegerPoints

/-- The Cauchy kernel used in the proof of Carlson's inequality. -/
noncomputable def carlsonKernel (lambda y : ℝ) : ℝ := (y ^ 2 + lambda ^ 2)⁻¹

/-- The Cauchy kernel is integrable for every positive scale. -/
theorem integrable_carlsonKernel {lambda : ℝ} (hlambda : 0 < lambda) :
    Integrable (carlsonKernel lambda) := by
  have hscaled : Integrable (fun y : ℝ => (1 + (y / lambda) ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.comp_div hlambda.ne'
  have hrewrite :
      carlsonKernel lambda =
        fun y : ℝ => (lambda ^ 2)⁻¹ * (1 + (y / lambda) ^ 2)⁻¹ := by
    funext y
    dsimp only [carlsonKernel]
    field_simp [hlambda.ne']
    ring
  rw [hrewrite]
  exact hscaled.const_mul _

/-- Exact mass of the Cauchy kernel. -/
theorem integral_carlsonKernel {lambda : ℝ} (hlambda : 0 < lambda) :
    ∫ y : ℝ, carlsonKernel lambda y = π / lambda := by
  have hrewrite :
      carlsonKernel lambda =
        fun y : ℝ => (lambda ^ 2)⁻¹ * (1 + (y / lambda) ^ 2)⁻¹ := by
    funext y
    dsimp only [carlsonKernel]
    field_simp [hlambda.ne']
    ring
  have hcomp :
      (∫ y : ℝ, (1 + (y / lambda) ^ 2)⁻¹) =
        |lambda| • (∫ y : ℝ, (1 + y ^ 2)⁻¹) :=
    MeasureTheory.Measure.integral_comp_div
      (fun y : ℝ => (1 + y ^ 2)⁻¹) lambda
  rw [hrewrite, integral_const_mul, hcomp,
    integral_univ_inv_one_add_sq, abs_of_pos hlambda, smul_eq_mul]
  field_simp [hlambda.ne']

/-- The precise scaled Cauchy--Schwarz inequality used in the proof of
Carlson's inequality.  This form is particularly convenient for optimisation:
the two quantities on the right are exactly the zeroth and second quadratic
moments of `g`. -/
theorem carlson_cauchy_sq (g : ℝ → ℝ) (hg : Measurable g)
    (hzero : Integrable (fun y : ℝ => g y ^ 2))
    (hsecond : Integrable (fun y : ℝ => y ^ 2 * g y ^ 2))
    {lambda : ℝ} (hlambda : 0 < lambda) :
    (∫ y : ℝ, |g y|) ^ 2 ≤
      π * ((∫ y : ℝ, y ^ 2 * g y ^ 2) / lambda +
        lambda * ∫ y : ℝ, g y ^ 2) := by
  let weight : ℝ → ℝ := fun y => y ^ 2 + lambda ^ 2
  let u : ℝ → ℝ := fun y => |g y| * Real.sqrt (weight y)
  let v : ℝ → ℝ := fun y => (Real.sqrt (weight y))⁻¹

  have hweight_pos (y : ℝ) : 0 < weight y := by
    dsimp only [weight]
    nlinarith [sq_nonneg y, sq_pos_of_pos hlambda]
  have hweight_nonneg (y : ℝ) : 0 ≤ weight y := (hweight_pos y).le

  have hweighted : Integrable (fun y : ℝ => weight y * g y ^ 2) := by
    have hadd := hsecond.add (hzero.const_mul (lambda ^ 2))
    refine hadd.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    dsimp only [weight]
    ring

  have hu_meas : AEStronglyMeasurable u := by
    dsimp only [u, weight]
    have habs : Measurable fun y => |g y| := by
      simpa only [Real.norm_eq_abs] using hg.norm
    exact ((habs.mul ((measurable_id.pow_const 2).add measurable_const).sqrt)).aestronglyMeasurable
  have hv_meas : AEStronglyMeasurable v := by
    dsimp only [v, weight]
    exact (((measurable_id.pow_const 2).add measurable_const).sqrt.inv).aestronglyMeasurable

  have hu_sq : (fun y : ℝ => u y ^ 2) = fun y => weight y * g y ^ 2 := by
    funext y
    dsimp only [u]
    rw [mul_pow, sq_abs, Real.sq_sqrt (hweight_nonneg y)]
    ring
  have hv_sq : (fun y : ℝ => v y ^ 2) = carlsonKernel lambda := by
    funext y
    dsimp only [v, weight, carlsonKernel]
    rw [inv_pow, Real.sq_sqrt]
    exact add_nonneg (sq_nonneg y) (sq_nonneg lambda)
  have huv : (fun y : ℝ => u y * v y) = fun y => |g y| := by
    funext y
    dsimp only [u, v]
    rw [mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.2 (hweight_pos y)), mul_one]

  have huLp : MemLp u 2 := by
    rw [memLp_two_iff_integrable_sq hu_meas, hu_sq]
    exact hweighted
  have hvLp : MemLp v 2 := by
    rw [memLp_two_iff_integrable_sq hv_meas, hv_sq]
    exact integrable_carlsonKernel hlambda

  have hCS := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := u) (g := v) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun y => by dsimp only [u]; positivity)
    (Filter.Eventually.of_forall fun y => by dsimp only [v]; positivity)
    (by simpa using huLp) (by simpa using hvLp)
  simp only [Real.rpow_two] at hCS
  rw [huv, hu_sq, hv_sq] at hCS

  let A : ℝ := ∫ y : ℝ, g y ^ 2
  let B : ℝ := ∫ y : ℝ, y ^ 2 * g y ^ 2
  let W : ℝ := ∫ y : ℝ, weight y * g y ^ 2
  let K : ℝ := ∫ y : ℝ, carlsonKernel lambda y

  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun y => sq_nonneg (g y)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact integral_nonneg fun y => mul_nonneg (sq_nonneg y) (sq_nonneg (g y))
  have hW : 0 ≤ W := by
    dsimp only [W]
    exact integral_nonneg fun y => mul_nonneg (hweight_nonneg y) (sq_nonneg (g y))
  have hK : 0 ≤ K := by
    dsimp only [K, carlsonKernel]
    exact integral_nonneg fun y => inv_nonneg.2 (add_nonneg (sq_nonneg y) (sq_nonneg lambda))
  have hleft : 0 ≤ ∫ y : ℝ, |g y| := integral_nonneg fun y => abs_nonneg (g y)

  have hWroot : (W ^ ((1 : ℝ) / 2)) ^ 2 = W := by
    calc
      (W ^ ((1 : ℝ) / 2)) ^ 2 = W ^ (((1 : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hW ((1 : ℝ) / 2) 2).symm
      _ = W := by norm_num
  have hKroot : (K ^ ((1 : ℝ) / 2)) ^ 2 = K := by
    calc
      (K ^ ((1 : ℝ) / 2)) ^ 2 = K ^ (((1 : ℝ) / 2) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hK ((1 : ℝ) / 2) 2).symm
      _ = K := by norm_num

  have hCSsq : (∫ y : ℝ, |g y|) ^ 2 ≤ W * K := by
    have hsquare := (sq_le_sq₀ hleft
      (mul_nonneg (Real.rpow_nonneg hW _) (Real.rpow_nonneg hK _))).2 hCS
    calc
      (∫ y : ℝ, |g y|) ^ 2 ≤
          (W ^ ((1 : ℝ) / 2) * K ^ ((1 : ℝ) / 2)) ^ 2 := hsquare
      _ = W * K := by rw [mul_pow, hWroot, hKroot]

  have hW_eval : W = B + lambda ^ 2 * A := by
    dsimp only [W, B, A, weight]
    rw [show (fun y : ℝ => (y ^ 2 + lambda ^ 2) * g y ^ 2) =
        fun y : ℝ => y ^ 2 * g y ^ 2 + lambda ^ 2 * g y ^ 2 by
          funext y
          ring]
    rw [integral_add hsecond (hzero.const_mul (lambda ^ 2)), integral_const_mul]
  have hK_eval : K = π / lambda := by
    dsimp only [K]
    exact integral_carlsonKernel hlambda

  calc
    (∫ y : ℝ, |g y|) ^ 2 ≤ W * K := hCSsq
    _ = π * (B / lambda + lambda * A) := by
      rw [hW_eval, hK_eval]
      field_simp [hlambda.ne']

/-- Scalar optimisation of the scaled Cauchy estimate.  The proof treats the
zero-moment cases directly from the estimate for all positive scales; no
nonvanishing hypothesis on `g` is needed. -/
theorem carlson_of_scaled_cauchy_sq {I A B : ℝ}
    (hI : 0 ≤ I) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hscaled : ∀ lambda : ℝ, 0 < lambda →
      I ^ 2 ≤ π * (B / lambda + lambda * A)) :
    I ≤ Real.sqrt (2 * π * Real.sqrt (A * B)) := by
  by_cases hAzero : A = 0
  · have hIzero : I = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hIpos : 0 < I := lt_of_not_ge hnot
        have hI2pos : 0 < I ^ 2 := sq_pos_of_pos hIpos
        let lambda : ℝ := 1 + π * B / I ^ 2
        have hlambda : 0 < lambda := by
          dsimp only [lambda]
          positivity
        have h := hscaled lambda hlambda
        rw [hAzero] at h
        simp only [mul_zero, add_zero] at h
        have hproduct : I ^ 2 * lambda = I ^ 2 + π * B := by
          dsimp only [lambda]
          field_simp [hI2pos.ne']
        have hstrict : π * (B / lambda) < I ^ 2 := by
          rw [show π * (B / lambda) = (π * B) / lambda by ring,
            div_lt_iff₀ hlambda, hproduct]
          linarith
        exact (not_lt_of_ge h) hstrict
      · exact hI
    rw [hIzero]
    exact Real.sqrt_nonneg _
  · have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hAzero)
    by_cases hBzero : B = 0
    · have hIzero : I = 0 := by
        apply le_antisymm
        · by_contra hnot
          have hIpos : 0 < I := lt_of_not_ge hnot
          have hI2pos : 0 < I ^ 2 := sq_pos_of_pos hIpos
          have hdenom : 0 < π * A + I ^ 2 := by positivity
          let lambda : ℝ := I ^ 2 / (π * A + I ^ 2)
          have hlambda : 0 < lambda := div_pos hI2pos hdenom
          have h := hscaled lambda hlambda
          rw [hBzero] at h
          simp only [zero_div, zero_add] at h
          have hstrict : π * (lambda * A) < I ^ 2 := by
            dsimp only [lambda]
            rw [show π * (I ^ 2 / (π * A + I ^ 2) * A) =
                (π * I ^ 2 * A) / (π * A + I ^ 2) by ring,
              div_lt_iff₀ hdenom]
            nlinarith [mul_pos hI2pos hI2pos]
          exact (not_lt_of_ge h) hstrict
        · exact hI
      rw [hIzero]
      exact Real.sqrt_nonneg _
    · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
      let lambda : ℝ := Real.sqrt (B / A)
      have hlambda : 0 < lambda := Real.sqrt_pos.2 (div_pos hBpos hApos)
      have hsqrtA : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
      have hsqrtB : 0 < Real.sqrt B := Real.sqrt_pos.2 hBpos
      have hAsq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
      have hBsq : (Real.sqrt B) ^ 2 = B := Real.sq_sqrt hB
      have hlambda_eval : lambda = Real.sqrt B / Real.sqrt A := by
        dsimp only [lambda]
        rw [Real.sqrt_div hB]
      have hopt : B / lambda + lambda * A = 2 * Real.sqrt (A * B) := by
        rw [hlambda_eval, Real.sqrt_mul hA]
        field_simp [hsqrtA.ne', hsqrtB.ne']
        nlinarith [hAsq, hBsq]
      apply Real.le_sqrt_of_sq_le
      calc
        I ^ 2 ≤ π * (B / lambda + lambda * A) := hscaled lambda hlambda
        _ = 2 * π * Real.sqrt (A * B) := by rw [hopt]; ring

/-- Carlson's inequality in fourth-root form. -/
theorem carlson_integral (g : ℝ → ℝ) (hg : Measurable g)
    (hzero : Integrable (fun y : ℝ => g y ^ 2))
    (hsecond : Integrable (fun y : ℝ => y ^ 2 * g y ^ 2)) :
    (∫ y : ℝ, |g y|) ≤
      Real.sqrt (2 * π) *
        (∫ y : ℝ, g y ^ 2) ^ ((1 : ℝ) / 4) *
        (∫ y : ℝ, y ^ 2 * g y ^ 2) ^ ((1 : ℝ) / 4) := by
  let A : ℝ := ∫ y : ℝ, g y ^ 2
  let B : ℝ := ∫ y : ℝ, y ^ 2 * g y ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun y => sq_nonneg (g y)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact integral_nonneg fun y => mul_nonneg (sq_nonneg y) (sq_nonneg (g y))
  have hbase :
      (∫ y : ℝ, |g y|) ≤ Real.sqrt (2 * π * Real.sqrt (A * B)) :=
    carlson_of_scaled_cauchy_sq
      (integral_nonneg fun y => abs_nonneg (g y)) hA hB
      (fun lambda hlambda => carlson_cauchy_sq g hg hzero hsecond hlambda)

  have hAquarter : (A ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt A := by
    calc
      (A ^ ((1 : ℝ) / 4)) ^ 2 = A ^ (((1 : ℝ) / 4) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hA ((1 : ℝ) / 4) 2).symm
      _ = A ^ ((1 : ℝ) / 2) := by congr 1; ring
      _ = Real.sqrt A := (Real.sqrt_eq_rpow A).symm
  have hBquarter : (B ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt B := by
    calc
      (B ^ ((1 : ℝ) / 4)) ^ 2 = B ^ (((1 : ℝ) / 4) * (2 : ℕ)) :=
        (Real.rpow_mul_natCast hB ((1 : ℝ) / 4) 2).symm
      _ = B ^ ((1 : ℝ) / 2) := by congr 1; ring
      _ = Real.sqrt B := (Real.sqrt_eq_rpow B).symm
  have hconstant :
      Real.sqrt (2 * π * Real.sqrt (A * B)) =
        Real.sqrt (2 * π) * A ^ ((1 : ℝ) / 4) * B ^ ((1 : ℝ) / 4) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    calc
      (Real.sqrt (2 * π * Real.sqrt (A * B))) ^ 2 =
          2 * π * Real.sqrt (A * B) := Real.sq_sqrt (by positivity)
      _ = 2 * π * (Real.sqrt A * Real.sqrt B) := by rw [Real.sqrt_mul hA]
      _ = (Real.sqrt (2 * π) * A ^ ((1 : ℝ) / 4) *
          B ^ ((1 : ℝ) / 4)) ^ 2 := by
        rw [show (Real.sqrt (2 * π) * A ^ ((1 : ℝ) / 4) *
              B ^ ((1 : ℝ) / 4)) ^ 2 =
            (Real.sqrt (2 * π)) ^ 2 * (A ^ ((1 : ℝ) / 4)) ^ 2 *
              (B ^ ((1 : ℝ) / 4)) ^ 2 by ring,
          Real.sq_sqrt (by positivity), hAquarter, hBquarter]
        ring
  simpa only [A, B] using hbase.trans_eq hconstant

/-- Carlson's inequality when the two quadratic moments are bounded by the
squares of nonnegative radii.  This caller-facing form is useful whenever the
moments come from a separate Plancherel or energy estimate: it performs the
fourth-root-to-square-root conversion once and does not expose the optimiser.
-/
theorem carlson_integral_of_quadratic_moment_bounds
    (g : ℝ → ℝ) (hg : Measurable g)
    (hzero : Integrable (fun y : ℝ => g y ^ 2))
    (hsecond : Integrable (fun y : ℝ => y ^ 2 * g y ^ 2))
    {Nzero Nsecond : ℝ} (hNzero : 0 ≤ Nzero) (hNsecond : 0 ≤ Nsecond)
    (hzeroBound : (∫ y : ℝ, g y ^ 2) ≤ Nzero ^ 2)
    (hsecondBound : (∫ y : ℝ, y ^ 2 * g y ^ 2) ≤ Nsecond ^ 2) :
    (∫ y : ℝ, |g y|) ≤
      Real.sqrt (2 * π) * Nzero ^ ((1 : ℝ) / 2) *
        Nsecond ^ ((1 : ℝ) / 2) := by
  let A : ℝ := ∫ y : ℝ, g y ^ 2
  let B : ℝ := ∫ y : ℝ, y ^ 2 * g y ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact integral_nonneg fun y => sq_nonneg (g y)
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact integral_nonneg fun y => mul_nonneg (sq_nonneg y) (sq_nonneg (g y))
  have hAroot : A ^ ((1 : ℝ) / 4) ≤ Nzero ^ ((1 : ℝ) / 2) := by
    calc
      A ^ ((1 : ℝ) / 4) ≤ (Nzero ^ 2) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hA (by simpa only [A] using hzeroBound) (by norm_num)
      _ = Nzero ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast Nzero 2, ← Real.rpow_mul hNzero]
        congr 1
        ring
  have hBroot : B ^ ((1 : ℝ) / 4) ≤ Nsecond ^ ((1 : ℝ) / 2) := by
    calc
      B ^ ((1 : ℝ) / 4) ≤ (Nsecond ^ 2) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hB (by simpa only [B] using hsecondBound) (by norm_num)
      _ = Nsecond ^ ((1 : ℝ) / 2) := by
        rw [← Real.rpow_natCast Nsecond 2, ← Real.rpow_mul hNsecond]
        congr 1
        ring
  calc
    (∫ y : ℝ, |g y|) ≤
        Real.sqrt (2 * π) * A ^ ((1 : ℝ) / 4) * B ^ ((1 : ℝ) / 4) := by
      simpa only [A, B] using carlson_integral g hg hzero hsecond
    _ = Real.sqrt (2 * π) *
          (A ^ ((1 : ℝ) / 4) * B ^ ((1 : ℝ) / 4)) := by ring
    _ ≤ Real.sqrt (2 * π) *
          (Nzero ^ ((1 : ℝ) / 2) * Nsecond ^ ((1 : ℝ) / 2)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hAroot hBroot (Real.rpow_nonneg hB _)
          (Real.rpow_nonneg hNzero _))
        (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * π) * Nzero ^ ((1 : ℝ) / 2) *
          Nsecond ^ ((1 : ℝ) / 2) := by ring

/-- The nonnegative Fourier density whose zeroth and second quadratic moments
are, respectively, the order-four and order-six Fourier moments in (11.4). -/
noncomputable def eq114FourierDensity (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ 2 * ‖𝓕 (fun t : ℝ => (f t : ℂ)) y‖

/-- The exact Fourier-specific interface needed by the Carlson argument for
(11.4).  The last two fields are the weak forms of the derivative--Plancherel
identities; Mathlib's Fourier normalisation actually supplies the smaller
factors `(2 * pi)⁻⁴` and `(2 * pi)⁻⁶`. -/
def HasEq114FourierMomentBounds (f : ℝ → ℝ) : Prop :=
  Measurable (eq114FourierDensity f) ∧
  Integrable (fun y : ℝ => eq114FourierDensity f y ^ 2) ∧
  Integrable (fun y : ℝ => y ^ 2 * eq114FourierDensity f y ^ 2) ∧
  (∫ y : ℝ, eq114FourierDensity f y ^ 2) ≤
      imL2Norm (iteratedDeriv 2 f) ^ 2 ∧
  (∫ y : ℝ, y ^ 2 * eq114FourierDensity f y ^ 2) ≤
      imL2Norm (iteratedDeriv 3 f) ^ 2

/-- Pointwise (11.4), conditional only on its two derivative--Plancherel
moment bounds and the measurability/integrability needed to state Carlson's
inequality. -/
theorem iwaniecMozzochi_eq114_of_fourier_moment_bounds {f : ℝ → ℝ}
    (hdata : HasEq114FourierMomentBounds f) :
    secondMomentFourier f ≤
      Real.sqrt (2 * π) * imL2Norm (iteratedDeriv 2 f) ^ ((1 : ℝ) / 2) *
        imL2Norm (iteratedDeriv 3 f) ^ ((1 : ℝ) / 2) := by
  rcases hdata with ⟨hmeas, hint0, hint2, hmoment2, hmoment3⟩
  let g : ℝ → ℝ := eq114FourierDensity f
  let N2 : ℝ := imL2Norm (iteratedDeriv 2 f)
  let N3 : ℝ := imL2Norm (iteratedDeriv 3 f)

  have hN2 : 0 ≤ N2 := by
    dsimp only [N2, imL2Norm]
    exact Real.sqrt_nonneg _
  have hN3 : 0 ≤ N3 := by
    dsimp only [N3, imL2Norm]
    exact Real.sqrt_nonneg _

  have hCarlson := carlson_integral_of_quadratic_moment_bounds g
    (by simpa only [g] using hmeas)
    (by simpa only [g] using hint0)
    (by simpa only [g] using hint2)
    hN2 hN3
    (by simpa only [N2, g] using hmoment2)
    (by simpa only [N3, g] using hmoment3)
  have hleft : secondMomentFourier f = ∫ y : ℝ, |g y| := by
    unfold secondMomentFourier
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      dsimp only [g, eq114FourierDensity]
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg y) (norm_nonneg _))]

  rw [hleft]
  simpa only [N2, N3] using hCarlson

/-- The statement of Iwaniec--Mozzochi (11.4), conditional on the minimal
Fourier moment interface used by the elementary Carlson argument. -/
theorem iwaniecMozzochi_lemma111_eq114_of_fourier_moment_bounds
    (hdata : ∀ f : ℝ → ℝ, IsSmoothCompactPos f → HasEq114FourierMomentBounds f) :
    iwaniecMozzochi_lemma111_eq114 := by
  intro f hf
  exact iwaniecMozzochi_eq114_of_fourier_moment_bounds (hdata f hf)

end LeanProofs.IntegerPoints

import Mathlib.Analysis.Fourier.Inversion

/-!
# Fourier inversion in saddle-point coordinates

This module derives the real Bromwich formula needed for the Fabius-function
asymptotic directly from Mathlib's Fourier inversion theorem.  It then performs
the exact real change of variables that puts a transform of the form `P z / z`
in dimensionless saddle-point coordinates.

There is no contour-shifting argument here.  Every analytic and integrability
hypothesis needed by Fourier inversion is explicit in the theorem statements.
The normalized saddle kernel is also recorded at its central coordinate,
where it is exactly `1` whenever the normalizing value `P r` is nonzero.
-/

set_option autoImplicit false

open Filter MeasureTheory
open scoped FourierTransform

namespace Fabius.QuantitativeSaddle

/-- Exponential tilting turns a bilateral Laplace transform on the vertical
line `Re z = r` into Mathlib's Fourier transform. -/
noncomputable def exponentialTilt (f : ℝ → ℂ) (r x : ℝ) : ℂ :=
  Complex.exp (-(r * x : ℝ)) * f x

/-- Fourier inversion written as a Bromwich integral.

Mathlib normalizes the Fourier transform with `exp (-2 π i ξ x)`, so the
vertical variable in this statement is `2 π ξ`. -/
theorem fourier_bromwich
    (f : ℝ → ℂ) (r x : ℝ) (L : ℂ → ℂ)
    (hcont : Continuous (exponentialTilt f r))
    (hint : Integrable (exponentialTilt f r))
    (htransform : ∀ ξ : ℝ,
      𝓕 (exponentialTilt f r) ξ =
        L ((r : ℂ) + 2 * Real.pi * Complex.I * ξ))
    (htransformInt : Integrable (𝓕 (exponentialTilt f r))) :
    f x = Complex.exp (r * x) *
      ∫ ξ : ℝ,
        Complex.exp (2 * Real.pi * Complex.I * (ξ * x)) *
          L ((r : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
  have hinv := congr_fun (hcont.fourierInv_fourier_eq hint htransformInt) x
  rw [Real.fourierInv_eq'] at hinv
  simp_rw [htransform] at hinv
  simp only [Real.inner_apply] at hinv
  have hintegral :
      (∫ ξ : ℝ,
          Complex.exp ((2 * Real.pi * (ξ * x) : ℝ) * Complex.I) •
            L ((r : ℂ) + 2 * Real.pi * Complex.I * ξ)) =
        ∫ ξ : ℝ,
          Complex.exp (2 * Real.pi * Complex.I * (ξ * x)) *
            L ((r : ℂ) + 2 * Real.pi * Complex.I * ξ) := by
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [smul_eq_mul]
    congr 2
    push_cast
    ring
  rw [hintegral] at hinv
  rw [exponentialTilt] at hinv
  rw [hinv]
  rw [← mul_assoc, ← Complex.exp_add]
  have hzero : (r : ℂ) * (x : ℂ) + -((r * x : ℝ) : ℂ) = 0 := by
    push_cast
    ring
  rw [hzero, Complex.exp_zero, one_mul]

/-- The dimensionless kernel obtained from a transform `P z / z` after the
saddle substitution `z = r (1 + i v / √b)`. -/
noncomputable def scaledSaddleKernel
    (P : ℂ → ℂ) (x r b v : ℝ) : ℂ :=
  Complex.exp (((r * x * v / Real.sqrt b : ℝ) : ℂ) * Complex.I) *
    (P ((r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I) /
      P (r : ℂ)) /
    (1 + ((v / Real.sqrt b : ℝ) : ℂ) * Complex.I)

/-- At the central coordinate `v = 0`, the normalized saddle kernel is
exactly `1`.  No positivity assumption on the scale is needed for this
algebraic normalization. -/
theorem scaledSaddleKernel_zero
    (P : ℂ → ℂ) (x r b : ℝ) (hPr : P (r : ℂ) ≠ 0) :
    scaledSaddleKernel P x r b 0 = 1 := by
  simp [scaledSaddleKernel, hPr]

/-- Exact Fourier/Bromwich formula in dimensionless saddle coordinates.

The conclusion separates the expected saddle prefactor from the normalized
kernel integral.  Positivity of `r` and `b` and nonvanishing of `P r` are used
only in this exact change of variables; all transform hypotheses remain
explicit. -/
theorem fourier_bromwich_scaled
    (f : ℝ → ℂ) (P : ℂ → ℂ) (r b x : ℝ)
    (hr : 0 < r) (hb : 0 < b) (hPr : P (r : ℂ) ≠ 0)
    (hcont : Continuous (exponentialTilt f r))
    (hint : Integrable (exponentialTilt f r))
    (htransform : ∀ ξ : ℝ,
      𝓕 (exponentialTilt f r) ξ =
        P ((r : ℂ) + 2 * Real.pi * Complex.I * ξ) /
          ((r : ℂ) + 2 * Real.pi * Complex.I * ξ))
    (htransformInt : Integrable (𝓕 (exponentialTilt f r))) :
    f x =
      Complex.exp (r * x) * P (r : ℂ) /
          (Real.sqrt (2 * Real.pi * b) : ℂ) *
        ((Real.sqrt (2 * Real.pi) : ℂ)⁻¹ *
          ∫ v : ℝ, scaledSaddleKernel P x r b v) := by
  let H : ℝ → ℂ := fun ξ =>
    Complex.exp (2 * Real.pi * Complex.I * (ξ * x)) *
      (P ((r : ℂ) + 2 * Real.pi * Complex.I * ξ) /
        ((r : ℂ) + 2 * Real.pi * Complex.I * ξ))
  have hB := fourier_bromwich f r x
    (fun z => P z / z) hcont hint htransform htransformInt
  change f x = Complex.exp (r * x) * ∫ ξ : ℝ, H ξ at hB
  rw [hB]
  let a : ℝ := r / (2 * Real.pi * Real.sqrt b)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hscale : (∫ ξ : ℝ, H ξ) = (a : ℂ) * ∫ v : ℝ, H (a * v) := by
    have hs := Measure.integral_comp_mul_left (fun v => H (a * v)) a⁻¹
    simpa [ha.ne', abs_of_pos ha, smul_eq_mul] using hs
  rw [hscale]
  have hsqrt : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hb)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hpoint : ∀ v : ℝ,
      (a : ℂ) * H (a * v) =
        P (r : ℂ) / (2 * Real.pi * Real.sqrt b : ℝ) *
          scaledSaddleKernel P x r b v := by
    intro v
    dsimp [H, a, scaledSaddleKernel]
    have hfreq :
        (2 * Real.pi * Complex.I *
          ((((r / (2 * Real.pi * Real.sqrt b)) * v : ℝ) : ℂ))) =
          (((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I) := by
      push_cast
      field_simp
    have hphase :
        (2 * Real.pi * Complex.I *
          ((((r / (2 * Real.pi * Real.sqrt b)) * v : ℝ) : ℂ) *
            (x : ℂ))) =
          (((r * x * v / Real.sqrt b : ℝ) : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [hfreq, hphase]
    have hfactor :
        (r : ℂ) + ((r * v / Real.sqrt b : ℝ) : ℂ) * Complex.I =
          (r : ℂ) *
            (1 + ((v / Real.sqrt b : ℝ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [hfactor]
    have hone :
        (1 + ((v / Real.sqrt b : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
    let c : ℂ := ((2 * Real.pi * Real.sqrt b : ℝ) : ℂ)
    have hc : c ≠ 0 := by
      dsimp [c]
      exact_mod_cast mul_ne_zero (mul_ne_zero (by norm_num) hpi) hsqrt
    have haC :
        (((r / (2 * Real.pi * Real.sqrt b) : ℝ) : ℂ)) =
          (r : ℂ) / c := by
      dsimp [c]
      push_cast
      rfl
    have halg (aa rr cc E Q p zz : ℂ)
        (hcc : cc ≠ 0) (hrr : rr ≠ 0) (hp : p ≠ 0) (hzz : zz ≠ 0)
        (haa : aa = rr / cc) :
        aa * (E * (Q / (rr * zz))) =
          p / cc * (E * (Q / p) / zz) := by
      rw [haa]
      field_simp
    exact halg _ _ _ _ _ _ _ hc (Complex.ofReal_ne_zero.mpr hr.ne')
      hPr hone haC
  rw [← integral_const_mul]
  have hinterchange :
      (∫ v : ℝ, (a : ℂ) * H (a * v)) =
        ∫ v : ℝ,
          P (r : ℂ) / (2 * Real.pi * Real.sqrt b : ℝ) *
            scaledSaddleKernel P x r b v := by
    apply integral_congr_ae
    filter_upwards with v
    exact hpoint v
  rw [hinterchange, integral_const_mul]
  have hsqrt_mul :
      Real.sqrt (2 * Real.pi * b) =
        Real.sqrt (2 * Real.pi) * Real.sqrt b := by
    rw [show 2 * Real.pi * b = (2 * Real.pi) * b by ring,
      Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
  rw [hsqrt_mul]
  push_cast
  field_simp [hsqrt, hpi]
  have hsquare :
      (Real.sqrt (2 * Real.pi) : ℂ) ^ 2 = 2 * (Real.pi : ℂ) := by
    norm_cast
    rw [Real.sq_sqrt]
    positivity
  rw [hsquare]
  ring

end Fabius.QuantitativeSaddle

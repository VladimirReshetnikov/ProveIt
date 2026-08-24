import IntegerPoints.IwaniecMozzochiEq114Carlson
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# The Fourier--Plancherel input to Iwaniec--Mozzochi (11.4)

This file discharges the Fourier moment interface isolated in
`IwaniecMozzochiEq114Carlson`.  A smooth compactly supported real function,
after composition with the isometric embedding `ℝ → ℂ`, is a Schwartz
function.  Multiplication of its Fourier transform by `y ^ 2` and `y ^ 3`
therefore remains in Schwartz space, which supplies the two required
square-integrability statements.

Mathlib normalises the Fourier transform with kernel `exp (-2 * pi * I * x * y)`.
Consequently,

```
  𝓕 (f⁽ⁿ⁾) y = (2 * pi * I * y) ^ n * 𝓕 f y,
```

and its Schwartz-space Plancherel theorem has no additional constant.  The
exact fourth- and sixth-moment identities thus contain the factors
`(2 * pi)⁻⁴` and `(2 * pi)⁻⁶`.  We only need the weaker coefficient-one bounds
packaged by `HasEq114FourierMomentBounds`.

There is no new trust assumption in this bridge: compact support to Schwartz,
Fourier differentiation, and Plancherel are all proved Mathlib theorems.  In
particular, the file introduces no axioms, opaque computational certificates,
or native-code evaluation boundary.
-/

open scoped FourierTransform SchwartzMap ContDiff
open Real MeasureTheory
open LineDeriv

namespace LeanProofs.IntegerPoints

/-- The square of the norm of a complex Schwartz function is integrable. -/
private theorem integrable_norm_sq_schwartz (u : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => ‖u x‖ ^ 2) := by
  exact (memLp_two_iff_integrable_sq_norm u.continuous.aestronglyMeasurable).1
    (u.memLp 2)

/-- Pointwise domination of squared Schwartz norms integrates monotonically.
Packaging integrability at the Schwartz level keeps downstream applications
small even when the functions are built from dependent local definitions. -/
private theorem integral_norm_sq_schwartz_mono (u v : 𝓢(ℝ, ℂ))
    (huv : forall x : ℝ, ‖u x‖ ^ 2 ≤ ‖v x‖ ^ 2) :
    (∫ x : ℝ, ‖u x‖ ^ 2) ≤ ∫ x : ℝ, ‖v x‖ ^ 2 := by
  exact MeasureTheory.integral_mono
    (integrable_norm_sq_schwartz u) (integrable_norm_sq_schwartz v) huv

/-- The real-to-complex embedding preserves the norm of every iterated
derivative. -/
private theorem norm_iteratedDeriv_ofReal {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (n : ℕ) (x : ℝ) :
    ‖iteratedDeriv n (Complex.ofRealCLM ∘ f) x‖ = ‖iteratedDeriv n f x‖ := by
  calc
    ‖iteratedDeriv n (Complex.ofRealCLM ∘ f) x‖ =
        ‖iteratedFDeriv ℝ n (Complex.ofRealCLM ∘ f) x‖ :=
      norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm
    _ = ‖iteratedFDeriv ℝ n f x‖ := by
      change ‖iteratedFDeriv ℝ n (Complex.ofRealLI ∘ f) x‖ =
        ‖iteratedFDeriv ℝ n f x‖
      exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left
        hf.contDiffAt (mod_cast le_top)
    _ = ‖iteratedDeriv n f x‖ := norm_iteratedFDeriv_eq_norm_iteratedDeriv

/-- Squaring the project-local `L²` norm recovers its defining integral. -/
private theorem integral_sq_eq_imL2Norm_sq (g : ℝ → ℝ) :
    (∫ x : ℝ, g x ^ 2) = imL2Norm g ^ 2 := by
  unfold imL2Norm
  exact (Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (g x))).symm

/-- Smoothness and compact support alone supply all Fourier moment data used
by the Carlson proof of Iwaniec--Mozzochi (11.4). -/
theorem hasEq114FourierMomentBounds_of_smooth_compact {f : ℝ → ℝ}
    (hsmooth : ContDiff ℝ ∞ f) (hcompact : HasCompactSupport f) :
    HasEq114FourierMomentBounds f := by
  let fc : ℝ → ℂ := Complex.ofRealCLM ∘ f
  have hfc_compact : HasCompactSupport fc := by
    dsimp only [fc]
    exact hcompact.comp_left rfl
  have hfc_smooth : ContDiff ℝ ∞ fc := by
    simpa only [fc] using Complex.ofRealCLM.contDiff.comp hsmooth
  let phi : 𝓢(ℝ, ℂ) := hfc_compact.toSchwartzMap hfc_smooth
  have hphi_fun : (phi : ℝ → ℂ) = fc := rfl

  let D (n : ℕ) : 𝓢(ℝ, ℂ) :=
    ∂^{fun _ : Fin n => (1 : ℝ)} phi
  have hD_apply (n : ℕ) (x : ℝ) :
      D n x = iteratedDeriv n fc x := by
    dsimp only [D]
    rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
      iteratedDeriv_eq_iteratedFDeriv, hphi_fun]
  have hD_fun (n : ℕ) : (D n : ℝ → ℂ) = iteratedDeriv n fc := by
    funext x
    exact hD_apply n x
  have hfc_deriv_integrable (n : ℕ) : Integrable (iteratedDeriv n fc) :=
    (D n).integrable.congr <| Filter.Eventually.of_forall (hD_apply n)

  have hfourier_deriv (n : ℕ) :
      𝓕 (iteratedDeriv n fc) =
        fun y : ℝ => (2 * π * Complex.I * y) ^ n • 𝓕 fc y := by
    exact Real.fourier_iteratedDeriv (N := (⊤ : ℕ∞)) hfc_smooth
      (fun m _ => hfc_deriv_integrable m) (by simp)
  have hFD_apply (n : ℕ) (y : ℝ) :
      (𝓕 (D n)) y =
        (2 * π * Complex.I * y) ^ n • (𝓕 phi) y := by
    change 𝓕 (D n : ℝ → ℂ) y =
      (2 * π * Complex.I * y) ^ n • 𝓕 (phi : ℝ → ℂ) y
    rw [hD_fun n, hphi_fun]
    exact congrFun (hfourier_deriv n) y

  have hpoly (n : ℕ) :
      Function.HasTemperateGrowth (fun y : ℝ => (y : ℂ) ^ n) := by
    fun_prop
  let W (n : ℕ) : 𝓢(ℝ, ℂ) :=
    SchwartzMap.smulLeftCLM ℂ (fun y : ℝ => (y : ℂ) ^ n) (𝓕 phi)
  have hW_apply (n : ℕ) (y : ℝ) :
      W n y = (y : ℂ) ^ n * (𝓕 phi) y := by
    simp only [W, SchwartzMap.smulLeftCLM_apply_apply (hpoly n), smul_eq_mul]
  have hW_sq_integrable (n : ℕ) :
      Integrable (fun y : ℝ => ‖W n y‖ ^ 2) :=
    integrable_norm_sq_schwartz (W n)
  have hmeas : Measurable (eq114FourierDensity f) := by
    apply Continuous.measurable
    change Continuous (fun y : ℝ => y ^ 2 * ‖(𝓕 phi) y‖)
    fun_prop

  have hW2_sq (y : ℝ) :
      ‖W 2 y‖ ^ 2 = eq114FourierDensity f y ^ 2 := by
    rw [hW_apply]
    change ‖(y : ℂ) ^ 2 * (𝓕 phi) y‖ ^ 2 =
      (y ^ 2 * ‖(𝓕 phi) y‖) ^ 2
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hW3_sq (y : ℝ) :
      ‖W 3 y‖ ^ 2 = y ^ 2 * eq114FourierDensity f y ^ 2 := by
    rw [hW_apply]
    change ‖(y : ℂ) ^ 3 * (𝓕 phi) y‖ ^ 2 =
      y ^ 2 * (y ^ 2 * ‖(𝓕 phi) y‖) ^ 2
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    calc
      (|y| ^ 3 * ‖(𝓕 phi) y‖) ^ 2 =
          (|y| ^ 2) ^ 3 * ‖(𝓕 phi) y‖ ^ 2 := by ring
      _ = y ^ 2 * (y ^ 2 * ‖(𝓕 phi) y‖) ^ 2 := by
        rw [sq_abs]
        ring

  have hint0 : Integrable (fun y : ℝ => eq114FourierDensity f y ^ 2) :=
    (hW_sq_integrable 2).congr <|
      Filter.Eventually.of_forall hW2_sq
  have hint2 :
      Integrable (fun y : ℝ => y ^ 2 * eq114FourierDensity f y ^ 2) :=
    (hW_sq_integrable 3).congr <|
      Filter.Eventually.of_forall hW3_sq

  have hscale2 (y : ℝ) :
      ‖(𝓕 (D 2)) y‖ ^ 2 = (2 * π : ℝ) ^ 4 * ‖W 2 y‖ ^ 2 := by
    rw [hFD_apply, hW_apply]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_two,
      Complex.norm_real, Real.norm_eq_abs]
    ring
  have hscale3 (y : ℝ) :
      ‖(𝓕 (D 3)) y‖ ^ 2 = (2 * π : ℝ) ^ 6 * ‖W 3 y‖ ^ 2 := by
    rw [hFD_apply, hW_apply]
    simp only [norm_smul, norm_pow, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_of_nonneg Real.pi_pos.le, Complex.norm_two,
      Complex.norm_real, Real.norm_eq_abs]
    ring

  have htwo_pi : (1 : ℝ) ≤ 2 * π := by
    nlinarith [Real.two_le_pi]
  have hpoint2 (y : ℝ) :
      ‖W 2 y‖ ^ 2 ≤ ‖(𝓕 (D 2)) y‖ ^ 2 := by
    rw [hscale2]
    exact le_mul_of_one_le_left (sq_nonneg ‖W 2 y‖) (one_le_pow₀ htwo_pi)
  have hpoint3 (y : ℝ) :
      ‖W 3 y‖ ^ 2 ≤ ‖(𝓕 (D 3)) y‖ ^ 2 := by
    rw [hscale3]
    exact le_mul_of_one_le_left (sq_nonneg ‖W 3 y‖) (one_le_pow₀ htwo_pi)

  have hD_sq (n : ℕ) (x : ℝ) :
      ‖D n x‖ ^ 2 = iteratedDeriv n f x ^ 2 := by
    rw [hD_apply, norm_iteratedDeriv_ofReal hsmooth,
      Real.norm_eq_abs, sq_abs]

  have hmoment2 :
      (∫ y : ℝ, eq114FourierDensity f y ^ 2) ≤
        imL2Norm (iteratedDeriv 2 f) ^ 2 := by
    calc
      (∫ y : ℝ, eq114FourierDensity f y ^ 2) =
          ∫ y : ℝ, ‖W 2 y‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => (hW2_sq y).symm
      _ ≤ ∫ y : ℝ, ‖(𝓕 (D 2)) y‖ ^ 2 :=
        integral_norm_sq_schwartz_mono (W 2) (𝓕 (D 2)) hpoint2
      _ = ∫ x : ℝ, ‖D 2 x‖ ^ 2 :=
        SchwartzMap.integral_norm_sq_fourier (D 2)
      _ = ∫ x : ℝ, iteratedDeriv 2 f x ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (hD_sq 2)
      _ = imL2Norm (iteratedDeriv 2 f) ^ 2 :=
        integral_sq_eq_imL2Norm_sq (iteratedDeriv 2 f)

  have hmoment3 :
      (∫ y : ℝ, y ^ 2 * eq114FourierDensity f y ^ 2) ≤
        imL2Norm (iteratedDeriv 3 f) ^ 2 := by
    calc
      (∫ y : ℝ, y ^ 2 * eq114FourierDensity f y ^ 2) =
          ∫ y : ℝ, ‖W 3 y‖ ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => (hW3_sq y).symm
      _ ≤ ∫ y : ℝ, ‖(𝓕 (D 3)) y‖ ^ 2 :=
        integral_norm_sq_schwartz_mono (W 3) (𝓕 (D 3)) hpoint3
      _ = ∫ x : ℝ, ‖D 3 x‖ ^ 2 :=
        SchwartzMap.integral_norm_sq_fourier (D 3)
      _ = ∫ x : ℝ, iteratedDeriv 3 f x ^ 2 := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (hD_sq 3)
      _ = imL2Norm (iteratedDeriv 3 f) ^ 2 :=
        integral_sq_eq_imL2Norm_sq (iteratedDeriv 3 f)

  exact ⟨hmeas, hint0, hint2, hmoment2, hmoment3⟩

/-- The support-in-`(0, ∞)` formulation used by Iwaniec--Mozzochi supplies the
smoothness and compactness required by the Fourier bridge.  Its positivity
field is not needed for (11.4). -/
theorem hasEq114FourierMomentBounds_of_isSmoothCompactPos {f : ℝ → ℝ}
    (hf : IsSmoothCompactPos f) : HasEq114FourierMomentBounds f :=
  hasEq114FourierMomentBounds_of_smooth_compact hf.1 hf.2.1

/-- Iwaniec--Mozzochi, Lemma 11.1, equation (11.4), with every analytic input
discharged. -/
theorem iwaniecMozzochi_lemma111_eq114_holds :
    iwaniecMozzochi_lemma111_eq114 := by
  apply iwaniecMozzochi_lemma111_eq114_of_fourier_moment_bounds
  intro f hf
  exact hasEq114FourierMomentBounds_of_isSmoothCompactPos hf

end LeanProofs.IntegerPoints

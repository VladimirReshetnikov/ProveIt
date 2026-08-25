import FabiusFunction.Differential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Analytic Fourier identities for Rvachev's function

This module proves that the complex Fourier transform of Rvachev's compactly
supported smooth function is entire, establishes Fourier inversion, and
relates the transform at imaginary arguments to the half-moment generating
function.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators ContDiff Interval FourierTransform SchwartzMap
open MeasureTheory Set

namespace Fabius

noncomputable section

/-- Rvachev's compactly supported function has support contained in `[-1, 1]`. -/
theorem rvachevUp_support_subset (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) ⊆ Icc (-1 : ℝ) 1 :=
  (support_rvachev_subset_Ioo F hF).trans Ioo_subset_Icc_self

/-- Rvachev's function has compact support. -/
theorem rvachevUp_hasCompactSupport (F : BoundedFabius) (hF : IsFabius F) :
    HasCompactSupport (rvachevUp F) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (rvachevUp_support_subset F hF)

/-- The complex-valued coercion of Rvachev's function is smooth. -/
theorem rvachevUp_complex_contDiff
    (F : BoundedFabius) (hF : IsFabius F) :
    ContDiff ℝ ∞ (fun x : ℝ => (rvachevUp F x : ℂ)) := by
  change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ rvachevUp F)
  exact Complex.ofRealCLM.contDiff.comp (rvachev_contDiff F hF)

/-- The complex-valued coercion of Rvachev's function also has compact support. -/
theorem rvachevUp_complex_hasCompactSupport
    (F : BoundedFabius) (hF : IsFabius F) :
    HasCompactSupport (fun x : ℝ => (rvachevUp F x : ℂ)) :=
  (rvachevUp_hasCompactSupport F hF).comp_left (map_zero Complex.ofRealCLM)

set_option backward.isDefEq.respectTransparency false in
/-- The complex Fourier transform of Rvachev's function is entire. -/
theorem rvachevFourier_differentiable_analytic
    (F : BoundedFabius) (hF : IsFabius F) :
    Differentiable ℂ (rvachevFourier F) := by
  let A : ℂ := -2 * Real.pi * Complex.I
  let G : ℂ → ℝ → ℂ := fun z t =>
    (rvachevUp F t : ℂ) * Complex.exp (A * (t : ℂ) * z)
  let G' : ℂ → ℝ → ℂ := fun z t =>
    (rvachevUp F t : ℂ) * Complex.exp (A * (t : ℂ) * z) *
      (A * (t : ℂ))
  have hcont : Continuous (fun t : ℝ => (rvachevUp F t : ℂ)) :=
    (rvachevUp_complex_contDiff F hF).continuous
  have hcomp : HasCompactSupport (fun t : ℝ => (rvachevUp F t : ℂ)) :=
    rvachevUp_complex_hasCompactSupport F hF
  intro z
  let K : ℝ := Real.exp (‖A‖ * (‖z‖ + 1)) * ‖A‖
  let bound : ℝ → ℝ := fun t => K * ‖(rvachevUp F t : ℂ)‖
  have hbound_int : Integrable bound := by
    exact (hcont.norm.integrable_of_hasCompactSupport hcomp.norm).const_mul K
  have hG_int : Integrable (G z) := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp [G]
      fun_prop
    · exact hcomp.mul_right
  have hG'_meas : AEStronglyMeasurable (G' z) := by
    apply Continuous.aestronglyMeasurable
    dsimp [G']
    fun_prop
  have hderiv : ∀ (t : ℝ) (w : ℂ),
      HasDerivAt (fun q : ℂ => G q t) (G' w t) w := by
    intro t w
    dsimp [G, G']
    convert! (((hasDerivAt_id w).const_mul (A * (t : ℂ))).cexp.const_mul
      (rvachevUp F t : ℂ)) using 1
    simp [id]
    ring
  have hbound : ∀ (t : ℝ) (w : ℂ), w ∈ Metric.ball z 1 →
      ‖G' w t‖ ≤ bound t := by
    intro t w hw
    by_cases hup : rvachevUp F t = 0
    · simp [G', bound, hup, K]
    have ht := rvachevUp_support_subset F hF
      (show t ∈ Function.support (rvachevUp F) from hup)
    have ht_norm : ‖t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ht
    have hw_norm : ‖w‖ ≤ ‖z‖ + 1 := by
      calc
        ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
          simpa [sub_eq_add_neg, add_comm] using norm_add_le z (w - z)
        _ ≤ ‖z‖ + 1 := by
          gcongr
          exact le_of_lt (by simpa [dist_eq_norm] using hw)
    change ‖(rvachevUp F t : ℂ) * Complex.exp (A * (t : ℂ) * w) *
        (A * (t : ℂ))‖ ≤ K * ‖(rvachevUp F t : ℂ)‖
    rw [norm_mul, norm_mul, Complex.norm_exp]
    rw [norm_mul A (t : ℂ), Complex.norm_real t]
    have hre : (A * (t : ℂ) * w).re ≤ ‖A‖ * (‖z‖ + 1) := by
      calc
        (A * (t : ℂ) * w).re ≤ ‖A * (t : ℂ) * w‖ := Complex.re_le_norm _
        _ = ‖A‖ * ‖t‖ * ‖w‖ := by simp
        _ ≤ ‖A‖ * 1 * (‖z‖ + 1) := by gcongr
        _ = ‖A‖ * (‖z‖ + 1) := by ring
    have hexp : Real.exp (A * (t : ℂ) * w).re ≤
        Real.exp (‖A‖ * (‖z‖ + 1)) := Real.exp_le_exp.mpr hre
    calc
      ‖(rvachevUp F t : ℂ)‖ * Real.exp (A * (t : ℂ) * w).re *
          (‖A‖ * ‖t‖) ≤
          ‖(rvachevUp F t : ℂ)‖ * Real.exp (‖A‖ * (‖z‖ + 1)) *
            (‖A‖ * 1) := by gcongr
      _ = K * ‖(rvachevUp F t : ℂ)‖ := by dsimp [K]; ring
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := G) (F' := G') (bound := bound) (s := Metric.ball z 1)
    (Metric.ball_mem_nhds z zero_lt_one)
    (Filter.Eventually.of_forall fun w => by
      apply Continuous.aestronglyMeasurable
      dsimp [G]
      fun_prop)
    hG_int hG'_meas
    (ae_of_all _ fun t w hw => hbound t w hw)
    hbound_int
    (ae_of_all _ fun t w _hw => hderiv t w)
  have hdifferentiable : DifferentiableAt ℂ (fun q => ∫ t : ℝ, G q t) z :=
    hd.2.differentiableAt
  have hfun : (fun q => ∫ t : ℝ, G q t) = rvachevFourier F := by
    funext q
    unfold rvachevFourier
    apply integral_congr_ae
    filter_upwards with t
    dsimp [G, A]
  rwa [hfun] at hdifferentiable

private lemma rvachevFourier_real_eq_fourier
    (F : BoundedFabius) (t : ℝ) :
    rvachevFourier F (t : ℂ) =
      𝓕 (fun x : ℝ => (rvachevUp F x : ℂ)) t := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold rvachevFourier
  apply integral_congr_ae
  filter_upwards with x
  simp only [smul_eq_mul]
  have hexp : -2 * Real.pi * Complex.I * (x : ℂ) * (t : ℂ) =
      ((-2 * Real.pi * x * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hexp]
  ring

/-- Fourier inversion for Rvachev's function. -/
theorem rvachev_fourier_inversion_analytic
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    (rvachevUp F x : ℂ) =
      ∫ t : ℝ, rvachevFourier F t *
        Complex.exp (2 * Real.pi * Complex.I * t * x) := by
  have hcont : Continuous (fun t : ℝ => (rvachevUp F t : ℂ)) :=
    (rvachevUp_complex_contDiff F hF).continuous
  have hcomp : HasCompactSupport (fun t : ℝ => (rvachevUp F t : ℂ)) :=
    rvachevUp_complex_hasCompactSupport F hF
  have hsmooth : ContDiff ℝ ∞ (fun t : ℝ => (rvachevUp F t : ℂ)) :=
    rvachevUp_complex_contDiff F hF
  let φ : 𝓢(ℝ, ℂ) := hcomp.toSchwartzMap hsmooth
  have hφcoe : (φ : ℝ → ℂ) = fun t : ℝ => (rvachevUp F t : ℂ) := rfl
  have hfourier_int : Integrable (𝓕 (φ : ℝ → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 φ).integrable
  have hup_int : Integrable (fun t : ℝ => (rvachevUp F t : ℂ)) := by
    rw [← hφcoe]
    exact φ.integrable
  have hup_fourier_int :
      Integrable (𝓕 (fun t : ℝ => (rvachevUp F t : ℂ))) := by
    rw [← hφcoe]
    exact hfourier_int
  have hinv := hcont.fourierInv_fourier_eq hup_int hup_fourier_int
  have hx := congrFun hinv x
  rw [Real.fourierInv_eq'] at hx
  rw [← hx]
  apply integral_congr_ae
  filter_upwards with t
  rw [← rvachevFourier_real_eq_fourier F t]
  simp only [smul_eq_mul]
  have hexp : ((2 * Real.pi * inner ℝ t x : ℝ) : ℂ) * Complex.I =
      2 * Real.pi * Complex.I * (t : ℂ) * (x : ℂ) := by
    rw [Real.inner_apply]
    push_cast
    ring
  rw [hexp]
  ring

private lemma rvachevUp_two_mul_add_one_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : 0 ≤ x) :
    rvachevUp F (2 * x + 1) = 0 := by
  rw [rvachevUp, if_neg (by linarith : ¬ 2 * x + 1 ≤ 0)]
  exact hF.zero_of_nonpos _ (by linarith)

private lemma rvachevUp_complex_hasDerivAt_on_unit
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => (rvachevUp F y : ℂ))
      ((-2 * rvachevUp F (2 * x - 1) : ℝ) : ℂ) x := by
  have h := rvachev_hasDerivAt F hF x
  rw [rvachevUp_two_mul_add_one_eq_zero F hF hx] at h
  convert! h.ofReal_comp using 1
  push_cast
  ring

private lemma complexGeneratingFunction_eq_affine_integral
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      2 * ∫ x in (0 : ℝ)..1,
        (rvachevUp F (2 * x - 1) : ℂ) * Complex.exp (z * x) := by
  let u : ℝ → ℂ := fun x => (rvachevUp F x : ℂ)
  let u' : ℝ → ℂ := fun x => ((-2 * rvachevUp F (2 * x - 1) : ℝ) : ℂ)
  let v : ℝ → ℂ := fun x => Complex.exp (z * x)
  let v' : ℝ → ℂ := fun x => z * Complex.exp (z * x)
  have hupcont : Continuous (rvachevUp F) := (rvachev_contDiff F hF).continuous
  have haffine : Continuous (fun x : ℝ => rvachevUp F (2 * x - 1)) := by
    exact hupcont.comp (by fun_prop)
  have hucont : Continuous u := by
    dsimp [u]
    exact Complex.continuous_ofReal.comp hupcont
  have hu'cont : Continuous u' := by
    dsimp [u']
    exact Complex.continuous_ofReal.comp (continuous_const.mul haffine)
  have hvcont : Continuous v := by
    dsimp [v]
    fun_prop
  have hv'cont : Continuous v' := by
    dsimp [v']
    fun_prop
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt u (u' x) x := by
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    exact rvachevUp_complex_hasDerivAt_on_unit F hF hx.1
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt v (v' x) x := by
    intro x hx
    dsimp [v, v']
    convert! (((hasDerivAt_id x).ofReal_comp.const_mul z).cexp) using 1
    simp [id]
    ring
  have hu'_int : IntervalIntegrable u' volume (0 : ℝ) 1 :=
    hu'cont.intervalIntegrable (μ := volume) 0 1
  have hv'_int : IntervalIntegrable v' volume (0 : ℝ) 1 :=
    hv'cont.intervalIntegrable (μ := volume) 0 1
  have hterm1 : IntervalIntegrable (fun x => u' x * v x) volume (0 : ℝ) 1 :=
    (hu'cont.mul hvcont).intervalIntegrable (μ := volume) 0 1
  have hterm2 : IntervalIntegrable (fun x => u x * v' x) volume (0 : ℝ) 1 :=
    (hucont.mul hv'cont).intervalIntegrable (μ := volume) 0 1
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub hu hv hu'_int hv'_int
  rw [intervalIntegral.integral_add hterm1 hterm2] at hibp
  have hfirst : (∫ x in (0 : ℝ)..1, u' x * v x) =
      (-2 : ℂ) * ∫ x in (0 : ℝ)..1,
        (rvachevUp F (2 * x - 1) : ℂ) * Complex.exp (z * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp [u', v]
    push_cast
    ring
  have hsecond : (∫ x in (0 : ℝ)..1, u x * v' x) =
      z * ∫ x in (0 : ℝ)..1,
        (rvachevUp F x : ℂ) * Complex.exp (z * x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp [u, v']
    ring
  rw [hfirst, hsecond] at hibp
  dsimp [u, v] at hibp
  rw [rvachevUp_zero F hF,
    rvachevUp_eq_zero_of_one_le F hF (by norm_num)] at hibp
  norm_num at hibp
  unfold complexGeneratingFunction
  linear_combination hibp

private lemma up_support_subset_Ioc (F : BoundedFabius) (hF : IsFabius F) :
    Function.support (rvachevUp F) ⊆ Ioc (-1 : ℝ) 1 := by
  intro x hx
  have hx' := support_rvachev_subset_Ioo F hF hx
  exact ⟨hx'.1, hx'.2.le⟩

/-- The half-moment generating function is the Fourier transform evaluated
at the corresponding imaginary argument. -/
theorem complexGeneratingFunction_eq_fourier_analytic
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    complexGeneratingFunction F z =
      Complex.exp (z / 2) *
        rvachevFourier F (Complex.I * z / (4 * Real.pi)) := by
  let q : ℝ → ℂ := fun t =>
    (rvachevUp F t : ℂ) * Complex.exp (z * t / 2)
  let p : ℝ → ℂ := fun t => Complex.exp (z / 2) * q t
  have hfourier :
      rvachevFourier F (Complex.I * z / (4 * Real.pi)) = ∫ t : ℝ, q t := by
    unfold rvachevFourier
    apply integral_congr_ae
    filter_upwards with t
    dsimp [q]
    congr 2
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hpi]
    rw [Complex.I_sq]
    ring
  have hp_support : Function.support p ⊆ Ioc (-1 : ℝ) 1 := by
    intro t ht
    apply up_support_subset_Ioc F hF
    intro hup
    apply ht
    simp [p, q, hup]
  have hrestrict :
      (∫ t in (-1 : ℝ)..1, p t) = ∫ t : ℝ, p t :=
    intervalIntegral.integral_eq_integral_of_support_subset hp_support
  have hpcomp :
      (∫ x in (0 : ℝ)..1, p (2 * x - 1)) =
        ∫ x in (0 : ℝ)..1,
          (rvachevUp F (2 * x - 1) : ℂ) * Complex.exp (z * x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp [p, q]
    have hexp : z / 2 + z * ((2 * x - 1 : ℝ) : ℂ) / 2 = z * (x : ℂ) := by
      push_cast
      ring
    calc
      Complex.exp (z / 2) *
          ((rvachevUp F (2 * x - 1) : ℂ) *
            Complex.exp (z * ((2 * x - 1 : ℝ) : ℂ) / 2)) =
          (rvachevUp F (2 * x - 1) : ℂ) *
            (Complex.exp (z / 2) *
              Complex.exp (z * ((2 * x - 1 : ℝ) : ℂ) / 2)) := by ring
      _ = (rvachevUp F (2 * x - 1) : ℂ) *
          Complex.exp (z / 2 + z * ((2 * x - 1 : ℝ) : ℂ) / 2) := by
            rw [Complex.exp_add]
      _ = (rvachevUp F (2 * x - 1) : ℂ) * Complex.exp (z * x) := by rw [hexp]
  have hsubst := intervalIntegral.smul_integral_comp_mul_add
    (f := p) (a := (0 : ℝ)) (b := 1) (2 : ℝ) (-1 : ℝ)
  have hinterval :
      (∫ t in (-1 : ℝ)..1, p t) =
        2 * ∫ x in (0 : ℝ)..1,
          (rvachevUp F (2 * x - 1) : ℂ) * Complex.exp (z * x) := by
    have hsubst' :
        (2 : ℝ) • (∫ x in (0 : ℝ)..1, p (2 * x - 1)) =
          ∫ t in (-1 : ℝ)..1, p t := by
      convert! hsubst using 1
      norm_num [sub_eq_add_neg]
    rw [hpcomp] at hsubst'
    convert hsubst'.symm using 1
    norm_num
  rw [complexGeneratingFunction_eq_affine_integral F hF z, hfourier]
  symm
  calc
    Complex.exp (z / 2) * ∫ t : ℝ, q t = ∫ t : ℝ, p t := by
      rw [integral_const_mul]
    _ = ∫ t in (-1 : ℝ)..1, p t := hrestrict.symm
    _ = 2 * ∫ x in (0 : ℝ)..1,
        (rvachevUp F (2 * x - 1) : ℂ) * Complex.exp (z * x) := hinterval

end

end Fabius

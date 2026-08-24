import IntegerPoints.IwaniecMozzochiEq115Fresnel
import IntegerPoints.IwaniecMozzochiReciprocalQuadraticBound
import IntegerPoints.SP3Tail
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The negative reciprocal-Bessel transform as a parameter ODE

For `r > 0`, write

```
  F(r) = integral_0^infinity e(-u^2 + r/u^2) du.
```

Formal differentiation and the reciprocal substitution `u = sqrt(r)/v`
give the coupled real-parameter ODE

```
  F'(r) = (2*pi*i/sqrt(r)) * conj(F(r)).
```

The half-Fresnel boundary value `A = (2i)^(-1/2)/2` satisfies
`conj(A) = i*A`.  The coupled ODE then forces that phase relation at every
positive `r`, after which it becomes the scalar equation

```
  F'(r) = -(2*pi/sqrt(r))*F(r).
```

The abstract ODE argument is proved completely below.  The subsequent
fixed-cutoff definitions prove locally uniform convergence of the partial
integrals and their derivatives by subtracting the negative Fresnel kernel.
This supplies the precise interface expected by Mathlib's
`hasDerivAt_of_tendstoLocallyUniformlyOn`.
-/

open Real Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace LeanProofs.IntegerPoints

namespace NegativeReciprocalODE

/-! ## The coupled ODE and its unique solution -/

/-- The singular real coefficient in the reciprocal-conjugate ODE. -/
noncomputable def odeCoeff (r : Real) : Real :=
  2 * Real.pi / Real.sqrt r

/-- The decaying scalar solution selected by the boundary value at zero. -/
noncomputable def decay (r : Real) : Real :=
  Real.exp (-4 * Real.pi * Real.sqrt r)

private noncomputable def growth (r : Real) : Real :=
  Real.exp (4 * Real.pi * Real.sqrt r)

private theorem decay_hasDerivAt {r : Real} (hr : 0 < r) :
    HasDerivAt decay (-odeCoeff r * decay r) r := by
  have hsqrt := Real.hasDerivAt_sqrt hr.ne'
  have hinner : HasDerivAt (fun x : Real => -4 * Real.pi * Real.sqrt x)
      (-4 * Real.pi * (1 / (2 * Real.sqrt r))) r :=
    hsqrt.const_mul (-4 * Real.pi)
  have hexp := hinner.exp
  apply hexp.congr_deriv
  unfold odeCoeff decay
  field_simp [Real.sqrt_ne_zero'.2 hr]
  ring

private theorem growth_hasDerivAt {r : Real} (hr : 0 < r) :
    HasDerivAt growth (odeCoeff r * growth r) r := by
  have hsqrt := Real.hasDerivAt_sqrt hr.ne'
  have hinner : HasDerivAt (fun x : Real => 4 * Real.pi * Real.sqrt x)
      (4 * Real.pi * (1 / (2 * Real.sqrt r))) r :=
    hsqrt.const_mul (4 * Real.pi)
  have hexp := hinner.exp
  apply hexp.congr_deriv
  unfold odeCoeff growth
  field_simp [Real.sqrt_ne_zero'.2 hr]
  ring

private theorem conj_hasDerivAt
    {F : Real -> Complex} {F' : Complex} {r : Real}
    (hF : HasDerivAt F F' r) :
    HasDerivAt (fun x => starRingEnd Complex (F x))
      (starRingEnd Complex F') r := by
  have hconst : HasDerivAt
      (fun _ : Real => (Complex.conjCLE : Complex →L[Real] Complex))
        (0 : Complex →L[Real] Complex) r :=
    hasDerivAt_const r _
  have hconj := hconst.clm_apply hF
  have hderiv : (Complex.conjCLE : Complex →L[Real] Complex) F' =
      starRingEnd Complex F' := by
    change star F' = starRingEnd Complex F'
    rw [starRingEnd_apply]
  apply (hconj.congr_deriv ?_).congr_of_eventuallyEq
  · exact Eventually.of_forall fun x => by
      change starRingEnd Complex (F x) = star (F x)
      rw [starRingEnd_apply]
  · simpa only [zero_apply, zero_add] using hderiv

private theorem coupled_defect_hasDerivAt
    {F : Real -> Complex} {r : Real} (hr : 0 < r)
    (hF : HasDerivAt F
      (((odeCoeff r : Real) : Complex) * Complex.I *
        starRingEnd Complex (F r)) r) :
    HasDerivAt
      (fun x => starRingEnd Complex (F x) - Complex.I * F x)
      (((odeCoeff r : Real) : Complex) *
        (starRingEnd Complex (F r) - Complex.I * F r)) r := by
  have hconj := conj_hasDerivAt hF
  have hI := hF.const_mul Complex.I
  apply (hconj.sub hI).congr_deriv
  have hstarI : star Complex.I = -Complex.I := by
    rw [Complex.star_def, Complex.conj_I]
  have hstarCoeff : star (((odeCoeff r : Real) : Complex)) =
      ((odeCoeff r : Real) : Complex) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  simp only [starRingEnd_apply, star_mul, star_star, hstarI, hstarCoeff]
  ring_nf
  rw [Complex.I_sq]
  ring

private theorem coupled_defect_zero
    {F : Real -> Complex} {A : Complex}
    (hF : forall r : Real, 0 < r -> HasDerivAt F
      (((odeCoeff r : Real) : Complex) * Complex.I *
        starRingEnd Complex (F r)) r)
    (hboundary : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds A))
    (hphaseA : starRingEnd Complex A = Complex.I * A) :
    forall r : Real, 0 < r ->
      starRingEnd Complex (F r) = Complex.I * F r := by
  let D : Real -> Complex := fun r =>
    starRingEnd Complex (F r) - Complex.I * F r
  let H : Real -> Complex := fun r => ((decay r : Real) : Complex) * D r
  have hD : forall r : Real, 0 < r ->
      HasDerivAt D (((odeCoeff r : Real) : Complex) * D r) r := by
    intro r hr
    simpa only [D] using coupled_defect_hasDerivAt hr (hF r hr)
  have hH : forall r : Real, 0 < r -> HasDerivAt H 0 r := by
    intro r hr
    have hdecay := (decay_hasDerivAt hr).ofReal_comp
    have hprod := hdecay.mul (hD r hr)
    apply hprod.congr_deriv
    push_cast
    ring
  have hHdiff : DifferentiableOn Real H (Ioi 0) := by
    intro r hr
    exact (hH r hr).differentiableAt.differentiableWithinAt
  have hHderiv : (Ioi (0 : Real)).EqOn (deriv H) 0 := by
    intro r hr
    exact (hH r hr).deriv
  have hHconst : forall {r s : Real}, 0 < r -> 0 < s -> H r = H s := by
    intro r s hr hs
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      hHdiff hHderiv hr hs
  have hconjBoundary : Tendsto (fun r => starRingEnd Complex (F r))
      (nhdsWithin 0 (Ioi 0)) (nhds (starRingEnd Complex A)) :=
    (Complex.continuous_conj.tendsto A).comp hboundary
  have hDBoundary : Tendsto D (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hphaseBoundary : Tendsto (fun r : Real => Complex.I * F r)
        (nhdsWithin 0 (Ioi 0)) (nhds (Complex.I * A)) :=
      (tendsto_const_nhds : Tendsto (fun _ : Real => Complex.I)
        (nhdsWithin 0 (Ioi 0)) (nhds Complex.I)).mul hboundary
    have hsub := hconjBoundary.sub hphaseBoundary
    simpa only [D, hphaseA, sub_self] using hsub
  have hdecayBoundary : Tendsto (fun r : Real => ((decay r : Real) : Complex))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hcont : Continuous (fun r : Real => ((decay r : Real) : Complex)) := by
      unfold decay
      fun_prop
    convert hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num [decay]
  have hHBoundary : Tendsto H (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa only [H, one_mul] using hdecayBoundary.mul hDBoundary
  letI : NeBot (nhdsWithin (0 : Real) (Ioi 0)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  intro r hr
  have hevent : H =ᶠ[nhdsWithin (0 : Real) (Ioi 0)] fun _ => H r := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hHconst hs hr
  have hconstant : Tendsto H (nhdsWithin (0 : Real) (Ioi 0)) (nhds (H r)) :=
    tendsto_const_nhds.congr' hevent.symm
  have hHr : H r = 0 := tendsto_nhds_unique hconstant hHBoundary
  have hdecayPos : 0 < decay r := by
    unfold decay
    positivity
  have hDzero : D r = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left
      (Complex.ofReal_ne_zero.mpr hdecayPos.ne')
    simpa only [H] using hHr
  dsimp only [D] at hDzero
  exact sub_eq_zero.mp hDzero

/-- A solution of the reciprocal-conjugate ODE with the Fresnel phase at zero
is necessarily the exponentially decaying branch. -/
theorem coupled_ode_unique
    {F : Real -> Complex} {A : Complex}
    (hF : forall r : Real, 0 < r -> HasDerivAt F
      (((odeCoeff r : Real) : Complex) * Complex.I *
        starRingEnd Complex (F r)) r)
    (hboundary : Tendsto F (nhdsWithin 0 (Ioi 0)) (nhds A))
    (hphaseA : starRingEnd Complex A = Complex.I * A) :
    forall r : Real, 0 < r ->
      F r = A * ((decay r : Real) : Complex) := by
  have hphase := coupled_defect_zero hF hboundary hphaseA
  let G : Real -> Complex := fun r => ((growth r : Real) : Complex) * F r
  have hG : forall r : Real, 0 < r -> HasDerivAt G 0 r := by
    intro r hr
    have hgrowth := (growth_hasDerivAt hr).ofReal_comp
    have hscalar : HasDerivAt F
        (-((odeCoeff r : Real) : Complex) * F r) r := by
      convert hF r hr using 1
      rw [hphase r hr]
      push_cast
      calc
        -((odeCoeff r : Real) : Complex) * F r =
            ((odeCoeff r : Real) : Complex) * (Complex.I ^ 2) * F r := by
          rw [Complex.I_sq]
          ring
        _ = ((odeCoeff r : Real) : Complex) * Complex.I *
            (Complex.I * F r) := by ring
    have hprod := hgrowth.mul hscalar
    apply hprod.congr_deriv
    push_cast
    ring
  have hGdiff : DifferentiableOn Real G (Ioi 0) := by
    intro r hr
    exact (hG r hr).differentiableAt.differentiableWithinAt
  have hGderiv : (Ioi (0 : Real)).EqOn (deriv G) 0 := by
    intro r hr
    exact (hG r hr).deriv
  have hGconst : forall {r s : Real}, 0 < r -> 0 < s -> G r = G s := by
    intro r s hr hs
    exact isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
      hGdiff hGderiv hr hs
  have hgrowthBoundary : Tendsto (fun r : Real => ((growth r : Real) : Complex))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    have hcont : Continuous (fun r : Real => ((growth r : Real) : Complex)) := by
      unfold growth
      fun_prop
    convert hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1
    norm_num [growth]
  have hGBoundary : Tendsto G (nhdsWithin 0 (Ioi 0)) (nhds A) := by
    simpa only [G, one_mul] using hgrowthBoundary.mul hboundary
  letI : NeBot (nhdsWithin (0 : Real) (Ioi 0)) :=
    mem_closure_iff_nhdsWithin_neBot.mp (by simp)
  intro r hr
  have hevent : G =ᶠ[nhdsWithin (0 : Real) (Ioi 0)] fun _ => G r := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hGconst hs hr
  have hconstant : Tendsto G (nhdsWithin (0 : Real) (Ioi 0)) (nhds (G r)) :=
    tendsto_const_nhds.congr' hevent.symm
  have hGr : G r = A := tendsto_nhds_unique hconstant hGBoundary
  have hgrowthPos : 0 < growth r := by
    unfold growth
    positivity
  have hsolve : F r = (((growth r : Real) : Complex)⁻¹) * A := by
    dsimp only [G] at hGr
    have hg0 : ((growth r : Real) : Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hgrowthPos.ne'
    calc
      F r = 1 * F r := by rw [one_mul]
      _ = ((((growth r : Real) : Complex)⁻¹) *
          ((growth r : Real) : Complex)) * F r := by
        rw [inv_mul_cancel₀ hg0]
      _ = (((growth r : Real) : Complex)⁻¹) *
          (((growth r : Real) : Complex) * F r) := by ring
      _ = (((growth r : Real) : Complex)⁻¹) * A := by rw [hGr]
  rw [hsolve]
  unfold growth decay
  push_cast
  rw [← Complex.exp_neg
    (4 * (Real.pi : Complex) * (Real.sqrt r : Complex))]
  ring

private theorem e_one_fourth : e ((1 : Real) / 4) = Complex.I := by
  unfold e
  have harg :
      (2 * Real.pi * Complex.I * (((1 : Real) / 4 : Real) : Complex)) =
        (Real.pi : Complex) / 2 * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_pi_div_two_mul_I]

/-- The principal half-Fresnel constant lies on the phase line preserved by
the reciprocal-conjugate ODE. -/
theorem halfFresnel_phase :
    starRingEnd Complex
        (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) =
      Complex.I *
        (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) := by
  rw [eq115_two_mul_I_cpow_neg_half]
  have hconj :
      starRingEnd Complex (e (-(1 : Real) / 8)) = e ((1 : Real) / 8) := by
    rw [← KL.e_neg]
    congr 1
    ring
  simp only [map_div₀, Complex.conj_ofReal, map_ofNat, hconj]
  calc
    e ((1 : Real) / 8) / ((Real.sqrt 2 : Real) : Complex) / 2 =
        (e ((1 : Real) / 4) * e (-(1 : Real) / 8)) /
          ((Real.sqrt 2 : Real) : Complex) / 2 := by
      rw [← KL.e_add]
      congr 3
      ring
    _ = Complex.I *
        (e (-(1 : Real) / 8) / ((Real.sqrt 2 : Real) : Complex) / 2) := by
      rw [e_one_fourth]
      ring

/-! ## Fixed-cutoff transform and its formal derivative -/

/-- The negative reciprocal-quadratic oscilland. -/
noncomputable def oscilland (r u : Real) : Complex :=
  e (-(u ^ 2) + r / u ^ 2)

/-- A two-sided finite truncation, convenient for parameter differentiation. -/
noncomputable def partialIntegral (eta U r : Real) : Complex :=
  ∫ u in eta..U, oscilland r u

/-- The pointwise parameter derivative of the oscilland. -/
noncomputable def parameterDeriv (r u : Real) : Complex :=
  (2 * Real.pi * Complex.I / (u : Complex) ^ 2) * oscilland r u

private theorem oscilland_hasDerivAt_parameter {r u : Real} (hu : u ≠ 0) :
    HasDerivAt (fun s => oscilland s u) (parameterDeriv r u) r := by
  have hphase : HasDerivAt (fun s : Real => -(u ^ 2) + s / u ^ 2)
      (1 / u ^ 2) r := by
    exact ((hasDerivAt_id r).div_const (u ^ 2)).const_add (-(u ^ 2))
  unfold parameterDeriv oscilland
  convert PS.hasDerivAt_e_comp hphase using 1
  push_cast
  field_simp [hu]

private theorem measurable_oscilland (r : Real) : Measurable (oscilland r) := by
  unfold oscilland e
  fun_prop

private theorem measurable_parameterDeriv (r : Real) :
    Measurable (parameterDeriv r) := by
  unfold parameterDeriv
  exact (by fun_prop : Measurable (fun u : Real =>
    2 * Real.pi * Complex.I / (u : Complex) ^ 2)).mul
      (measurable_oscilland r)

private theorem intervalIntegrable_oscilland (eta U r : Real) :
    IntervalIntegrable (oscilland r) volume eta U := by
  apply SP.intervalIntegrable_of_bounded_on_complex (measurable_oscilland r)
  intro u _
  unfold oscilland
  rw [norm_e]

private theorem norm_parameterDeriv {r u : Real} (hu : 0 < u) :
    norm (parameterDeriv r u) = 2 * Real.pi / u ^ 2 := by
  unfold parameterDeriv oscilland
  rw [norm_mul, norm_div, PS.norm_two_pi_I, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu, norm_e, mul_one]

/-- Differentiation under the integral sign is unconditional for every
two-sided finite truncation bounded away from the pole. -/
theorem partialIntegral_hasDerivAt
    {eta U r : Real} (heta : 0 < eta) (hetaU : eta <= U) :
    HasDerivAt (partialIntegral eta U)
      (∫ u in eta..U, parameterDeriv r u) r := by
  let M : Real := 2 * Real.pi / eta ^ 2
  have hFmeas : ∀ᶠ s in nhds r,
      AEStronglyMeasurable (oscilland s) (volume.restrict (Set.uIoc eta U)) :=
    Eventually.of_forall fun s => (measurable_oscilland s).aestronglyMeasurable
  have hFint : IntervalIntegrable (oscilland r) volume eta U :=
    intervalIntegrable_oscilland eta U r
  have hF'meas : AEStronglyMeasurable (parameterDeriv r)
      (volume.restrict (Set.uIoc eta U)) :=
    (measurable_parameterDeriv r).aestronglyMeasurable
  have hbound : ∀ᵐ u ∂volume, u ∈ Set.uIoc eta U ->
      ∀ s ∈ (Set.univ : Set Real), norm (parameterDeriv s u) <= M := by
    exact Eventually.of_forall fun u hu s _ => by
      rw [Set.uIoc_of_le hetaU] at hu
      have hu0 : 0 < u := heta.trans hu.1
      rw [norm_parameterDeriv hu0]
      dsimp only [M]
      have hsquares : eta ^ 2 <= u ^ 2 :=
        pow_le_pow_left₀ heta.le hu.1.le 2
      exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos heta)
        hsquares
  have hM : IntervalIntegrable (fun _ : Real => M) volume eta U :=
    continuous_const.intervalIntegrable eta U
  have hdiff : ∀ᵐ u ∂volume, u ∈ Set.uIoc eta U ->
      ∀ s ∈ (Set.univ : Set Real),
        HasDerivAt (fun x => oscilland x u) (parameterDeriv s u) s := by
    exact Eventually.of_forall fun u hu s _ => by
      rw [Set.uIoc_of_le hetaU] at hu
      exact oscilland_hasDerivAt_parameter (heta.trans hu.1).ne'
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s u => oscilland s u)
    (F' := fun s u => parameterDeriv s u)
    (bound := fun _ => M) (s := Set.univ)
    (a := eta) (b := U) (x₀ := r)
    univ_mem hFmeas hFint hF'meas hbound hM hdiff
  exact hmain.2

/-! ## Reciprocal symmetry of the parameter derivative -/

private def reciprocalMap (s v : Real) : Real := s / v

private theorem reciprocalMap_hasDerivAt {s v : Real} (hv : v ≠ 0) :
    HasDerivAt (reciprocalMap s) (-s / v ^ 2) v := by
  unfold reciprocalMap
  have h := (hasDerivAt_const v s).div (hasDerivAt_id' v) hv
  apply h.congr_deriv
  field_simp [hv]
  ring

private theorem oscilland_reciprocal {r v : Real} (hr : 0 < r) (hv : 0 < v) :
    oscilland r (reciprocalMap (Real.sqrt r) v) =
      starRingEnd Complex (oscilland r v) := by
  have hs2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hphase :
      -(reciprocalMap (Real.sqrt r) v ^ 2) +
          r / reciprocalMap (Real.sqrt r) v ^ 2 =
        -(-(v ^ 2) + r / v ^ 2) := by
    have hs4 : Real.sqrt r ^ 4 = r ^ 2 := by
      calc
        Real.sqrt r ^ 4 = (Real.sqrt r ^ 2) ^ 2 := by ring
        _ = r ^ 2 := by rw [hs2]
    unfold reciprocalMap
    field_simp [hr.ne', hv.ne', Real.sqrt_ne_zero'.2 hr]
    rw [hs2, hs4]
    ring
  unfold oscilland
  rw [hphase, KL.e_neg, starRingEnd_apply]

private noncomputable def weightedOscilland (r u : Real) : Complex :=
  (((1 / u ^ 2 : Real) : Complex) * oscilland r u)

private theorem weightedOscilland_contDiffOn (r : Real) :
    ContDiffOn Real 1 (weightedOscilland r) (Ioi 0) := by
  unfold weightedOscilland oscilland e
  have hpow : ContDiffOn Real 1 (fun u : Real => u ^ 2) (Ioi 0) :=
    contDiffOn_id.pow 2
  have hinv : ContDiffOn Real 1 (fun u : Real => (u ^ 2)⁻¹) (Ioi 0) :=
    hpow.inv (by
      intro u hu
      exact pow_ne_zero 2 (ne_of_gt hu))
  have hweight : ContDiffOn Real 1 (fun u : Real => 1 / u ^ 2) (Ioi 0) := by
    simpa only [one_div] using hinv
  have hweightComplex : ContDiffOn Real 1
      (fun u : Real => ((1 / u ^ 2 : Real) : Complex)) (Ioi 0) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hweight
  have hphase : ContDiffOn Real 1
      (fun u : Real => -(u ^ 2) + r / u ^ 2) (Ioi 0) := by
    simpa only [div_eq_mul_inv] using
      (hpow.neg.add (contDiffOn_const.mul hinv))
  have harg : ContDiffOn Real 1 (fun u : Real =>
      2 * Real.pi * Complex.I *
        (((-(u ^ 2) + r / u ^ 2 : Real)) : Complex)) (Ioi 0) :=
    contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hphase)
  exact hweightComplex.mul (Complex.contDiff_exp.comp_contDiffOn harg)

private theorem reciprocal_weighted_integrand
    {r v : Real} (hr : 0 < r) (hv : 0 < v) :
    (-Real.sqrt r / v ^ 2) •
        weightedOscilland r (reciprocalMap (Real.sqrt r) v) =
      (((-1 / Real.sqrt r : Real) : Complex) *
        starRingEnd Complex (oscilland r v)) := by
  rw [Complex.real_smul]
  unfold weightedOscilland
  rw [oscilland_reciprocal hr hv]
  have hcoeff :
      (-Real.sqrt r / v ^ 2) *
          (1 / reciprocalMap (Real.sqrt r) v ^ 2) =
        -1 / Real.sqrt r := by
    unfold reciprocalMap
    field_simp [hv.ne', Real.sqrt_ne_zero'.2 hr]
  calc
    _ = ((((-Real.sqrt r / v ^ 2) *
          (1 / reciprocalMap (Real.sqrt r) v ^ 2) : Real) : Complex) *
        starRingEnd Complex (oscilland r v)) := by
      push_cast
      ring
    _ = _ := by rw [hcoeff]

/-- On finite positive intervals, the weighted derivative integral is exactly
the conjugate of an unweighted integral over the reciprocal interval. -/
theorem weightedPartial_reciprocal
    {r eta U : Real} (hr : 0 < r) (heta : 0 < eta) (hetaU : eta <= U) :
    (∫ u in eta..U, weightedOscilland r u) =
      (((1 / Real.sqrt r : Real) : Complex) *
        starRingEnd Complex
          (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
            oscilland r v)) := by
  have hU : 0 < U := heta.trans_le hetaU
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hab : Real.sqrt r / U <= Real.sqrt r / eta :=
    div_le_div_of_nonneg_left hs.le heta hetaU
  have ha : 0 < Real.sqrt r / U := div_pos hs hU
  have hb : 0 < Real.sqrt r / eta := div_pos hs heta
  let rho : Real -> Real := reciprocalMap (Real.sqrt r)
  let rho' : Real -> Real := fun v => -Real.sqrt r / v ^ 2
  have hrho : ∀ v ∈ Set.uIcc (Real.sqrt r / U) (Real.sqrt r / eta),
      HasDerivAt rho (rho' v) v := by
    intro v hv
    rw [Set.uIcc_of_le hab] at hv
    exact reciprocalMap_hasDerivAt (ha.trans_le hv.1).ne'
  have hrho' : ContinuousOn rho'
      (Set.uIcc (Real.sqrt r / U) (Real.sqrt r / eta)) := by
    unfold rho'
    rw [Set.uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_const (continuous_id.pow 2).continuousOn
    intro v hv
    exact pow_ne_zero 2 (ha.trans_le hv.1).ne'
  have himage : rho '' Set.uIcc (Real.sqrt r / U) (Real.sqrt r / eta) ⊆
      Ioi 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    rw [Set.uIcc_of_le hab] at hv
    exact div_pos hs (ha.trans_le hv.1)
  have hg : ContinuousOn (weightedOscilland r)
      (rho '' Set.uIcc (Real.sqrt r / U) (Real.sqrt r / eta)) :=
    (weightedOscilland_contDiffOn r).continuousOn.mono himage
  have hsubst := intervalIntegral.integral_deriv_smul_comp'
    (a := Real.sqrt r / U) (b := Real.sqrt r / eta)
    (f := rho) (f' := rho') (g := weightedOscilland r)
    hrho hrho' hg
  have hrhoU : rho (Real.sqrt r / U) = U := by
    unfold rho reciprocalMap
    field_simp [hr.ne', hU.ne', Real.sqrt_ne_zero'.2 hr]
  have hrhoEta : rho (Real.sqrt r / eta) = eta := by
    unfold rho reciprocalMap
    field_simp [hr.ne', heta.ne', Real.sqrt_ne_zero'.2 hr]
  have hleft :
      (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
        rho' v • weightedOscilland r (rho v)) =
      (((-1 / Real.sqrt r : Real) : Complex) *
        starRingEnd Complex
          (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
            oscilland r v)) := by
    calc
      (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
          rho' v • weightedOscilland r (rho v)) =
          ∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
            (((-1 / Real.sqrt r : Real) : Complex) *
              starRingEnd Complex (oscilland r v)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [Set.uIcc_of_le hab] at hv
        exact reciprocal_weighted_integrand hr (ha.trans_le hv.1)
      _ = (((-1 / Real.sqrt r : Real) : Complex) *
          (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
            starRingEnd Complex (oscilland r v))) := by
        rw [intervalIntegral.integral_const_mul]
      _ = (((-1 / Real.sqrt r : Real) : Complex) *
          starRingEnd Complex
            (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
              oscilland r v)) := by
        rw [intervalIntegral.intervalIntegral_conj]
  simp only [Function.comp_apply] at hsubst
  rw [hrhoU, hrhoEta] at hsubst
  have hnegative :
      (((-1 / Real.sqrt r : Real) : Complex) *
          starRingEnd Complex
            (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
              oscilland r v)) =
        -(∫ u in eta..U, weightedOscilland r u) := by
    calc
      (((-1 / Real.sqrt r : Real) : Complex) *
          starRingEnd Complex
            (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
              oscilland r v)) =
          ∫ u in U..eta, weightedOscilland r u :=
        hleft.symm.trans hsubst
      _ = -(∫ u in eta..U, weightedOscilland r u) :=
        intervalIntegral.integral_symm eta U
  have hneg :
      -((((1 / Real.sqrt r : Real) : Complex) *
          starRingEnd Complex
            (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
              oscilland r v))) =
        -(∫ u in eta..U, weightedOscilland r u) := by
    calc
      -((((1 / Real.sqrt r : Real) : Complex) *
          starRingEnd Complex
            (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
              oscilland r v))) =
          (((-1 / Real.sqrt r : Real) : Complex) *
            starRingEnd Complex
              (∫ v in (Real.sqrt r / U)..(Real.sqrt r / eta),
                oscilland r v)) := by
        push_cast
        ring
      _ = -(∫ u in eta..U, weightedOscilland r u) := hnegative
  exact (neg_inj.mp hneg).symm

/-! ## Existence of the improper integral by an integrable perturbation -/

/-- The finite integral from the actual endpoint `0`.  The integrand is
bounded there because Lean's division is total; the value at the singleton
`u = 0` is immaterial. -/
noncomputable def zeroPartial (U r : Real) : Complex :=
  ∫ u in (0 : Real)..U, oscilland r u

/-- Subtracting the negative Fresnel oscilland leaves an absolutely integrable
tail: at infinity its norm is `O(|r|/u^2)`. -/
noncomputable def fresnelPerturbation (r u : Real) : Complex :=
  oscilland r u - e (-(u ^ 2))

private theorem measurable_fresnelPerturbation (r : Real) :
    Measurable (fresnelPerturbation r) := by
  unfold fresnelPerturbation
  exact (measurable_oscilland r).sub
    (GK32.continuous_e_comp (by fun_prop)).measurable

private theorem oscilland_eq_fresnel_mul (r u : Real) :
    oscilland r u = e (-(u ^ 2)) * e (r / u ^ 2) := by
  unfold oscilland
  rw [KL.e_add]

private theorem norm_fresnelPerturbation_le (r u : Real) :
    norm (fresnelPerturbation r u) <= 2 * Real.pi * |r / u ^ 2| := by
  unfold fresnelPerturbation
  rw [oscilland_eq_fresnel_mul]
  calc
    norm (e (-(u ^ 2)) * e (r / u ^ 2) - e (-(u ^ 2))) =
        norm (e (-(u ^ 2)) * (e (r / u ^ 2) - 1)) := by ring
    _ = norm (e (r / u ^ 2) - 1) := by
      rw [norm_mul, norm_e, one_mul]
    _ <= 2 * Real.pi * |r / u ^ 2| := SP.norm_e_sub_one_le _

private theorem norm_fresnelPerturbation_le_two (r u : Real) :
    norm (fresnelPerturbation r u) <= 2 := by
  unfold fresnelPerturbation
  calc
    norm (oscilland r u - e (-(u ^ 2))) <=
        norm (oscilland r u) + norm (e (-(u ^ 2))) := norm_sub_le _ _
    _ = 2 := by
      unfold oscilland
      rw [norm_e, norm_e]
      norm_num

private theorem intervalIntegrable_fresnelPerturbation (r p q : Real) :
    IntervalIntegrable (fresnelPerturbation r) volume p q := by
  apply SP.intervalIntegrable_of_bounded_on_complex
    (measurable_fresnelPerturbation r) (C := 2)
  intro u _
  exact norm_fresnelPerturbation_le_two r u

/-- The Fresnel perturbation is Bochner integrable on the whole positive ray.
Near zero boundedness suffices; past `1`, the bound is a constant multiple of
`u^(-2)`. -/
theorem integrableOn_fresnelPerturbation_Ioi (r : Real) :
    IntegrableOn (fresnelPerturbation r) (Ioi (0 : Real)) := by
  have hnear : IntegrableOn (fresnelPerturbation r) (Ioc (0 : Real) 1) := by
    refine Measure.integrableOn_of_bounded (M := 2) measure_Ioc_lt_top.ne
      (measurable_fresnelPerturbation r).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2
      (Eventually.of_forall fun u _ => norm_fresnelPerturbation_le_two r u)
  let C : Real := 2 * Real.pi * |r|
  have hmajor : IntegrableOn (fun u : Real => C * u ^ (-(2 : Real)))
      (Ioi (1 : Real)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(2 : Real)) (by norm_num)
      (by norm_num)).const_mul C
  have htail : IntegrableOn (fresnelPerturbation r) (Ioi (1 : Real)) := by
    refine hmajor.mono'
      (measurable_fresnelPerturbation r).aestronglyMeasurable.restrict ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun u hu => ?_)
    have hu0 : 0 < u := zero_lt_one.trans hu
    calc
      norm (fresnelPerturbation r u) <= 2 * Real.pi * |r / u ^ 2| :=
        norm_fresnelPerturbation_le r u
      _ = C * u ^ (-(2 : Real)) := by
        dsimp only [C]
        rw [abs_div, abs_pow, abs_of_pos hu0, Real.rpow_neg hu0.le,
          Real.rpow_two, div_eq_mul_inv]
        ring
  have hunion := hnear.union htail
  have hsets : Ioc (0 : Real) 1 ∪ Ioi (1 : Real) = Ioi (0 : Real) := by
    ext u
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨hu0, -⟩ | hu1) <;> linarith
    · intro hu0
      by_cases hu : u <= 1
      · exact Or.inl ⟨hu0, hu⟩
      · exact Or.inr (lt_of_not_ge hu)
  rwa [hsets] at hunion

/-- The absolutely convergent tail of the Fresnel perturbation above `U`. -/
noncomputable def perturbationTail (r U : Real) : Complex :=
  ∫ u in Ioi U, fresnelPerturbation r u

private theorem integral_Ioi_rpow_neg_two (C U : Real) (hU : 0 < U) :
    (∫ u in Ioi U, C * u ^ (-(2 : Real))) = C / U := by
  rw [MeasureTheory.integral_const_mul,
    integral_Ioi_rpow_of_lt (a := -(2 : Real)) (by norm_num) hU]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- Quantitative absolute convergence of the perturbation at infinity. -/
theorem norm_perturbationTail_le {r U : Real} (hU : 0 < U) :
    norm (perturbationTail r U) <= 2 * Real.pi * |r| / U := by
  let C : Real := 2 * Real.pi * |r|
  have hmajor : IntegrableOn (fun u : Real => C * u ^ (-(2 : Real)))
      (Ioi U) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(2 : Real)) (by norm_num) hU).const_mul C
  unfold perturbationTail
  calc
    norm (∫ u in Ioi U, fresnelPerturbation r u) <=
        ∫ u in Ioi U, C * u ^ (-(2 : Real)) := by
      apply MeasureTheory.norm_integral_le_of_norm_le hmajor
      refine (ae_restrict_iff' measurableSet_Ioi).2
        (Eventually.of_forall fun u hu => ?_)
      have hu0 : 0 < u := hU.trans hu
      calc
        norm (fresnelPerturbation r u) <= 2 * Real.pi * |r / u ^ 2| :=
          norm_fresnelPerturbation_le r u
        _ = C * u ^ (-(2 : Real)) := by
          dsimp only [C]
          rw [abs_div, abs_pow, abs_of_pos hu0, Real.rpow_neg hu0.le,
            Real.rpow_two, div_eq_mul_inv]
          ring
    _ = 2 * Real.pi * |r| / U := by
      exact integral_Ioi_rpow_neg_two C U hU

/-- Splitting the absolutely convergent perturbation at a positive finite
endpoint. -/
private theorem perturbation_Ioi_split {r U : Real} (hU : 0 < U) :
    (∫ u in Ioi (0 : Real), fresnelPerturbation r u) =
      (∫ u in (0 : Real)..U, fresnelPerturbation r u) +
        perturbationTail r U := by
  have hwhole := integrableOn_fresnelPerturbation_Ioi r
  have hIoc : IntegrableOn (fresnelPerturbation r) (Ioc (0 : Real) U) :=
    hwhole.mono_set Ioc_subset_Ioi_self
  have htail : IntegrableOn (fresnelPerturbation r) (Ioi U) :=
    hwhole.mono_set (Ioi_subset_Ioi hU.le)
  have hdisj : Disjoint (Ioc (0 : Real) U) (Ioi U) := by
    exact Set.disjoint_left.2 fun u hu h'u => (not_lt_of_ge hu.2) h'u
  have hunion : Ioi (0 : Real) = Ioc (0 : Real) U ∪ Ioi U := by
    ext u
    constructor
    · intro hu
      by_cases huU : u <= U
      · exact Or.inl ⟨hu, huU⟩
      · exact Or.inr (lt_of_not_ge huU)
    · rintro (hu | hu)
      · exact hu.1
      · exact hU.trans hu
  have hsplit := setIntegral_union hdisj measurableSet_Ioi hIoc htail
  rw [← hunion] at hsplit
  rw [intervalIntegral.integral_of_le hU.le]
  unfold perturbationTail
  exact hsplit

private theorem norm_oscilland_interval_zero_le {r eta : Real}
    (heta : 0 <= eta) :
    norm (∫ u in (0 : Real)..eta, oscilland r u) <= eta := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : Real)) (b := eta) (C := 1)
    (f := oscilland r) (fun u _ => by unfold oscilland; rw [norm_e])
  simpa only [one_mul, abs_of_nonneg heta, sub_zero] using h

/-- The canonical pointwise improper integral, defined as the known Fresnel
constant plus an absolutely convergent perturbation. -/
noncomputable def improperLimit (r : Real) : Complex :=
  (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) +
    ∫ u in Ioi (0 : Real), fresnelPerturbation r u

private theorem zeroPartial_decomposition (U r : Real) :
    zeroPartial U r = eq115HalfFresnelIntegral U +
      ∫ u in (0 : Real)..U, fresnelPerturbation r u := by
  unfold zeroPartial eq115HalfFresnelIntegral
  rw [← intervalIntegral.integral_add
    ((GK32.continuous_e_comp (by fun_prop)).intervalIntegrable 0 U)
    (intervalIntegrable_fresnelPerturbation r 0 U)]
  apply intervalIntegral.integral_congr
  intro u _
  unfold fresnelPerturbation
  ring

/-- For every real parameter, the actual finite integrals from `0` converge.
Thus existence of the strict-negative improper transform is unconditional. -/
theorem tendsto_zeroPartial (r : Real) :
    Tendsto (fun U : Real => zeroPartial U r) atTop (nhds (improperLimit r)) := by
  have hperturb := intervalIntegral_tendsto_integral_Ioi (0 : Real)
    (integrableOn_fresnelPerturbation_Ioi r) tendsto_id
  have hsum := iwaniecMozzochi_eq115_halfFresnel.add hperturb
  unfold improperLimit
  apply hsum.congr'
  exact Eventually.of_forall fun U => (zeroPartial_decomposition U r).symm

/-! ## Canonical cutoff sequences and the local-uniform limit interface -/

private def cutoff (n : Nat) : Real := (n + 1 : Nat)

private theorem cutoff_pos (n : Nat) : 0 < cutoff n := by
  unfold cutoff
  positivity

private theorem one_le_cutoff (n : Nat) : 1 <= cutoff n := by
  unfold cutoff
  exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

private theorem cutoff_inv_le (n : Nat) : (cutoff n)⁻¹ <= cutoff n :=
  ((inv_le_one₀ (cutoff_pos n)).mpr (one_le_cutoff n)).trans
    (one_le_cutoff n)

private theorem tendsto_cutoff_atTop : Tendsto cutoff atTop atTop := by
  change Tendsto (fun n : Nat => ((n + 1 : Nat) : Real)) atTop atTop
  simpa only [Nat.cast_add, Nat.cast_one] using
    (tendsto_atTop_add_const_right atTop (1 : Real)
      tendsto_natCast_atTop_atTop)

private theorem tendsto_cutoff_inv_zero :
    Tendsto (fun n : Nat => (cutoff n)⁻¹) atTop (nhds 0) :=
  tendsto_inv_atTop_zero.comp tendsto_cutoff_atTop

/-- The standard two-sided truncation `1/(n+1) <= u <= n+1`. -/
noncomputable def standardPartial (n : Nat) (r : Real) : Complex :=
  partialIntegral (cutoff n)⁻¹ (cutoff n) r

/-- The derivative of `standardPartial n`, still written as a finite interval
integral. -/
noncomputable def derivativePartial (n : Nat) (r : Real) : Complex :=
  ∫ u in (cutoff n)⁻¹..(cutoff n), parameterDeriv r u

/-- The reciprocal image of the standard cutoff interval.  For fixed
`r > 0`, both endpoints tend to the corresponding improper endpoints. -/
noncomputable def reciprocalPartial (n : Nat) (r : Real) : Complex :=
  ∫ v in (Real.sqrt r / cutoff n)..(Real.sqrt r / (cutoff n)⁻¹),
    oscilland r v

private theorem finitePartial_error_bound
    {r eta U : Real} (heta : 0 < eta) (hetaU : eta <= U) :
    norm (improperLimit r - (∫ u in eta..U, oscilland r u)) <=
      norm
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral U) +
        eta + 2 * Real.pi * |r| / U := by
  have hU : 0 < U := heta.trans_le hetaU
  have hperturb := perturbation_Ioi_split (r := r) hU
  have hzero := zeroPartial_decomposition U r
  have hoscSplit :
      (∫ u in (0 : Real)..eta, oscilland r u) +
          (∫ u in eta..U, oscilland r u) = zeroPartial U r := by
    unfold zeroPartial
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_oscilland 0 eta r)
      (intervalIntegrable_oscilland eta U r)
  have hperturb' :
      (∫ u in Ioi (0 : Real), fresnelPerturbation r u) =
        (zeroPartial U r - eq115HalfFresnelIntegral U) +
          perturbationTail r U := by
    rw [hperturb]
    have hfinite :
        (∫ u in (0 : Real)..U, fresnelPerturbation r u) =
          zeroPartial U r - eq115HalfFresnelIntegral U := by
      rw [hzero]
      ring
    rw [hfinite]
  have hidentity :
      improperLimit r - (∫ u in eta..U, oscilland r u) =
        ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral U) +
          (∫ u in (0 : Real)..eta, oscilland r u) +
          perturbationTail r U := by
    unfold improperLimit
    rw [hperturb', ← hoscSplit]
    ring
  rw [hidentity]
  calc
    norm
        (((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral U) +
          (∫ u in (0 : Real)..eta, oscilland r u) +
          perturbationTail r U) <=
          norm
            ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
              eq115HalfFresnelIntegral U) +
          norm (∫ u in (0 : Real)..eta, oscilland r u) +
          norm (perturbationTail r U) := norm_add₃_le
    _ <= norm
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral U) +
        eta + 2 * Real.pi * |r| / U := by
      exact add_le_add
        (add_le_add le_rfl (norm_oscilland_interval_zero_le heta.le))
        (norm_perturbationTail_le hU)

private theorem tendsto_fresnel_error_zero :
    Tendsto
      (fun U : Real =>
        norm
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral U))
      atTop (nhds 0) := by
  have hnorm :=
    tendsto_iff_norm_sub_tendsto_zero.mp iwaniecMozzochi_eq115_halfFresnel
  apply hnorm.congr'
  exact Eventually.of_forall fun U => norm_sub_rev _ _

private theorem tendsto_fresnel_cutoff_error_zero :
    Tendsto
      (fun n : Nat =>
        norm
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral (cutoff n)))
      atTop (nhds 0) := by
  exact tendsto_fresnel_error_zero.comp tendsto_cutoff_atTop

/-- The standard cutoff sequence converges pointwise to the explicitly
constructed improper integral. -/
theorem tendsto_standardPartial (r : Real) :
    Tendsto (fun n : Nat => standardPartial n r) atTop
      (nhds (improperLimit r)) := by
  let E : Nat -> Real := fun n =>
    norm
        ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
          eq115HalfFresnelIntegral (cutoff n)) +
      (cutoff n)⁻¹ + 2 * Real.pi * |r| / cutoff n
  have htail : Tendsto (fun n : Nat => 2 * Real.pi * |r| / cutoff n)
      atTop (nhds 0) := by
    change Tendsto (fun n : Nat => (2 * Real.pi * |r|) * (cutoff n)⁻¹)
      atTop (nhds 0)
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_cutoff_inv_zero
  have hE : Tendsto E atTop (nhds 0) := by
    dsimp only [E]
    simpa only [zero_add, add_zero] using
      (tendsto_fresnel_cutoff_error_zero.add tendsto_cutoff_inv_zero).add htail
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (g := E)
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun n => by
      unfold standardPartial
      rw [norm_sub_rev]
      exact finitePartial_error_bound (r := r)
        (inv_pos.mpr (cutoff_pos n)) (cutoff_inv_le n)
  · exact hE

private theorem tendsto_standard_error_major_zero (R : Real) :
    Tendsto
      (fun n : Nat =>
        norm
            ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
              eq115HalfFresnelIntegral (cutoff n)) +
          (cutoff n)⁻¹ + 2 * Real.pi * R / cutoff n)
      atTop (nhds 0) := by
  have htail : Tendsto (fun n : Nat => 2 * Real.pi * R / cutoff n)
      atTop (nhds 0) := by
    change Tendsto (fun n : Nat => (2 * Real.pi * R) * (cutoff n)⁻¹)
      atTop (nhds 0)
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_cutoff_inv_zero
  simpa only [zero_add, add_zero] using
    (tendsto_fresnel_cutoff_error_zero.add tendsto_cutoff_inv_zero).add htail

/-- The standard cutoff convergence is locally uniform on the positive
parameter ray.  On a neighborhood `0 < r < R`, the only parameter-dependent
tail is bounded by `2*pi*R/(n+1)`. -/
theorem tendstoLocallyUniformlyOn_standardPartial :
    TendstoLocallyUniformlyOn standardPartial improperLimit atTop (Ioi 0) := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  let R : Real := x + 1
  have hxR : x < R := by dsimp only [R]; linarith
  have hR0 : 0 < R := hx.trans hxR
  refine ⟨Ioo (0 : Real) R,
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hx hxR), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hmajor := tendsto_standard_error_major_zero R
  filter_upwards [hmajor.eventually (Iio_mem_nhds hepsilon)] with n hn
  intro r hr
  have hr0 : 0 < r := hr.1
  have hrR : |r| <= R := by
    rw [abs_of_pos hr0]
    exact hr.2.le
  have hbound := finitePartial_error_bound (r := r)
    (inv_pos.mpr (cutoff_pos n)) (cutoff_inv_le n)
  rw [dist_eq_norm]
  exact hbound.trans_lt <| lt_of_le_of_lt (by
    gcongr
    exact (cutoff_pos n).le) hn

private theorem reciprocalUpper_eq (n : Nat) (r : Real) :
    Real.sqrt r / (cutoff n)⁻¹ = Real.sqrt r * cutoff n := by
  field_simp [(cutoff_pos n).ne']

/-- For a positive parameter, the reciprocal cutoff sequence also converges
pointwise to the same improper integral. -/
theorem tendsto_reciprocalPartial {r : Real} (hr : 0 < r) :
    Tendsto (fun n : Nat => reciprocalPartial n r) atTop
      (nhds (improperLimit r)) := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hupper : Tendsto (fun n : Nat => Real.sqrt r / (cutoff n)⁻¹)
      atTop atTop := by
    have hmul := tendsto_cutoff_atTop.const_mul_atTop hs
    exact hmul.congr' (Eventually.of_forall fun n => (reciprocalUpper_eq n r).symm)
  have hlower : Tendsto (fun n : Nat => Real.sqrt r / cutoff n)
      atTop (nhds 0) := by
    change Tendsto (fun n : Nat => Real.sqrt r * (cutoff n)⁻¹)
      atTop (nhds 0)
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_cutoff_inv_zero
  have hzero := (tendsto_zeroPartial r).comp hupper
  have hlowerIntegral :
      Tendsto
        (fun n : Nat =>
          ∫ u in (0 : Real)..(Real.sqrt r / cutoff n), oscilland r u)
        atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact Eventually.of_forall fun n =>
        norm_oscilland_interval_zero_le
          (div_nonneg (Real.sqrt_nonneg _) (cutoff_pos n).le)
    · exact hlower
  have hdifference := hzero.sub hlowerIntegral
  simpa only [sub_zero] using hdifference.congr' (Eventually.of_forall fun n => by
    unfold zeroPartial reciprocalPartial
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_oscilland 0 (Real.sqrt r / cutoff n) r)
      (intervalIntegrable_oscilland (Real.sqrt r / cutoff n)
        (Real.sqrt r / (cutoff n)⁻¹) r)
    simp only [Function.comp_apply]
    rw [← hsplit]
    ring)

/-- The reciprocal cutoff convergence is locally uniform as well.  Around a
fixed `x > 0`, `sqrt r` is bounded above and bounded away from zero; hence the
reciprocal lower endpoint tends uniformly to zero and the reciprocal upper
endpoint tends uniformly to infinity. -/
theorem tendstoLocallyUniformlyOn_reciprocalPartial :
    TendstoLocallyUniformlyOn reciprocalPartial improperLimit atTop (Ioi 0) := by
  apply tendstoLocallyUniformlyOn_of_forall_exists_nhds
  intro x hx
  have hx0 : 0 < x := hx
  let m : Real := x / 2
  let M : Real := x + 1
  let lo : Real := Real.sqrt m
  let hi : Real := Real.sqrt M
  have hm0 : 0 < m := by dsimp only [m]; linarith
  have hmX : m < x := by dsimp only [m]; linarith
  have hxM : x < M := by dsimp only [M]; linarith
  have hM0 : 0 < M := hx.trans hxM
  have hlo0 : 0 < lo := by dsimp only [lo]; exact Real.sqrt_pos.2 hm0
  have hhi0 : 0 < hi := by dsimp only [hi]; exact Real.sqrt_pos.2 hM0
  refine ⟨Ioo m M,
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hmX hxM), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hepsilonThird : 0 < epsilon / 3 := by positivity
  have hFsmall : ∀ᶠ U in atTop,
      norm
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral U) < epsilon / 3 :=
    tendsto_fresnel_error_zero.eventually (Iio_mem_nhds hepsilonThird)
  obtain ⟨T, hT⟩ := (eventually_atTop.1 hFsmall)
  have hloCutoff : Tendsto (fun n : Nat => lo * cutoff n) atTop atTop :=
    tendsto_cutoff_atTop.const_mul_atTop hlo0
  have hlarge : ∀ᶠ n in atTop, T <= lo * cutoff n :=
    hloCutoff.eventually (eventually_ge_atTop T)
  have hetaLimit : Tendsto (fun n : Nat => hi / cutoff n) atTop (nhds 0) := by
    change Tendsto (fun n : Nat => hi * (cutoff n)⁻¹) atTop (nhds 0)
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_cutoff_inv_zero
  have hetaSmall : ∀ᶠ n in atTop, hi / cutoff n < epsilon / 3 :=
    hetaLimit.eventually (Iio_mem_nhds hepsilonThird)
  have htailLimit :
      Tendsto (fun n : Nat => 2 * Real.pi * M / (lo * cutoff n))
        atTop (nhds 0) := by
    have hbase : Tendsto
        (fun n : Nat => (2 * Real.pi * M / lo) * (cutoff n)⁻¹)
        atTop (nhds 0) := by
      simpa only [mul_zero] using
        tendsto_const_nhds.mul tendsto_cutoff_inv_zero
    apply hbase.congr'
    exact Eventually.of_forall fun n => by
      field_simp [hlo0.ne', (cutoff_pos n).ne']
  have htailSmall : ∀ᶠ n in atTop,
      2 * Real.pi * M / (lo * cutoff n) < epsilon / 3 :=
    htailLimit.eventually (Iio_mem_nhds hepsilonThird)
  filter_upwards [hlarge, hetaSmall, htailSmall] with n hnLarge hnEta hnTail
  intro r hr
  have hr0 : 0 < r := hm0.trans hr.1
  have hsqrt0 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr0
  have hsqrtLower : lo <= Real.sqrt r := by
    dsimp only [lo]
    exact Real.sqrt_le_sqrt hr.1.le
  have hsqrtUpper : Real.sqrt r <= hi := by
    dsimp only [hi]
    exact Real.sqrt_le_sqrt hr.2.le
  have heta : 0 < Real.sqrt r / cutoff n :=
    div_pos hsqrt0 (cutoff_pos n)
  have hetaU : Real.sqrt r / cutoff n <=
      Real.sqrt r / (cutoff n)⁻¹ :=
    div_le_div_of_nonneg_left (Real.sqrt_nonneg r)
      (inv_pos.mpr (cutoff_pos n)) (cutoff_inv_le n)
  have hupperLarge : T <= Real.sqrt r / (cutoff n)⁻¹ := by
    rw [reciprocalUpper_eq]
    exact hnLarge.trans (mul_le_mul_of_nonneg_right hsqrtLower
      (cutoff_pos n).le)
  have hFactual :
      norm
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) -
            eq115HalfFresnelIntegral
              (Real.sqrt r / (cutoff n)⁻¹)) < epsilon / 3 :=
    hT _ hupperLarge
  have hetaActual : Real.sqrt r / cutoff n < epsilon / 3 :=
    (div_le_div_of_nonneg_right hsqrtUpper (cutoff_pos n).le).trans_lt hnEta
  have htailActual :
      2 * Real.pi * |r| / (Real.sqrt r / (cutoff n)⁻¹) < epsilon / 3 := by
    have hnum : 2 * Real.pi * |r| <= 2 * Real.pi * M := by
      rw [abs_of_pos hr0]
      gcongr
      exact hr.2.le
    have hdenom : lo * cutoff n <= Real.sqrt r / (cutoff n)⁻¹ := by
      rw [reciprocalUpper_eq]
      exact mul_le_mul_of_nonneg_right hsqrtLower (cutoff_pos n).le
    have hcompare :
        2 * Real.pi * |r| / (Real.sqrt r / (cutoff n)⁻¹) <=
          2 * Real.pi * M / (lo * cutoff n) :=
      div_le_div₀ (by positivity) hnum (mul_pos hlo0 (cutoff_pos n)) hdenom
    exact hcompare.trans_lt hnTail
  have hbound := finitePartial_error_bound (r := r) heta hetaU
  rw [dist_eq_norm]
  exact hbound.trans_lt <| by
    linarith

private theorem tendsto_fresnelPerturbation_interval_zero :
    Tendsto
      (fun r : Real =>
        ∫ u in (0 : Real)..1, fresnelPerturbation r u)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hmeas : ∀ᶠ r in nhdsWithin (0 : Real) (Ioi 0),
      AEStronglyMeasurable (fresnelPerturbation r)
        (volume.restrict (Set.uIoc (0 : Real) 1)) :=
    Eventually.of_forall fun r =>
      (measurable_fresnelPerturbation r).aestronglyMeasurable
  have hbound : ∀ᶠ r in nhdsWithin (0 : Real) (Ioi 0),
      ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : Real) 1 ->
        norm (fresnelPerturbation r u) <= (fun _ : Real => 2) u :=
    Eventually.of_forall fun r =>
      Eventually.of_forall fun u _ => norm_fresnelPerturbation_le_two r u
  have hmajor : IntervalIntegrable (fun _ : Real => (2 : Real)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hpointwise : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : Real) 1 ->
      Tendsto (fun r : Real => fresnelPerturbation r u)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    exact Eventually.of_forall fun u _ => by
      have hcont : Continuous (fun r : Real => fresnelPerturbation r u) := by
        unfold fresnelPerturbation oscilland e
        fun_prop
      have ht : Tendsto (fun r : Real => fresnelPerturbation r u)
          (nhdsWithin 0 (Ioi 0)) (nhds (fresnelPerturbation 0 u)) :=
        hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have hzero : fresnelPerturbation 0 u = 0 := by
        unfold fresnelPerturbation oscilland
        simp only [zero_div, add_zero, sub_self]
      simpa only [hzero] using ht
  simpa only [intervalIntegral.integral_zero] using
    intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (a := (0 : Real)) (b := 1) (μ := volume)
      (F := fun r u => fresnelPerturbation r u)
      (f := fun _ : Real => (0 : Complex))
      (bound := fun _ : Real => 2)
      hmeas hbound hmajor hpointwise

private theorem tendsto_perturbationTail_one_zero :
    Tendsto (fun r : Real => perturbationTail r 1)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero'
  · exact Eventually.of_forall fun _ => norm_nonneg _
  · exact Eventually.of_forall fun r => by
      simpa only [div_one] using
        (norm_perturbationTail_le (r := r) (U := (1 : Real)) one_pos)
  · have hid : Tendsto (fun r : Real => r)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto (fun _ : Real => 2 * Real.pi)
        (nhdsWithin 0 (Ioi 0)) (nhds (2 * Real.pi)) :=
      tendsto_const_nhds
    simpa only [abs_zero, mul_zero] using hconst.mul hid.abs

/-- The explicitly constructed improper integral has the evaluated
half-Fresnel boundary at `r = 0+`. -/
theorem tendsto_improperLimit_zero :
    Tendsto improperLimit (nhdsWithin 0 (Ioi 0))
      (nhds (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2)) := by
  have hperturb :
      Tendsto
        (fun r : Real =>
          ∫ u in Ioi (0 : Real), fresnelPerturbation r u)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hsum := tendsto_fresnelPerturbation_interval_zero.add
      tendsto_perturbationTail_one_zero
    simpa only [zero_add] using hsum.congr'
      (Eventually.of_forall fun r =>
        (perturbation_Ioi_split (r := r) one_pos).symm)
  unfold improperLimit
  simpa only [add_zero] using tendsto_const_nhds.add hperturb

private theorem parameterDeriv_eq_weighted (r u : Real) :
    parameterDeriv r u =
      (2 * Real.pi * Complex.I) * weightedOscilland r u := by
  unfold parameterDeriv weightedOscilland
  push_cast
  ring

/-- The derivative of a canonical finite truncation is the conjugate integral
over its reciprocal interval.  This is the finite-cutoff identity behind the
coupled ODE; it contains no limiting argument. -/
theorem derivativePartial_eq_reciprocal
    (n : Nat) {r : Real} (hr : 0 < r) :
    derivativePartial n r =
      (((odeCoeff r : Real) : Complex) * Complex.I) *
        starRingEnd Complex (reciprocalPartial n r) := by
  have heta : 0 < (cutoff n)⁻¹ := inv_pos.mpr (cutoff_pos n)
  have hweighted := weightedPartial_reciprocal hr heta (cutoff_inv_le n)
  unfold derivativePartial reciprocalPartial
  calc
    (∫ u in (cutoff n)⁻¹..(cutoff n), parameterDeriv r u) =
        ∫ u in (cutoff n)⁻¹..(cutoff n),
          (2 * Real.pi * Complex.I) * weightedOscilland r u := by
      apply intervalIntegral.integral_congr
      intro u _
      exact parameterDeriv_eq_weighted r u
    _ = (2 * Real.pi * Complex.I) *
        (∫ u in (cutoff n)⁻¹..(cutoff n), weightedOscilland r u) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (((odeCoeff r : Real) : Complex) * Complex.I) *
        starRingEnd Complex
          (∫ v in (Real.sqrt r / cutoff n)..
              (Real.sqrt r / (cutoff n)⁻¹), oscilland r v) := by
      rw [hweighted]
      unfold odeCoeff
      push_cast
      ring

private theorem standardPartial_hasDerivAt (n : Nat) {r : Real} :
    HasDerivAt (standardPartial n) (derivativePartial n r) r := by
  unfold standardPartial derivativePartial
  exact partialIntegral_hasDerivAt (inv_pos.mpr (cutoff_pos n))
    (cutoff_inv_le n)

/-- The exact remaining locally uniform analytic interface.

The first convergence constructs the improper integral from standard
two-sided cutoffs.  The second says that a fixed positive reciprocal rescaling
of both cutoffs gives the same improper integral.  The finite reciprocal
identity above then makes the derivative integrals converge locally uniformly
automatically, so that Mathlib's uniform-limit differentiation theorem
applies.  The final clause is the already evaluated half-Fresnel boundary
value.

None of these clauses states a Bessel evaluation or the desired exponential
formula. -/
def NegativeReciprocalLocallyUniformLimit : Prop :=
  exists F : Real -> Complex,
    TendstoLocallyUniformlyOn
      standardPartial F atTop (Ioi 0) ∧
    TendstoLocallyUniformlyOn
      reciprocalPartial F atTop (Ioi 0) ∧
    Tendsto F (nhdsWithin 0 (Ioi 0))
      (nhds (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2))

/-- The locally uniform analytic interface is discharged by the explicit
Fresnel-perturbation construction and its compact-parameter tail bounds. -/
theorem negativeReciprocalLocallyUniformLimit_holds :
    NegativeReciprocalLocallyUniformLimit :=
  ⟨improperLimit, tendstoLocallyUniformlyOn_standardPartial,
    tendstoLocallyUniformlyOn_reciprocalPartial, tendsto_improperLimit_zero⟩

private theorem tendstoLocallyUniformlyOn_refl
    {f : Real -> Complex} {s : Set Real} :
    TendstoLocallyUniformlyOn (fun _ : Nat => f) f atTop s := by
  intro u hu x _
  refine ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ => ?_⟩
  exact refl_mem_uniformity hu

/-- The local-uniform cutoff interface implies the coupled ODE.  This theorem
is the formal bridge from finite calculus to the abstract uniqueness argument;
the only analytic content it consumes is
`NegativeReciprocalLocallyUniformLimit`. -/
theorem exists_coupled_solution_of_locallyUniformLimit
    (hlimit : NegativeReciprocalLocallyUniformLimit) :
    exists F : Real -> Complex,
      TendstoLocallyUniformlyOn standardPartial F atTop (Ioi 0) ∧
      Tendsto F (nhdsWithin 0 (Ioi 0))
        (nhds (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2)) ∧
      forall r : Real, 0 < r -> HasDerivAt F
        (((odeCoeff r : Real) : Complex) * Complex.I *
          starRingEnd Complex (F r)) r := by
  rcases hlimit with ⟨F, hstandard, hreciprocal, hboundary⟩
  refine ⟨F, hstandard, hboundary, ?_⟩
  have hconjugate :
      TendstoLocallyUniformlyOn
        (fun n => starRingEnd Complex ∘ reciprocalPartial n)
        (starRingEnd Complex ∘ F) atTop (Ioi 0) :=
    Complex.isometry_conj.uniformContinuous.comp_tendstoLocallyUniformlyOn
      hreciprocal
  have hcoefficient :
      TendstoLocallyUniformlyOn
        (fun _ : Nat => fun r : Real =>
          (((odeCoeff r : Real) : Complex) * Complex.I))
        (fun r : Real => (((odeCoeff r : Real) : Complex) * Complex.I))
        atTop (Ioi 0) :=
    tendstoLocallyUniformlyOn_refl
  have hstandardContinuous : ∀ᶠ n in atTop,
      ContinuousOn (standardPartial n) (Ioi (0 : Real)) := by
    exact Eventually.of_forall fun n r hr =>
      (standardPartial_hasDerivAt n).continuousAt.continuousWithinAt
  have hFContinuous : ContinuousOn F (Ioi (0 : Real)) :=
    hstandard.continuousOn hstandardContinuous.frequently
  have hcoefficientContinuous : ContinuousOn
      (fun r : Real => (((odeCoeff r : Real) : Complex) * Complex.I))
      (Ioi 0) := by
    have hode : ContinuousOn odeCoeff (Ioi (0 : Real)) := by
      unfold odeCoeff
      fun_prop (disch := grind [Set.mem_Ioi])
    exact (Complex.continuous_ofReal.comp_continuousOn hode).mul continuousOn_const
  have hconjugateContinuous : ContinuousOn (starRingEnd Complex ∘ F)
      (Ioi (0 : Real)) :=
    Complex.continuous_conj.comp_continuousOn hFContinuous
  have hproduct := hcoefficient.mul₀ hconjugate
    hcoefficientContinuous hconjugateContinuous
  have hderivative :
      TendstoLocallyUniformlyOn derivativePartial
        (fun r => (((odeCoeff r : Real) : Complex) * Complex.I) *
          starRingEnd Complex (F r)) atTop (Ioi 0) := by
    have hproduct' : TendstoLocallyUniformlyOn
        (fun n r => (((odeCoeff r : Real) : Complex) * Complex.I) *
          starRingEnd Complex (reciprocalPartial n r))
        (fun r => (((odeCoeff r : Real) : Complex) * Complex.I) *
          starRingEnd Complex (F r)) atTop (Ioi 0) := by
      refine (hproduct.congr ?_).congr_right ?_
      · intro n r hr
        simp only [Pi.mul_apply, Function.comp_apply]
      · intro r hr
        simp only [Pi.mul_apply, Function.comp_apply]
    apply hproduct'.congr
    intro n r hr
    exact (derivativePartial_eq_reciprocal n hr).symm
  have hfinite : ∀ᶠ n in atTop, ∀ x ∈ Ioi (0 : Real),
      HasDerivAt (standardPartial n) (derivativePartial n x) x := by
    exact Eventually.of_forall fun n x _ => standardPartial_hasDerivAt n
  intro r hr
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioi hderivative
    hfinite (fun x hx => hstandard.tendsto_at hx) hr

/-- Consequently, the standard finite cutoffs converge to the unique decaying
solution.  This is the strict-negative reciprocal-quadratic evaluation obtained
from the reusable analytic interface above. -/
theorem tendsto_standardPartial_of_locallyUniformLimit
    (hlimit : NegativeReciprocalLocallyUniformLimit) {r : Real} (hr : 0 < r) :
    Tendsto (fun n : Nat => standardPartial n r) atTop
      (nhds
        ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) *
          ((Real.exp (-4 * Real.pi * Real.sqrt r) : Real) : Complex))) := by
  rcases exists_coupled_solution_of_locallyUniformLimit hlimit with
    ⟨F, hstandard, hboundary, hODE⟩
  have hvalue := coupled_ode_unique hODE hboundary halfFresnel_phase r hr
  unfold decay at hvalue
  rw [← hvalue]
  exact hstandard.tendsto_at hr

/-- Unconditional strict-negative evaluation for the actual finite integrals
from `0`, with a real upper cutoff tending to infinity.  This is the normalized
analytic statement needed after the substitution `t = a/u^2`. -/
theorem tendsto_zeroPartial_exact {r : Real} (hr : 0 < r) :
    Tendsto (fun U : Real => zeroPartial U r) atTop
      (nhds
        ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) *
          ((Real.exp (-4 * Real.pi * Real.sqrt r) : Real) : Complex))) := by
  have hstandardValue := tendsto_standardPartial_of_locallyUniformLimit
    negativeReciprocalLocallyUniformLimit_holds hr
  have hstandardImproper := tendsto_standardPartial r
  have hvalue : improperLimit r =
      (((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) *
        ((Real.exp (-4 * Real.pi * Real.sqrt r) : Real) : Complex) :=
    tendsto_nhds_unique hstandardImproper hstandardValue
  rw [← hvalue]
  exact tendsto_zeroPartial r

/-- For a nonpositive linear frequency, the normalized oscilland can be
written in the literal reciprocal-phase form used after the substitution
`t = a / u^2`. -/
theorem zeroPartial_eq_negativeReciprocalPhase
    {a c U : Real} (hc : c <= 0) :
    zeroPartial U (a * |c|) =
      ∫ u in (0 : Real)..U, e (-(u ^ 2) - (a * c) / u ^ 2) := by
  unfold zeroPartial oscilland
  apply intervalIntegral.integral_congr
  intro u _
  congr 1
  rw [abs_of_nonpos hc]
  ring

/-- Composing the exact normalized limit with the moving endpoint
`sqrt (a / delta)` and the Jacobian factor produced by `t = a / u^2`.  This
generic scaling lemma is the analytic input needed by the strict-negative
generalized Bessel bridge. -/
theorem tendsto_scaled_zeroPartial_exact {a r : Real}
    (ha : 0 < a) (hr : 0 < r) :
    Tendsto
      (fun delta : Real =>
        ((2 / Real.sqrt a : Real) : Complex) *
          zeroPartial (Real.sqrt (a / delta)) r)
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (((2 / Real.sqrt a : Real) : Complex) *
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) *
            ((Real.exp (-4 * Real.pi * Real.sqrt r) : Real) : Complex)))) := by
  exact tendsto_const_nhds.mul
    ((tendsto_zeroPartial_exact hr).comp
      (tendsto_eq115_truncationEndpoint ha))

/-- The scaled strict-negative reciprocal-phase limit in the literal form
appearing on the right of the truncated Bessel change of variables. -/
theorem tendsto_scaled_negativeReciprocalPhase_exact
    {a c : Real} (ha : 0 < a) (hc : c < 0) :
    Tendsto
      (fun delta : Real =>
        ((2 / Real.sqrt a : Real) : Complex) *
          (∫ u in (0 : Real)..Real.sqrt (a / delta),
            e (-(u ^ 2) - (a * c) / u ^ 2)))
      (nhdsWithin 0 (Ioi 0))
      (nhds
        (((2 / Real.sqrt a : Real) : Complex) *
          ((((2 : Complex) * Complex.I) ^ (-(1 : Complex) / 2) / 2) *
            ((Real.exp
              (-4 * Real.pi * Real.sqrt (a * |c|)) : Real) : Complex)))) := by
  have hr : 0 < a * |c| := mul_pos ha (abs_pos.mpr hc.ne)
  have hlimit := tendsto_scaled_zeroPartial_exact ha hr
  apply hlimit.congr'
  exact Eventually.of_forall fun delta => by
    change ((2 / Real.sqrt a : Real) : Complex) *
        zeroPartial (Real.sqrt (a / delta)) (a * |c|) =
      ((2 / Real.sqrt a : Real) : Complex) *
        (∫ u in (0 : Real)..Real.sqrt (a / delta),
          e (-(u ^ 2) - (a * c) / u ^ 2))
    rw [zeroPartial_eq_negativeReciprocalPhase hc.le]

end NegativeReciprocalODE

end LeanProofs.IntegerPoints

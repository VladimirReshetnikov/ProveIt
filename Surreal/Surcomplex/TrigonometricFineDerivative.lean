import Surreal.Surcomplex.TrigonometricTaylor
import Surreal.Surcomplex.AnalyticLiftCalculus

/-!
# Fine derivatives of finite surreal trigonometry

The separate sine and cosine strong sums agree with the ordinary analytic
Taylor lifts. Their ambient functions therefore have the derivatives stated
in `trigonometry:thm:identities` at every finite real surreal point. The phase
has a surcomplex-valued difference quotient with a real surreal increment;
its derivative is `I * cis`. Every limit uses the native fine topology.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Filter Topology

noncomputable section

/-- Sine as an ambient real surreal function, equal to finite sine on its domain. -/
def sinFunction : SignSequence.{u} → SignSequence.{u} :=
  SignSequence.analyticLiftFunction Real.sin

/-- Cosine as an ambient real surreal function, equal to finite cosine on its domain. -/
def cosFunction : SignSequence.{u} → SignSequence.{u} :=
  SignSequence.analyticLiftFunction Real.cos

/-- The analytic lift gives exactly the previously defined finite cosine. -/
theorem cosFunction_eq_finiteCos (θ : SignSequence.FiniteElement.{u}) :
    cosFunction θ.val = finiteCos θ := by
  rw [cosFunction, SignSequence.analyticLiftFunction_of_domain _ _ θ.property Real.analyticAt_cos]
  simp only [SignSequence.analyticLift, SignSequence.analyticTaylorEvaluation]
  rw [Analytic.taylorSeries_real_cos]
  simp only [map_sub, map_mul, SignSequence.powerSeriesEvaluation_C,
    powerSeriesEvaluation_taylor_cos_zero, powerSeriesEvaluation_taylor_sin_zero]
  exact (finiteCos_eq_taylor θ).symm

/-- The analytic lift gives exactly the previously defined finite sine. -/
theorem sinFunction_eq_finiteSin (θ : SignSequence.FiniteElement.{u}) :
    sinFunction θ.val = finiteSin θ := by
  rw [sinFunction, SignSequence.analyticLiftFunction_of_domain _ _ θ.property Real.analyticAt_sin]
  simp only [SignSequence.analyticLift, SignSequence.analyticTaylorEvaluation]
  rw [Analytic.taylorSeries_real_sin]
  simp only [map_add, map_mul, SignSequence.powerSeriesEvaluation_C,
    powerSeriesEvaluation_taylor_cos_zero, powerSeriesEvaluation_taylor_sin_zero]
  exact (finiteSin_eq_taylor θ).symm

/-- The fine derivative of sine is cosine at every finite real surreal point. -/
theorem fineHasDerivAt_sinFunction (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    FineHasDerivAt sinFunction (cosFunction x) x := by
  simpa only [sinFunction, cosFunction, Real.deriv_sin] using
    SignSequence.fineHasDerivAt_analyticLiftFunction Real.sin x hx Real.analyticAt_sin

/-- The fine derivative of cosine is negative sine at every finite real surreal point. -/
theorem fineHasDerivAt_cosFunction (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    FineHasDerivAt cosFunction (-sinFunction x) x := by
  have he : deriv Real.cos = -Real.sin := Real.deriv_cos'
  simpa only [cosFunction, sinFunction, he,
    SignSequence.analyticLiftFunction_neg Real.sin x hx Real.analyticAt_sin] using
    SignSequence.fineHasDerivAt_analyticLiftFunction Real.cos x hx Real.analyticAt_cos

/-- The surcomplex phase as a function of real surreal angles. -/
def cisFunction (x : SignSequence.{u}) : Surcomplex.{u} :=
  ofReal (cosFunction x) + ofReal (sinFunction x) * I

/-- The ambient phase agrees with the existing finite phase. -/
theorem cisFunction_eq_finitePhase (θ : SignSequence.FiniteElement.{u}) :
    cisFunction θ.val = finitePhase θ := by
  rw [cisFunction, cosFunction_eq_finiteCos, sinFunction_eq_finiteSin]
  exact (finitePhase_eq_cos_add_sin_mul_I θ).symm

/-- Fine differentiation of a surcomplex-valued function along the real surreal axis. -/
def RealFineHasDerivAt (f : SignSequence.{u} → Surcomplex.{u})
    (d : Surcomplex.{u}) (a : SignSequence.{u}) : Prop :=
  Tendsto (fun h => (f (a + h) - f a) / ofReal h) (𝓝[≠] 0) (𝓝 d)

/-- Euler's phase has the derivative `I * cis`, using all nonzero real surreal increments. -/
theorem realFineHasDerivAt_cisFunction (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    RealFineHasDerivAt cisFunction (I * cisFunction x) x := by
  have hc := continuous_ofReal.continuousAt.tendsto.comp (fineHasDerivAt_cosFunction x hx)
  have hs := continuous_ofReal.continuousAt.tendsto.comp (fineHasDerivAt_sinFunction x hx)
  have ht := hc.add (hs.mul_const I)
  have he : ofReal (-sinFunction x) + ofReal (cosFunction x) * I = I * cisFunction x := by
    simp only [cisFunction, map_neg]
    linear_combination -(ofReal (sinFunction x)) * (I_sq : (I : Surcomplex.{u}) ^ 2 = -1)
  rw [he] at ht
  apply ht.congr'
  exact Filter.Eventually.of_forall fun h => by
    simp only [Function.comp_apply, cisFunction, map_div₀, map_sub]
    ring

/-- Finite sine is continuous in the full native surreal topology. -/
theorem continuousAt_sinFunction (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    ContinuousAt sinFunction x := (fineHasDerivAt_sinFunction x hx).continuousAt

/-- Finite cosine is continuous in the full native surreal topology. -/
theorem continuousAt_cosFunction (x : SignSequence.{u}) (hx : SignSequence.IsFinite x) :
    ContinuousAt cosFunction x := (fineHasDerivAt_cosFunction x hx).continuousAt

end

end Surreal.Surcomplex

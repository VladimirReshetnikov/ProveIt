import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialTaylorTransport
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalLinearProduct
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Named.GaussianGammaDigammaTwoShiftNamedSize

/-!
# First-order estimate for the finite Barnes correction exponential

The exponent is the original finite correction fold. The estimate
compares the increment of its actual radius-programmed exponential
with its derivative times the input increment.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadCorrectionExponentialDerivative

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalCorrectionShift (total)
open GaussianBarnesCanonicalHeadCorrectionDerivative (slope linear total_formula quadratic_bound)
open GaussianBarnesCanonicalHeadExponentialFactors (exponentData)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular constant_at harmonicPoint)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical qmul positive_product canonical_congr)
open GaussianRationalMetric (bounded qsub qsub_canonical)
open GaussianRationalReciprocal (bounded_product bounded_difference bound_congr)
open GaussianRationalNaturalScale (naturalPoint)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev exponentialF : PR 2 := GaussianRadiusExponentialName.nameF constantF
abbrev incrementF : PR 2 := GaussianNamedDifference.nameF exponentialF exponentialF
abbrev derivativeF : PR 2 := multiplyF exponentialF constantF
abbrev linearF : PR 2 := multiplyF constantF derivativeF

def incrementData (z h B N : PTm n) : PTm n :=
  GaussianNamedDifference.data (exponentData (add z h) B N) (exponentData z B N)
def derivativeData (z B N : PTm n) : PTm n := multiplyData exponentialF constantF (exponentData z B N) (slope z B N)
def linearData (z h B N : PTm n) : PTm n := multiplyData constantF derivativeF (ofGaussian h B) (derivativeData z B N)

def exponentRadius (R N : PTm n) : PTm n := one+N*(R+R*R)
def incrementGain (R N : PTm n) : PTm n := N*(R+two)
def exponentialBound (R N : PTm n) : PTm n := GaussianCyclicExponentialSamples.sampleBound (two*exponentRadius R N+two)
def errorGain (R N : PTm n) : PTm n :=
  GaussianNamedExponentialTaylorTransport.numerator (exponentRadius R N) (incrementGain R N) N
def errorNumerator (R N H : PTm n) : PTm n := errorGain R N*H*H

@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (exponentData z B N) = exponentData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) :=
  by simp [exponentData,GaussianGammaFiniteApproximantName.exponentialInputData]

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (incrementData z h B N) = incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) :=
  by simp [incrementData]

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (derivativeData z B N) = derivativeData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) :=
  by simp [derivativeData]

@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (linearData z h B N) = linearData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) :=
  by simp [linearData]

@[simp] theorem subst_exponentRadius {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (exponentRadius R N) = exponentRadius (Syn.subst σ R) (Syn.subst σ N) :=
  by simp [exponentRadius,one]

@[simp] theorem subst_incrementGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (incrementGain R N) = incrementGain (Syn.subst σ R) (Syn.subst σ N) :=
  by simp [incrementGain,two]

@[simp] theorem subst_exponentialBound {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (exponentialBound R N) = exponentialBound (Syn.subst σ R) (Syn.subst σ N) :=
  by simp [exponentialBound,two]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (errorGain R N) = errorGain (Syn.subst σ R) (Syn.subst σ N) := by simp [errorGain]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (R N H : PTm n) :
    Syn.subst σ (errorNumerator R N H) = errorNumerator (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ H) :=
  by simp [errorNumerator]

theorem exponent_bound (z B N R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (total z B N) (exponentRadius R N) one := by
  have p := GaussianGammaEulerHead.fraction_disk z R B hB hz
  have hb : Γ ⊢[PRAAx] le B (two*B) := le_congr (one_mul B) (.eqRefl _) (mul_le_mul_right B (le_succ_self one))
  have h₂ := le_trans hB hb
  have q := GaussianGammaEulerHead.fraction_disk z R (two*B) h₂
    (ComplexLogarithmRemainder.bounded_mono hz (le_mul_mono (le_refl R) hb))
  have a := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ R one R one (le_refl one) (le_refl one) p q)
  have b := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ (R*R) one N one (le_refl one) (le_refl one) a
      (GaussianGammaCanonicalExponentBound.harmonic_point_bound N))
  have c := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ N one R one (le_refl one) (le_refl one) (GaussianNamedNaturalScale.natural_point_bound N) p)
  have d := bounded_difference _ _ (R*R*N) one (N*R) one (le_refl one) (le_refl one) b c
  exact bound_congr (total_formula z B N hB).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ (positive_product one one (le_refl one) (le_refl one)) (le_refl one)
      (le_congr (by ipra_ring) (by unfold exponentRadius; ipra_ring) (le_add_left (N*(R+R*R)) one)) d)

theorem slope_bound (z B N R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (slope z B N) (N*(R+one)) one := by
  have p := bound_congr (.eqRefl _) (.eqRefl _) (one_mul one)
    (bounded_product _ _ R one N one (le_refl one) (le_refl one) (GaussianGammaEulerHead.fraction_disk z R B hB hz)
      (GaussianGammaCanonicalExponentBound.harmonic_point_bound N))
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (bounded_difference _ _ (R*N) one N one (le_refl one) (le_refl one) p (GaussianNamedNaturalScale.natural_point_bound N))

theorem exponential_regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN exponentialF (exponentData z B N) :=
  GaussianRadiusExponentialName.name_regular constantF _ _ (exponential_input constantF _ (constant_regular _))

theorem derivative_regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN derivativeF (derivativeData z B N) :=
  multiply_fast _ _ _ _ (exponential_regular z B N) (constant_regular _)

theorem exponential_sample_bound (p z B N R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] bounded (ap2 exponentialF p (exponentData z B N)) (exponentialBound R N) one := by
  let x := total z B N
  let r := U constantF x
  let S := exponentRadius R N
  have h := exponent_bound z B N R hB hz
  have ur := GaussianNamedExponentialTaylorTransport.radius_from_sample constantF x S
    (bound_congr (constant_at _ x).eqSymm (.eqRefl _) (.eqRefl _) h)
  have fit := GaussianFactorBudget.power_monotone_length (num 3) r (two*S+two)
    (le_trans (le_succ_self one) (le_succ_self two)) ur
  have fit' : Γ ⊢[PRAAx] le (GaussianCyclicExponentialSamples.sampleBound r*one) (exponentialBound R N*one) :=
    le_congr (by unfold GaussianCyclicExponentialSamples.sampleBound; ipra_ring)
      (by unfold exponentialBound GaussianCyclicExponentialSamples.sampleBound; ipra_ring) fit
  exact bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) fit'
    (GaussianCyclicExponentialSamples.exponential_bound constantF r x p
      (exponential_input constantF x (constant_regular x)))

theorem exponential_samples (z B N R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound exponentialF (exponentData z B N) (exponentialBound R N) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have b : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift
  have h : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh z) (sh R*sh B) :=
    by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,
    subst_exponentData,subst_exponentialBound] using
    exponential_sample_bound (var 0) (sh z) (sh B) (sh N) (sh R) b h

private theorem increment_bound (z h B N R H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) (hH : Γ ⊢[PRAAx] le H B) :
    Γ ⊢[PRAAx] bounded (qsub (total (add z h) B N) (total z B N)) (incrementGain R N*H) B := by
  let W := qsub (total (add z h) B N) (total z B N)
  let L := linear z h B N
  let a := N*H
  let c := H*(N*(R+one))
  have d := positive_product _ _ hB hB
  have hstep : Γ ⊢[PRAAx] bounded (ofGaussian h B) H B :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hB hB (ofGaussian_represents h B hB)
      (le_congr (.eqRefl _) (mul_comm _ _) (le_mul_mono (le_refl (B*B)) hh))
  have hlin : Γ ⊢[PRAAx] bounded L c B := bound_congr (.eqRefl _) (.eqRefl _) (show Γ ⊢[PRAAx] B*one ≐ B by ipra_ring)
    (bounded_product _ _ H B _ one hB (le_refl one) hstep (slope_bound z B N R hB hz))
  have fit : Γ ⊢[PRAAx] le ((N*H*H)*B) (a*(B*B)) :=
    le_congr (by ipra_ring) (by unfold a; ipra_ring) (mul_le_mul_right (N*H*B) hH)
  have q : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded W L a B :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ d hB fit
      (quadratic_bound z h B N H hB hh)
  exact bounded_radius_mono _ _ _ _ _ d hB
    (le_of_eq_add (d := LeanProofs.ConciseIPRA.PTm.zero) (by dsimp only [a,c,incrementGain]; ipra_ring))
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hB hB q hlin)

private theorem small_constant (x A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A B)
    (hx : Γ ⊢[PRAAx] bounded x A B) (hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical x) :
    Γ ⊢[PRAAx] GaussianNamedExponentialLinearRate.source constantF x A B := by
  refine .andI hB (.andI hA (.andI (constant_regular x) (.allI ?_)))
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] bounded (sh x) (sh A) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hx.shift
  have c : Δ ⊢[PRAAx] GaussianRationalHorner.canonical (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hc.shift
  have e := constant_at (Γ := Δ) (var 0) (sh x)
  exact .andI (bound_congr e.eqSymm (.eqRefl _) (.eqRefl _) h) (canonical_congr e c)

private theorem linear_cross (z h B N : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent linearF derivativeF (linearData z h B N)
      (multiplyData exponentialF constantF (exponentData z B N) (linear z h B N)) := by
  let a := ofGaussian h B
  let x := exponentData z B N
  let b := slope z B N
  let F := exponentialF
  let C := constantF
  have ha := constant_regular (Γ := Γ) a
  have hx := exponential_regular (Γ := Γ) z B N
  have hb := constant_regular (Γ := Γ) b
  have swap := GaussianNameRingLaws.multiply_commutative C derivativeF a (derivativeData z B N) ha (derivative_regular z B N)
  have group := GaussianNameRingLaws.multiply_associative F C C x b a hx hb ha
  have rhs := GaussianGammaDigammaTwoShiftNamedSize.constant_product (Γ := Γ) b a (linear z h B N)
    (GaussianRationalPowerAlgebra.qmul_commutative b a)
  have res := GaussianGammaAdjacentCutoff.multiply_cross F F (multiplyF C C) C x x (multiplyData C C b a) (linear z h B N)
    hx hx (multiply_fast _ _ _ _ hb ha) (constant_regular _) (cross_refl _ _ hx) rhs
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ swap
    (GaussianNameEquivalence.cross_trans _ _ _ _ _ _ group res)

theorem rate (z h B N R H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) (hH : Γ ⊢[PRAAx] le H B)
    (hsmall : Γ ⊢[PRAAx] le (incrementGain R N*H) B) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData z h B N) (linearData z h B N)
      (errorNumerator R N H) (B*B) := by
  let C := constantF
  let x := total z B N
  let v := total (add z h) B N
  let y := qsub v x
  let w := linear z h B N
  let A := incrementGain R N*H
  let R₀ := U C x
  let R₁ := U C v
  let S := exponentRadius R N
  let W := GaussianNamedExponentialTaylorTransport.numerator S A (N*H*H)
  have hR : Γ ⊢[PRAAx] le one S := le_add_right _ _
  have hf := GaussianSignedNameExponentialOrder.constant_input x S (exponent_bound z B N R hB hz)
  have hv : Γ ⊢[PRAAx] GaussianRationalHorner.canonical v := GaussianRationalFiniteSum.sum_canonical _ _ _
  have d := positive_product _ _ hB hB
  have hy := small_constant y A B hB hsmall (increment_bound z h B N R H hB hz hh hH) (qsub_canonical _ _)
  have e := GaussianNamedGammaHalfShift.constant_sum x y v (GaussianRationalLinearProduct.add_sub_right x v hv)
  have r := GaussianNamedAddRate.constant_rate y w (N*H*H) (B*B) d (quadratic_bound z h B N H hB hh)
  have raw := GaussianNamedExponentialTaylorTransport.rate C C C S R₀ R₁ x v y w A B (N*H*H) hR hf
    (exponential_input C x (constant_regular _)) (exponential_input C v (constant_regular _))
    hy (constant_regular _) e r
  have moved := GaussianNamedRateTransport.transport incrementF derivativeF incrementF linearF (incrementData z h B N)
    (multiplyData exponentialF constantF (exponentData z B N) w) (incrementData z h B N) (linearData z h B N) W (B*B) d raw
    (cross_refl _ _ (GaussianNamedDifference.name_regular exponentialF exponentialF _ _
      (exponential_regular (add z h) B N) (exponential_regular z B N))) (linear_cross z h B N)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [W,S,A,errorNumerator,errorGain,GaussianNamedExponentialTaylorTransport.numerator]; ipra_ring)
    (.eqRefl _) moved

theorem actual_finite_Barnes_correction_exponential_first_order_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (let z := var 0
       let h := var 1
       let B := var 2
       let N := var 3
       let R := var 4
       let H := var 5
       (le one B ⋏ (ComplexLogarithmRemainder.bounded z (R*B) ⋏ (ComplexLogarithmRemainder.bounded h H ⋏
        (le H B ⋏ le (incrementGain R N*H) B)))) ⟶
        independentRate incrementF linearF (incrementData z h B N) (linearData z h B N) (errorNumerator R N H) (B*B)) :=
  closeUniv 6 (.impI (rate _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadCorrectionExponentialDerivative

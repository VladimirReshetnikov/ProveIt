import IPRADerivations.Analysis.GaussianBarnesCanonicalPrefactorDerivative

/-!
# Disk Lipschitz bound for the original Barnes prefactor derivative

The logarithmic derivative of the prefactor is affine with its
original named Euler–Mascheroni coefficient. Its uniform rate and
the prefactor rate yield a product estimate at independent clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorDerivativeContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalPrefactor
  (linearF quadraticCoefficientF quadraticCoefficientData quadraticF polynomialF negativeHalf correctionF quadratic_coefficient_regular)
open GaussianBarnesCanonicalPrefactorDerivative (exponentDerivativeF exponentDerivativeData derivativeF derivativeData
  exponent_derivative_regular prefactor_samples incrementGain)
open GaussianBarnesCanonicalPrefactorExponentDerivative (linearOf quadraticOf polynomialOf correctionOf twicePoint)
open GaussianBarnesCanonicalPrefactorExponentEstimate (quadraticErrorGain derivative_sample_bound)
open GaussianBarnesCanonicalPrefactorLipschitz (quadraticGain halfGain)
open GaussianBarnesCanonicalDiskBound (prefactorBound)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (add_fast multiply_fast sum_distance)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNamedDifferenceRate (rate_parameters_congr self_rate)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (qone)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "Q" => quadraticCoefficientF
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "E" => exponentDerivativeF
local notation "ed" => exponentDerivativeData
local notation "prefactorGain" => GaussianBarnesCanonicalPrefactorLipschitz.gain

def exponentDerivativeGain : PTm n := two*quadraticErrorGain

def gain (R : PTm n) : PTm n :=
  incrementGain R*prefactorGain R+prefactorBound R*exponentDerivativeGain

@[simp] theorem subst_exponentDerivativeGain {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (exponentDerivativeGain : PTm n) = exponentDerivativeGain :=
  by simp [exponentDerivativeGain,two]

private theorem subst_disk {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalPrefactorLipschitz.disk R) =
      GaussianBarnesCanonicalPrefactorLipschitz.disk (Syn.subst σ R) := by
  let L : PTm n := U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
  let G : PTm n := U GaussianGammaCanonicalExponent.gammaF zero
  let L' : PTm m := U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
  let G' : PTm m := U GaussianGammaCanonicalExponent.gammaF zero
  let r := Syn.subst σ R
  let T := (two*(R*L)+two)+(two*(R+(R*R)*(one+G))+two)
  let T' := (two*(r*L')+two)+(two*(r+(r*r)*(one+G'))+two)
  change Syn.subst σ (T+T) = T'+T'
  simp [T,T',L,G,L',G',r,one,two,GaussianStirlingConstant.nameData]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (gain R) = gain (Syn.subst σ R) := by
  have h := GaussianBarnesCanonicalPrefactorDerivative.subst_incrementGain σ R
  change Syn.subst σ (GaussianBarnesCanonicalPrefactorLipschitz.exponentGain R) =
    GaussianBarnesCanonicalPrefactorLipschitz.exponentGain (Syn.subst σ R) at h
  simp [gain,GaussianBarnesCanonicalPrefactorLipschitz.gain,subst_disk,h]

theorem exponent_rate (z w B D A M : PTm n) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A M) :
    Γ ⊢[PRAAx] independentRate E E (ed z B) (ed w D) (exponentDerivativeGain*A) M := by
  let a := twicePoint z B
  let b := twicePoint w D
  let s : PTm n := qone
  let q : PTm n := quadraticCoefficientData
  let c : PTm n := negativeHalf
  let X := A+A
  let G : PTm n := quadraticGain
  let K : PTm n := halfGain
  have hd : Γ ⊢[PRAAx] distanceBounded a b X M := sum_distance _ _ _ _ A A M hM h h
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hs := constant_regular (Γ := Γ) s
  have hc := constant_regular (Γ := Γ) c
  have hq := quadratic_coefficient_regular (Γ := Γ)
  have haq := multiply_fast C Q a q ha hq
  have hbq := multiply_fast C Q b q hb hq
  have hp := add_fast C quadraticF s (quadraticOf a) hs haq
  have hP := add_fast C quadraticF s (quadraticOf b) hs hbq
  have raw := GaussianNamedAddRate.constant_rate a b X M hM hd
  have qp := GaussianNamedMultiplyRate.independent_rate C Q C Q a q b q X M zero one G (U C b) hM (le_refl one)
    ha hq hb hq (all_samples_bounded Q q hq) (all_samples_bounded C b hb) raw (self_rate Q q hq)
  have rq : Γ ⊢[PRAAx] independentRate quadraticF quadraticF (quadraticOf a) (quadraticOf b) (G*X) M :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) qp
  have pRate := GaussianNamedAddRate.independent_rate C quadraticF C quadraticF s (quadraticOf a) s (quadraticOf b)
    zero one (G*X) M (le_refl one) hM (self_rate C s hs) rq
  have pq : Γ ⊢[PRAAx] independentRate polynomialF polynomialF (polynomialOf s a) (polynomialOf s b) (G*X) M :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) pRate
  have cRate := GaussianNamedMultiplyRate.independent_rate C polynomialF C polynomialF c (polynomialOf s a)
    c (polynomialOf s b) zero one (G*X) M (U polynomialF (polynomialOf s a)) K (le_refl one) hM hc hp hc hP
    (all_samples_bounded polynomialF _ hp) (all_samples_bounded C _ hc) (self_rate C c hc) pq
  have pc : Γ ⊢[PRAAx] independentRate correctionF correctionF (correctionOf s a) (correctionOf s b) (K*(G*X)) M :=
    rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold GaussianNamedMultiplyRate.leadingNumerator; ipra_ring)
      (by unfold GaussianNamedMultiplyRate.leadingDenominator; ipra_ring) cRate
  have l := multiply_fast C GaussianStirlingConstant.nameF s (GaussianStirlingConstant.nameData zero) hs
    (GaussianStirlingConstant.name_regular zero)
  have eRate := GaussianNamedAddRate.independent_rate linearF correctionF linearF correctionF (linearOf s) (correctionOf s a)
    (linearOf s) (correctionOf s b) zero one (K*(G*X)) M (le_refl one) hM (self_rate linearF _ l) pc
  exact rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [K,G,X,exponentDerivativeGain,quadraticErrorGain,GaussianNamedRateComposition.leadingNumerator]; ipra_ring)
    (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) eRate

theorem exponent_samples (z R B : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound E (ed z B) (incrementGain R) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) :=
    by simpa [sh,Fm.shift,Syn.shift] using hz.shift
  have h : Γ.map Fm.shift ⊢[PRAAx] GaussianRationalMetric.bounded (ap2 E (var 0) (ed (sh z) (sh B))) (incrementGain (sh R)) one :=
    derivative_sample_bound (var 0) (sh z) (sh R) (sh B) hs.andE₁ hs.andE₂
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,
    GaussianBarnesCanonicalPrefactorDerivative.subst_exponentDerivativeData,
    GaussianBarnesCanonicalPrefactorDerivative.subst_incrementGain] using h

theorem rate (z w R B D A M : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R D) (hM : Γ ⊢[PRAAx] le one M)
    (h : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w D) A M) :
    Γ ⊢[PRAAx] independentRate derivativeF derivativeF (derivativeData z B) (derivativeData w D) (gain R*A) M := by
  have full := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator
    P E P E (pd z B) (ed z B) (pd w D) (ed w D) (prefactorGain R*A) (exponentDerivativeGain*A)
    M (incrementGain R) (prefactorBound R) hM
    (GaussianBarnesCanonicalPrefactor.regular z B) (exponent_derivative_regular z B)
    (GaussianBarnesCanonicalPrefactor.regular w D) (exponent_derivative_regular w D)
    (exponent_samples z R B hz) (prefactor_samples w R D hw)
    (GaussianBarnesCanonicalPrefactorLipschitz.independent_rate z w R B D A M hz hw hM h) (exponent_rate z w B D A M hM h)
  exact rate_parameters_congr _ _ _ _ _ _ _ _ (by unfold gain; ipra_ring) (.eqRefl _) full

theorem actual_Barnes_prefactor_derivative_disk_Lipschitz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let D := var 4
     let A := var 5
     let M := var 6
     (source z R B ⋏ (source w R D ⋏ (le one M ⋏ distanceBounded (ofGaussian z B) (ofGaussian w D) A M))) ⟶
       independentRate derivativeF derivativeF (derivativeData z B) (derivativeData w D) (gain R*A) M) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorDerivativeContinuity

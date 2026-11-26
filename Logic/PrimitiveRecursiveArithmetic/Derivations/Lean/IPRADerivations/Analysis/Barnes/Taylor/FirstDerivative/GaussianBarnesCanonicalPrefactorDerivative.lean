import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorExponentEstimate
import IPRADerivations.Analysis.Exponential.Names.GaussianNamedExponentialTaylorTransport

/-!
# First-order estimate for the original Barnes prefactor

The original prefactor is the product of two literal sampled
exponentials. Its first-order term retains that product and both fixed
named constants from the original quadratic exponent.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorDerivative

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalDiskBound (radius_le prefactorBound prefactor_sample_bound)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalPrefactor (nameF data combinedF combinedData combined regular)
open GaussianBarnesCanonicalPrefactorInverse (exponentF exponentData exponentRadius exponent_input)
open GaussianBarnesCanonicalPrefactorLipschitz (disk exponentGain)
open GaussianBarnesCanonicalPrefactorExponentEstimate (quadraticErrorGain increment_sample_bound derivative_sample_bound)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "E" => exponentF
local notation "P" => nameF
local notation "pd" => data
local notation "C" => constantF
local notation "dD" => GaussianBarnesCanonicalPrefactorExponentDerivative.derivativeData
local notation "iD" => GaussianBarnesCanonicalPrefactorExponentDerivative.incrementData
local notation "tD" => GaussianBarnesCanonicalPrefactorExponentDerivative.linearData

abbrev incrementF : PR 2 := Diff P P
abbrev exponentDerivativeF : PR 2 := E
abbrev derivativeF : PR 2 := multiplyF P exponentDerivativeF
abbrev linearF : PR 2 := multiplyF C derivativeF

def incrementData (z h B : PTm n) : PTm n := dd (pd (add z h) B) (pd z B)
def exponentDerivativeData (z B : PTm n) : PTm n := dD z B
def derivativeData (z B : PTm n) : PTm n := multiplyData P E (pd z B) (exponentDerivativeData z B)
def linearData (z h B : PTm n) : PTm n := multiplyData C derivativeF (ofGaussian h B) (derivativeData z B)
def incrementGain (R : PTm n) : PTm n := exponentGain R
def errorGain (R : PTm n) : PTm n := GaussianNamedExponentialTaylorTransport.numerator (disk R) (incrementGain R) quadraticErrorGain
def errorNumerator (R H : PTm n) : PTm n := errorGain R*H*H
def derivativeBound (R : PTm n) : PTm n := prefactorBound R*incrementGain R

@[simp] theorem subst_incrementData {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (incrementData z h B) = incrementData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) := by simp [incrementData]
@[simp] theorem subst_exponentDerivativeData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (exponentDerivativeData z B) = exponentDerivativeData (Syn.subst σ z) (Syn.subst σ B) := by simp [exponentDerivativeData]
@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (z B : PTm n) :
    Syn.subst σ (derivativeData z B) = derivativeData (Syn.subst σ z) (Syn.subst σ B) := by simp [derivativeData]
@[simp] theorem subst_linearData {m : ℕ} (σ : Fin n → PTm m) (z h B : PTm n) :
    Syn.subst σ (linearData z h B) = linearData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) := by simp [linearData]
@[simp] theorem subst_incrementGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (incrementGain R) = incrementGain (Syn.subst σ R) := by
  simp [incrementGain,exponentGain,GaussianBarnesCanonicalPrefactorLipschitz.linearGain,
    GaussianBarnesCanonicalPrefactorLipschitz.quadraticGain,GaussianBarnesCanonicalPrefactorLipschitz.halfGain,
    GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,GaussianBarnesCanonicalPrefactor.negativeHalf,one,two]
private theorem subst_prefactor_radius {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (GaussianBarnesCanonicalDiskBound.prefactorRadius R) =
      GaussianBarnesCanonicalDiskBound.prefactorRadius (Syn.subst σ R) := by
  let L : PTm n := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData LeanProofs.ConciseIPRA.PTm.zero)
  let G : PTm n := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF LeanProofs.ConciseIPRA.PTm.zero
  let L' : PTm m := GaussianNameBounds.U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData LeanProofs.ConciseIPRA.PTm.zero)
  let G' : PTm m := GaussianNameBounds.U GaussianGammaCanonicalExponent.gammaF LeanProofs.ConciseIPRA.PTm.zero
  let r := Syn.subst σ R
  change Syn.subst σ ((two*(R*L)+two)+(two*(R+(R*R)*(one+G))+two)) =
    (two*(r*L')+two)+(two*(r+(r*r)*(one+G'))+two)
  simp [L,G,L',G',r,one,two,GaussianStirlingConstant.nameData]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (errorGain R) = errorGain (Syn.subst σ R) := by simp [errorGain,disk,subst_prefactor_radius]
@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (R H : PTm n) :
    Syn.subst σ (errorNumerator R H) = errorNumerator (Syn.subst σ R) (Syn.subst σ H) := by simp [errorNumerator]
@[simp] theorem subst_derivativeBound {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (derivativeBound R) = derivativeBound (Syn.subst σ R) := by simp [derivativeBound]

theorem exponent_derivative_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN exponentDerivativeF (exponentDerivativeData z B) :=
  GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _

theorem derivative_regular (z B : PTm n) : Γ ⊢[PRAAx] pointCN derivativeF (derivativeData z B) :=
  multiply_fast _ _ _ _ (regular z B) (exponent_derivative_regular z B)

theorem prefactor_samples (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound P (pd z B) (prefactorBound R) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [sh,Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,GaussianBarnesCanonicalPrefactor.subst_data,
    GaussianBarnesCanonicalDiskBound.subst_prefactorBound] using prefactor_sample_bound (var 0) (sh z) (sh R) (sh B) hs

theorem derivative_samples (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound derivativeF (derivativeData z B) (derivativeBound R) := by
  have hd : Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound E (dD z B) (incrementGain R) := by
    refine .allI ?_
    let sh (t : PTm n) := Syn.shift t
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) :=
      by simpa [sh,Fm.shift,Syn.shift] using h.shift
    have d : Γ.map Fm.shift ⊢[PRAAx] bounded (ap2 E (var 0) (dD (sh z) (sh B))) (incrementGain (sh R)) one :=
      derivative_sample_bound (var 0) (sh z) (sh R) (sh B) hs.andE₁ hs.andE₂
    simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,subst_incrementGain,
      GaussianBarnesCanonicalPrefactorExponentDerivative.subst_derivativeData] using d
  exact GaussianNamedBoundedProductObservation.sample_bounds P E _ _ _ _ (prefactor_samples z R B h) hd

private theorem small_source (z h R B H : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) (hs : Γ ⊢[PRAAx] le (incrementGain R*H) B) :
    Γ ⊢[PRAAx] GaussianNamedExponentialLinearRate.source E (iD z h B) (incrementGain R*H) B := by
  refine .andI hz.andE₁ (.andI hs (.andI (GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _) (.allI ?_)))
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift
  have hw' : Δ ⊢[PRAAx] source (add (sh z) (sh h)) (sh R) (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hw.shift
  have hh' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh h) (sh H) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hh.shift
  let a := ofGaussian (sh h) (sh B)
  let b := GaussianBarnesCanonicalPrefactorExponentDerivative.squareStep (sh z) (sh h) (sh B)
  have hd : Δ ⊢[PRAAx] bounded (ap2 E (var 0) (iD (sh z) (sh h) (sh B))) (incrementGain (sh R)*sh H) (sh B) :=
    increment_sample_bound (var 0) (sh z) (sh h) (sh R) (sh B) (sh H) hz'.andE₁ hz'.andE₂ hw'.andE₂ hh'
  have c : Δ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 E (var 0) (iD (sh z) (sh h) (sh B))) :=
    GaussianNameArithmetic.add_canonical GaussianBarnesCanonicalPrefactor.linearF GaussianBarnesCanonicalPrefactor.correctionF
      (GaussianBarnesCanonicalPrefactorExponentDerivative.linearOf a)
      (GaussianBarnesCanonicalPrefactorExponentDerivative.correctionOf a b) (var 0)
  simpa only [GaussianNamedExponentialLinearRate.smallSamples,Syn.shift,sh,subst_incrementGain,
    GaussianBarnesCanonicalPrefactorExponentDerivative.subst_incrementData,PTm.subst_mul] using Prf.andI hd c

private theorem linear_cross (z h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent linearF (multiplyF combinedF E) (linearData z h B)
      (multiplyData combinedF E (combinedData z B) (tD z h B)) := by
  let a := ofGaussian h B
  let x := pd z B
  let y := dD z B
  let v := tD z h B
  let u := combinedData z B
  have ha := constant_regular (Γ := Γ) a
  have hx := regular (Γ := Γ) z B
  have hy := exponent_derivative_regular (Γ := Γ) z B
  have hu : Γ ⊢[PRAAx] pointCN combinedF u := GaussianRadiusExponentialName.name_regular _ _ _ (exponent_input z B)
  have hv : Γ ⊢[PRAAx] pointCN E v := GaussianBarnesCanonicalPrefactorExponentDerivative.regular _ _
  have swap := GaussianNameRingLaws.multiply_commutative C derivativeF a (derivativeData z B) ha (derivative_regular z B)
  have group := GaussianNameRingLaws.multiply_associative P E C x y a hx hy ha
  have comm := GaussianNameRingLaws.multiply_commutative E C y a hy ha
  have bind := GaussianBarnesCanonicalPrefactorExponentDerivative.linear_factor z h B hB
  have finish := GaussianGammaAdjacentCutoff.multiply_cross P combinedF (multiplyF E C) E x u (multiplyData E C y a) v
    hx hu (multiply_fast _ _ _ _ hy ha) hv (combined z B) (cross_trans _ _ _ _ _ _ comm bind)
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ group finish)

theorem rate (z h R B H : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) (hsmall : Γ ⊢[PRAAx] le (incrementGain R*H) B) :
    Γ ⊢[PRAAx] independentRate incrementF linearF (incrementData z h B) (linearData z h B) (errorNumerator R H) (B*B) := by
  let w := add z h
  let x := exponentData z B
  let y := iD z h B
  let v := exponentData w B
  let t := tD z h B
  let R₀ := exponentRadius z B
  let R₁ := exponentRadius w B
  let S := disk R
  let A := incrementGain R*H
  let K : PTm n := quadraticErrorGain*H*H
  let W := GaussianNamedExponentialTaylorTransport.numerator S A K
  have hB := hz.andE₁
  have hD := positive_product _ _ hB hB
  have hx := exponent_input (Γ := Γ) z B
  have hv := exponent_input (Γ := Γ) w B
  have hS : Γ ⊢[PRAAx] le R₀ S := add_le_add₂ (radius_le z R B hz) (radius_le z R B hz)
  have hR := le_trans (le_trans (GaussianBarnesCanonicalPrefactor.radius_positive z B) (le_add_right _ _)) hS
  have ex := GaussianExponentialRadiusIndependence.input_widen E R₀ S x hx hS
  have small := small_source z h R B H hz hw hh hsmall
  have ht := GaussianBarnesCanonicalPrefactorExponentDerivative.regular (Γ := Γ) (ofGaussian h B)
    (GaussianBarnesCanonicalPrefactorExponentDerivative.linearSquare z h B)
  have sum := GaussianBarnesCanonicalPrefactorExponentDerivative.increment_add z h B hB
  have rem := GaussianBarnesCanonicalPrefactorExponentEstimate.rate z h B H hB hh
  have base := GaussianNamedExponentialTaylorTransport.rate E E E S R₀ R₁ x v y t A B K hR ex hx hv small ht sum rem
  have l := GaussianNamedDifferenceQuotientProperness.difference_proper P combinedF P combinedF
    (pd w B) (combinedData w B) (pd z B) (combinedData z B) (regular w B)
    (GaussianRadiusExponentialName.name_regular E R₁ v hv) (regular z B)
    (GaussianRadiusExponentialName.name_regular E R₀ x hx) (combined w B) (combined z B)
  have moved := GaussianNamedRateTransport.transport (Diff combinedF combinedF) (multiplyF combinedF E) incrementF linearF
    (dd (combinedData w B) (combinedData z B)) (multiplyData combinedF E (combinedData z B) t)
    (incrementData z h B) (linearData z h B) W (B*B) hD base l (linear_cross z h B hB)
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [W,S,A,K,errorNumerator,errorGain,GaussianNamedExponentialTaylorTransport.numerator]; ipra_ring)
    (.eqRefl _) moved

theorem actual_Barnes_prefactor_first_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let H := var 4
     (source z R B ⋏ (source (add z h) R B ⋏
      (ComplexLogarithmRemainder.bounded h H ⋏ le (incrementGain R*H) B))) ⟶
      independentRate incrementF linearF (incrementData z h B) (linearData z h B)
        (errorNumerator R H) (B*B)) :=
  closeUniv 5 (.impI (rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefactorDerivative

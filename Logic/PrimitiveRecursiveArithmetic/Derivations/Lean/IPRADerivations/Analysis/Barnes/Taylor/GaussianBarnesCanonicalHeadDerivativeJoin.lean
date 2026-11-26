import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHeadExponentialFactors
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHeadPolynomialQuotient
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalHeadCorrectionDerivative
import IPRADerivations.Analysis.Names.Rates.GaussianNamedNativeProductDerivativeRate

/-!
# Product rule for the original finite kept Barnes head

Use the exact base-power times correction-exponential factorization.
The polynomial quotient estimate is already certified for arbitrary
points of the disk. The correction-exponential quotient and bounds
are separate inputs to the join. The divisor throughout is the
Gaussian displacement, so this join includes zeros of the head.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivativeJoin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalHead (source headData)
open GaussianBarnesCanonicalHeadExponentialFactors (exponentData)
open GaussianBarnesCanonicalHeadPolynomialDerivative (input valueCap errorGain powerSlope)
open GaussianBarnesCanonicalHeadPolynomialQuotient (continuityGain)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianL1 (norm1)
open GaussianNameArithmetic (add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Head" => GaussianBarnesCanonicalHead.nameF
local notation "Factorization" => GaussianBarnesCanonicalHeadExponentialFactors.nameF
local notation "factorizationData" => GaussianBarnesCanonicalHeadExponentialFactors.data
local notation "Ex" => GaussianRadiusExponentialName.nameF constantF
local notation "CF" => GaussianBarnesCanonicalHeadCorrectionDerivative.slope
local notation "QF" => GaussianNamedDifferenceQuotient.nameF
local notation "qd" => GaussianNamedDifferenceQuotient.data

abbrev expDerivativeF : PR 2 := multiplyF Ex constantF
def expDerivativeData (z B N : PTm n) : PTm n := multiplyData Ex constantF (exponentData z B N) (CF z B N)
abbrev derivativeF : PR 2 := GaussianNamedNativeProductDerivativeRate.derivativeF constantF Ex constantF expDerivativeF
def derivativeData (z B N : PTm n) : PTm n :=
  GaussianNamedNativeProductDerivativeRate.derivativeData constantF Ex constantF expDerivativeF
    (powerProduct z B N) (exponentData z B N) (powerSlope z B N) (expDerivativeData z B N)

def gain (R N A P Y : PTm n) : PTm n :=
  valueCap R N*A + P*continuityGain R N + Y*(two*errorGain R N)

@[simp] theorem subst_expDerivativeData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (expDerivativeData z B N) = expDerivativeData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [expDerivativeData,exponentData,GaussianGammaFiniteApproximantName.exponentialInputData]

@[simp] theorem subst_derivativeData {m : ℕ} (σ : Fin n → PTm m) (z B N : PTm n) :
    Syn.subst σ (derivativeData z B N) = derivativeData (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [derivativeData,GaussianNamedNativeProductDerivativeRate.derivativeData,
    exponentData,GaussianGammaFiniteApproximantName.exponentialInputData]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R N A P Y : PTm n) :
    Syn.subst σ (gain R N A P Y) = gain (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ A)
      (Syn.subst σ P) (Syn.subst σ Y) := by simp [gain,two]

theorem exponential_regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN Ex (exponentData z B N) :=
  GaussianRadiusExponentialName.name_regular constantF _ _
    (GaussianGammaFiniteApproximantName.exponential_input constantF _ (constant_regular _))

theorem exponential_derivative_regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN expDerivativeF (expDerivativeData z B N) :=
  multiply_fast _ _ _ _ (exponential_regular z B N) (constant_regular _)

theorem regular (z B N : PTm n) : Γ ⊢[PRAAx] pointCN derivativeF (derivativeData z B N) :=
  add_fast _ _ _ _
    (multiply_fast _ _ _ _ (exponential_derivative_regular z B N) (constant_regular _))
    (multiply_fast _ _ _ _ (exponential_regular z B N) (constant_regular _))

theorem head_samples_bound (z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound Head (headData z R B N) (GaussianBarnesCanonicalHead.cap R zero N) := by
  refine .allI ?_
  let sh (x : PTm n) := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using hz.shift
  simpa only [sampleBound,Syn.shift,sh,GaussianBarnesCanonicalHead.headData,
    GaussianBarnesCanonicalHead.subst_data,GaussianBarnesCanonicalHead.subst_cap,
    ConciseIPRA.PTm.subst_zero] using
    GaussianBarnesCanonicalHead.sample_bound (var 0) (sh z) (sh R) (sh B) zero (sh N) hs

theorem rate (z h R B N A P Y : PTm n) (hs : Γ ⊢[PRAAx] input z h R B (norm1 h))
    (hh : Γ ⊢[PRAAx] le one (normSq h)) (hsmall : Γ ⊢[PRAAx] le (norm1 h) B)
    (hp : Γ ⊢[PRAAx] sampleBound expDerivativeF (expDerivativeData z B N) P)
    (hy : Γ ⊢[PRAAx] sampleBound Ex (exponentData z B N) Y)
    (hex : Γ ⊢[PRAAx] independentRate (QF Ex Ex) expDerivativeF
      (qd Ex Ex (exponentData (add z h) B N) (exponentData z B N) h B)
      (expDerivativeData z B N) (A*norm1 h) B) : Γ ⊢[PRAAx]
    independentRate (QF Head Head) derivativeF
      (qd Head Head (headData (add z h) R B N) (headData z R B N) h B)
      (derivativeData z B N) (gain R N A P Y*norm1 h) B := by
  let H := norm1 h
  let z' := add z h
  let x1 := powerProduct z' B N
  let x0 := powerProduct z B N
  let y1 := exponentData z' B N
  let y0 := exponentData z B N
  let u := powerSlope z B N
  let v := expDerivativeData z B N
  have hB := hs.andE₁
  have hz : Γ ⊢[PRAAx] source z R B := .andI hB hs.andE₂.andE₁
  have hz' : Γ ⊢[PRAAx] source z' R B := .andI hB hs.andE₂.andE₂.andE₁
  have pr := GaussianNamedNativeProductDerivativeRate.rate constantF Ex constantF expDerivativeF
    x1 x0 y1 y0 u v h B (A*H) (two*errorGain R N*H) (continuityGain R N*H) B P (valueCap R N) Y
    (constant_regular x1) (constant_regular x0) (exponential_regular z' B N) (exponential_regular z B N)
    (constant_regular u) (exponential_derivative_regular z B N) (.andI hB hh) hB hp
    (GaussianBarnesCanonicalHeadPolynomialQuotient.value_sample_bound z' R B N hB hs.andE₂.andE₂.andE₁) hy hex
    (GaussianBarnesCanonicalHeadPolynomialQuotient.quotient_rate z h R B N hs hh)
    (GaussianBarnesCanonicalHeadPolynomialQuotient.continuity z h R B H N hs hsmall)
  let G := gain R N A P Y
  let d := derivativeData z B N
  let k := qd Factorization Factorization (factorizationData z' B N) (factorizationData z B N) h B
  let k' := qd Head Head (headData z' R B N) (headData z R B N) h B
  have budget : Γ ⊢[PRAAx] G*H ≐ valueCap R N*(A*H)+P*(continuityGain R N*H)+Y*(two*errorGain R N*H) := by
    change Γ ⊢[PRAAx] (valueCap R N*A+P*continuityGain R N+Y*(two*errorGain R N))*H ≐
      valueCap R N*(A*H)+P*(continuityGain R N*H)+Y*(two*errorGain R N*H)
    ipra_ring
  have narrower : Γ ⊢[PRAAx] independentRate (QF Factorization Factorization) derivativeF k d (G*H) B :=
    GaussianNamedRateRadius.weaken (QF Factorization Factorization) derivativeF k d _ B (G*H) B hB hB
      (le_of_eq_add (d := zero) ((congrMul budget (.eqRefl B)).eqTrans (add_zero _).eqSymm)) pr
  have qcross := GaussianNamedDifferenceQuotientProperness.proper Head Factorization Head Factorization
    (headData z' R B N) (factorizationData z' B N) (headData z R B N) (factorizationData z B N) h B
    (GaussianBarnesCanonicalHead.regular z' R B zero N hz')
    (GaussianBarnesCanonicalHeadExponentialFactors.regular z' B N)
    (GaussianBarnesCanonicalHead.regular z R B zero N hz)
    (GaussianBarnesCanonicalHeadExponentialFactors.regular z B N)
    (GaussianBarnesCanonicalHeadExponentialFactors.head_cross z' R B N hz')
    (GaussianBarnesCanonicalHeadExponentialFactors.head_cross z R B N hz)
  exact GaussianNamedRateTransport.transport (QF Factorization Factorization) derivativeF (QF Head Head) derivativeF k d k' d
    (G*H) B hB narrower qcross (cross_refl derivativeF d (regular z B N))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivativeJoin

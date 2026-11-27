import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.FiniteFactors.GaussianBarnesCanonicalHeadDerivative
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadCorrectionContinuity
import IPRADerivations.Analysis.Polynomials.Horner.GaussianRationalSyntheticSlopeLipschitz
import IPRADerivations.Analysis.Names.FiniteOperations.Sums.GaussianNamedBoundedSumObservation

/-!
# Uniform disk continuity of the original finite Barnes head derivative

Use the actual derivative from the finite product rule. Both polynomial
legs are compared at the original rational arguments. The correction
exponential retains its original dynamic radii, and the result permits
independent observation clocks and different denominators.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivativeContinuity

open_ipra
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalHead (source)
open GaussianBarnesCanonicalHeadDerivative (correctionDerivativeCap correction_derivative_samples)
open GaussianBarnesCanonicalHeadDerivativeJoin (derivativeF derivativeData expDerivativeF expDerivativeData)
open GaussianBarnesCanonicalHeadExponentialFactors (exponentData)
open GaussianBarnesCanonicalHeadPolynomial (polynomial degree polynomial_length original_evaluation)
open GaussianBarnesCanonicalHeadPolynomialDerivative (valueCap slopeCap powerSlope argument_bound slope_bound)
open GaussianEulerNamedPowerScalingPowerFrozen (constant_bound multiply_same_denominator)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => constantF
local notation "E" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponentialF
local notation "D" => expDerivativeF
local notation "S" => GaussianBarnesCanonicalHeadCorrectionDerivative.slope
local notation "eCap" => GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponentialBound
local notation "eGain" => GaussianBarnesCanonicalHeadCorrectionContinuity.gain

def polynomialValueGain (R N : PTm n) : PTm n :=
  GaussianRationalSyntheticSlopeLipschitz.valueGain (polynomial N) (succ R)
def polynomialSlopeGain (R N : PTm n) : PTm n :=
  GaussianRationalSyntheticSlopeLipschitz.slopeGain (polynomial N) (degree N) (succ R)
def correctionSlopeCap (R N : PTm n) : PTm n := N*(R+one)
def correctionDerivativeGain (R N : PTm n) : PTm n := correctionSlopeCap R N*eGain R N+eCap R N*N

def gain (R N : PTm n) : PTm n :=
  (valueCap R N*correctionDerivativeGain R N+correctionDerivativeCap R N*polynomialValueGain R N) +
    (slopeCap R N*eGain R N+eCap R N*polynomialSlopeGain R N)

def cap (R N : PTm n) : PTm n := correctionDerivativeCap R N*valueCap R N+eCap R N*slopeCap R N

@[simp] theorem subst_polynomialValueGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (polynomialValueGain R N) = polynomialValueGain (Syn.subst σ R) (Syn.subst σ N) := by
  simp [polynomialValueGain]

@[simp] theorem subst_polynomialSlopeGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (polynomialSlopeGain R N) = polynomialSlopeGain (Syn.subst σ R) (Syn.subst σ N) := by
  simp [polynomialSlopeGain]

@[simp] theorem subst_correctionSlopeCap {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (correctionSlopeCap R N) = correctionSlopeCap (Syn.subst σ R) (Syn.subst σ N) := by
  simp [correctionSlopeCap,one]

@[simp] theorem subst_correctionDerivativeGain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (correctionDerivativeGain R N) = correctionDerivativeGain (Syn.subst σ R) (Syn.subst σ N) := by
  simp [correctionDerivativeGain]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (gain R N) = gain (Syn.subst σ R) (Syn.subst σ N) := by simp [gain]

@[simp] theorem subst_cap {m : ℕ} (σ : Fin n → PTm m) (R N : PTm n) :
    Syn.subst σ (cap R N) = cap (Syn.subst σ R) (Syn.subst σ N) := by simp [cap]

private theorem value_rate (z w R B C N A Q : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) A Q) :
    Γ ⊢[PRAAx] independentRate F F (powerProduct z B N) (powerProduct w C N) (polynomialValueGain R N*A) Q := by
  have core := GaussianRationalSyntheticSlopeLipschitz.value_rate (polynomial N) (ofGaussian z B) (ofGaussian w C) (succ R) A Q
    (zero_lt_succ R) (argument_bound z R B hz.andE₁ hz.andE₂) (argument_bound w R C hw.andE₁ hw.andE₂) hQ hd
  exact GaussianNamedAddRate.constant_rate _ _ _ _ hQ
    (distance_congr (original_evaluation z B N hz.andE₁) (original_evaluation w C N hw.andE₁) (.eqRefl _) (.eqRefl _) core)

private theorem polynomial_slope_rate (z w R B C N A Q : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) A Q) :
    Γ ⊢[PRAAx] independentRate F F (powerSlope z B N) (powerSlope w C N) (polynomialSlopeGain R N*A) Q :=
  GaussianNamedAddRate.constant_rate _ _ _ _ hQ
    (GaussianRationalSyntheticSlopeLipschitz.slope_rate (polynomial N) (ofGaussian z B) (ofGaussian w C)
      (degree N) (succ R) A Q (polynomial_length N) (zero_lt_succ R)
      (argument_bound z R B hz.andE₁ hz.andE₂) (argument_bound w R C hw.andE₁ hw.andE₂) hQ hd)

private theorem correction_derivative_rate (z w R B C N A Q : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) A Q)
    (he : Γ ⊢[PRAAx] independentRate E E (exponentData z B N) (exponentData w C N) (eGain R N*A) Q) :
    Γ ⊢[PRAAx] independentRate D D (expDerivativeData z B N) (expDerivativeData w C N) (correctionDerivativeGain R N*A) Q := by
  let x := exponentData z B N
  let y := exponentData w C N
  let s := S z B N
  let t := S w C N
  let P := correctionSlopeCap R N
  let M := eCap R N
  let K := eGain R N
  have hs := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.slope_bound z B N R hz.andE₁ hz.andE₂
  have left := GaussianBarnesCanonicalHeadDerivativeJoin.exponential_regular (Γ := Γ) z B N
  have right := GaussianBarnesCanonicalHeadDerivativeJoin.exponential_regular (Γ := Γ) w C N
  have hwcap := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponential_samples w C N R hw.andE₁ hw.andE₂
  have correction := GaussianNamedAddRate.constant_rate s t (N*A) Q hQ
    (GaussianBarnesCanonicalHeadCorrectionContinuity.slope_distance z w B C N A Q hQ hd)
  have rate := multiply_same_denominator E F E F x s y t (K*A) (N*A) Q P M hQ
    left (constant_regular s) right (constant_regular t) (constant_bound s P hs) hwcap he correction
  exact GaussianNamedDifferenceRate.rate_parameters_congr D D (expDerivativeData z B N) (expDerivativeData w C N)
    _ _ _ _ (by dsimp only [correctionDerivativeGain,P,M,K]; ipra_ring) (.eqRefl _) rate

private theorem sum_rate (F₁ F₂ : PR 2) (x y u v A C Q : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (ha : Γ ⊢[PRAAx] independentRate F₁ F₁ x u A Q) (hc : Γ ⊢[PRAAx] independentRate F₂ F₂ y v C Q) :
    Γ ⊢[PRAAx] independentRate (addF F₁ F₂) (addF F₁ F₂) (addData x y) (addData u v) (A+C) Q :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hQ hQ) hQ
    (le_of_eq_add (d := zero) (by dsimp only [GaussianNamedRateComposition.leadingNumerator,
      GaussianNamedRateComposition.leadingDenominator]; ipra_ring))
    (GaussianNamedAddRate.independent_rate _ _ _ _ _ _ _ _ _ _ _ _ hQ hQ ha hc)

theorem independent_rate (z w R B C N A Q : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source w R C) (hQ : Γ ⊢[PRAAx] le one Q)
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w C) A Q) :
    Γ ⊢[PRAAx] independentRate derivativeF derivativeF (derivativeData z B N) (derivativeData w C N) (gain R N*A) Q := by
  let x := exponentData z B N
  let y := exponentData w C N
  let d := expDerivativeData z B N
  let e := expDerivativeData w C N
  let p := powerProduct z B N
  let q := powerProduct w C N
  let a := powerSlope z B N
  let b := powerSlope w C N
  let X := multiplyF D F
  let Y := multiplyF E F
  let U := valueCap R N
  let V := slopeCap R N
  let W := correctionDerivativeCap R N
  let M := eCap R N
  let K := eGain R N
  let T := correctionDerivativeGain R N
  let J := polynomialValueGain R N
  let L := polynomialSlopeGain R N
  have hrX := GaussianBarnesCanonicalHeadDerivativeJoin.exponential_regular (Γ := Γ) z B N
  have hrY := GaussianBarnesCanonicalHeadDerivativeJoin.exponential_regular (Γ := Γ) w C N
  have hrD := GaussianBarnesCanonicalHeadDerivativeJoin.exponential_derivative_regular (Γ := Γ) z B N
  have hrE := GaussianBarnesCanonicalHeadDerivativeJoin.exponential_derivative_regular (Γ := Γ) w C N
  have he := GaussianBarnesCanonicalHeadCorrectionContinuity.independent_rate z w R B C N A Q hz hw hQ hd
  have hcd := correction_derivative_rate z w R B C N A Q hz hw hQ hd he
  have hvalue := value_rate z w R B C N A Q hz hw hQ hd
  have hslope := polynomial_slope_rate z w R B C N A Q hz hw hQ hd
  have bp := GaussianBarnesCanonicalHeadPolynomialQuotient.value_sample_bound z R B N hz.andE₁ hz.andE₂
  have ba := constant_bound a V (slope_bound z R B N hz.andE₁ hz.andE₂)
  have by' := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponential_samples w C N R hw.andE₁ hw.andE₂
  have be := correction_derivative_samples w R C N hw.andE₁ hw.andE₂
  have left : Γ ⊢[PRAAx] independentRate X X (multiplyData D F d p) (multiplyData D F e q) (U*(T*A)+W*(J*A)) Q :=
    multiply_same_denominator D F D F d p e q (T*A) (J*A) Q U W hQ
      hrD (constant_regular p) hrE (constant_regular q) bp be hcd hvalue
  have right : Γ ⊢[PRAAx] independentRate Y Y (multiplyData E F x a) (multiplyData E F y b) (V*(K*A)+M*(L*A)) Q :=
    multiply_same_denominator E F E F x a y b (K*A) (L*A) Q V M hQ
      hrX (constant_regular a) hrY (constant_regular b) ba by' he hslope
  have core := sum_rate X Y _ _ _ _ _ _ Q hQ left right
  have paid : Γ ⊢[PRAAx] (U*(T*A)+W*(J*A))+(V*(K*A)+M*(L*A)) ≐ gain R N*A := by
    change Γ ⊢[PRAAx] (U*(T*A)+W*(J*A))+(V*(K*A)+M*(L*A)) ≐ ((U*T+W*J)+(V*K+M*L))*A
    ipra_ring
  exact GaussianNamedDifferenceRate.rate_parameters_congr derivativeF derivativeF (derivativeData z B N)
    (derivativeData w C N) _ _ _ _ paid (.eqRefl _) core

theorem samples_bound (z R B N : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] sampleBound derivativeF (derivativeData z B N) (cap R N) := by
  let d := expDerivativeData z B N
  let x := exponentData z B N
  let p := powerProduct z B N
  let a := powerSlope z B N
  have hp := GaussianBarnesCanonicalHeadPolynomialQuotient.value_sample_bound z R B N hz.andE₁ hz.andE₂
  have ha := constant_bound a (slopeCap R N) (slope_bound z R B N hz.andE₁ hz.andE₂)
  have hd := correction_derivative_samples z R B N hz.andE₁ hz.andE₂
  have hx := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponential_samples z B N R hz.andE₁ hz.andE₂
  have left := GaussianNamedBoundedProductObservation.sample_bounds D F d p _ _ hd hp
  have right := GaussianNamedBoundedProductObservation.sample_bounds E F x a _ _ hx ha
  exact GaussianNamedBoundedSumObservation.sample_bounds (multiplyF D F) (multiplyF E F) _ _ _ _ left right

theorem actual_Barnes_kept_head_derivative_uniform_lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let z := var 0
       let w := var 1
       let R := var 2
       let B := var 3
       let C := var 4
       let N := var 5
       let A := var 6
       let Q := var 7
       (source z R B ⋏ (source w R C ⋏ (le one Q ⋏ distanceBounded (ofGaussian z B) (ofGaussian w C) A Q))) ⟶
         independentRate derivativeF derivativeF (derivativeData z B N) (derivativeData w C N) (gain R N*A) Q) :=
  closeUniv 8 (.impI (independent_rate _ _ _ _ _ _ _ _ Prf.hyp0.andE₁
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadDerivativeContinuity

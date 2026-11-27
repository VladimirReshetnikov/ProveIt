import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ExponentCoefficients.GaussianBarnesCanonicalExponentTaylorSchedule
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorExponentEstimate
import IPRADerivations.Analysis.Exponential.Names.Derivatives.GaussianNamedExponentialTaylorTransport

/-!
# A single stored Barnes exponent Taylor polynomial on a certified ball

A uniform majorant for the two prefactor observations is obtained from
the admitted radius and the displacement bound. The resulting stored
polynomial and both of its construction clocks are independent of the
particular point of evaluation.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBallSchedule

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalExponentTaylor (nameF data)
open GaussianBarnesCanonicalExponentTaylorSchedule (tailCutoff numerator denominator denominator_positive)
open GaussianBarnesCanonicalCorrectedMercatorCofinal
  (input cutoff_budget analyticDenominator scheduledNumerator scheduledDenominator)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalPrefactor
  (negativeHalf quadraticCoefficientF quadraticCoefficientData quadratic_coefficient_regular quadraticF polynomialF)
open GaussianBarnesCanonicalPrefactorExponentDerivative (square squareStep quadraticOf polynomialOf)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (multiplyModulus)
open GaussianNameBounds (U sample_bound)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian evaluate qzero positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bounded_product bounded_difference bound_congr)
open GaussianRationalSyntheticDivision (canonicalCoefficients)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "S" => GaussianStirlingConstant.nameF
local notation "sd" => GaussianStirlingConstant.nameData
local notation "Q" => quadraticCoefficientF
local notation "qd" => quadraticCoefficientData
local notation "FNum" => GaussianBarnesCanonicalExponentTaylorFrozen.numerator
local notation "FDen" => GaussianBarnesCanonicalExponentTaylorFrozen.denominator
local notation "FCost" => GaussianBarnesCanonicalExponentTaylorFrozen.cost

def squareCap (R : PTm n) : PTm n := R*R+R*R
def stepClockCap (H : PTm n) : PTm n := two*H+two
def squareClockCap (R : PTm n) : PTm n := two*squareCap R+two
def polynomialClockCap (R H : PTm n) : PTm n := two*(H+squareCap R*U Q qd)+two

def uniformCost (R H : PTm n) : PTm n :=
  num 12+stepClockCap H+U S (sd zero)+U C negativeHalf+polynomialClockCap R H+
    U C negativeHalf*(num 4+squareClockCap R+U Q qd)

def precision (p R H : PTm n) : PTm n := exponent (uniformCost R H) p

def buffer (p z R B H M : PTm n) : PTm n :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer (precision p R H) z R B (tailCutoff p R) M

def value (p z h R B H M : PTm n) : PTm n := evaluate (buffer p z R B H M) (ofGaussian h B)

theorem buffer_length (p z R B H M : PTm n) : Γ ⊢[PRAAx] length (buffer p z R B H M) ≐ succ (previous M) :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer_length _ _ _ _ _ _

theorem buffer_zero (p z R B H M : PTm n) : Γ ⊢[PRAAx] entry (buffer p z R B H M) (previous M) ≐ qzero :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer_zero _ _ _ _ _ _

theorem buffer_canonical (p z R B H M : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (buffer p z R B H M) :=
  GaussianBarnesCanonicalExponentTaylorBuffer.buffer_canonical _ _ _ _ _ _

private theorem step_bound (h B H : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H) :
    Γ ⊢[PRAAx] bounded (ofGaussian h B) H one := by
  have wider : Γ ⊢[PRAAx] le H (H*B) :=
    le_congr (LeanProofs.IPRA.Common.mul_one_right H) (.eqRefl _) (le_mul_mono (le_refl H) hB)
  exact GaussianGammaEulerHead.fraction_disk h H B hB (ComplexLogarithmRemainder.bounded_mono hh wider)

private theorem square_step_bound (z h R B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (add z h) (R*B)) :
    Γ ⊢[PRAAx] bounded (squareStep z h B) (squareCap R) one := by
  let a := ofGaussian (add z h) B
  let b := ofGaussian z B
  have ha := GaussianGammaEulerHead.fraction_disk (add z h) R B hB hw
  have hb := GaussianGammaEulerHead.fraction_disk z R B hB hz
  have left : Γ ⊢[PRAAx] bounded (square (add z h) B) (R*R) one :=
    bound_congr (.eqRefl (square (add z h) B)) (.eqRefl _) (one_mul _)
      (bounded_product a a R one R one (le_refl one) (le_refl one) ha ha)
  have right : Γ ⊢[PRAAx] bounded (square z B) (R*R) one :=
    bound_congr (.eqRefl (square z B)) (.eqRefl _) (one_mul _)
      (bounded_product b b R one R one (le_refl one) (le_refl one) hb hb)
  exact bound_congr (.eqRefl (squareStep z h B)) (by unfold squareCap; ipra_ring) (one_mul _)
    (bounded_difference _ _ _ _ _ _ (le_refl one) (le_refl one) left right)

private theorem polynomial_sample_bound (p a b A B : PTm n)
    (ha : Γ ⊢[PRAAx] bounded a A one) (hb : Γ ⊢[PRAAx] bounded b B one) :
    Γ ⊢[PRAAx] bounded (ap2 polynomialF p (polynomialOf a b)) (A+B*U Q qd) one := by
  let k := exponent two p
  let j := exponent (multiplyModulus C Q b qd) k
  have hb' : Γ ⊢[PRAAx] bounded (ap2 C j b) B one :=
    bound_congr (constant_at j b).eqSymm (.eqRefl _) (.eqRefl _) hb
  have hQ := sample_bound Q qd j (quadratic_coefficient_regular (Γ := Γ))
  have mult : Γ ⊢[PRAAx] bounded (ap2 quadraticF k (quadraticOf b)) (B*U Q qd) one :=
    bound_congr (GaussianNamedBoundedProductObservation.name_at C Q k b qd).eqSymm (.eqRefl _) (one_mul _)
      (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) hb' hQ)
  have ha' : Γ ⊢[PRAAx] bounded (ap2 C k a) A one :=
    bound_congr (constant_at k a).eqSymm (.eqRefl _) (.eqRefl _) ha
  exact bound_congr (GaussianExponentialReference.add_sample C quadraticF a (quadraticOf b) p).eqSymm (by ipra_ring) (one_mul _)
    (GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ (le_refl one) (le_refl one) ha' mult)

private theorem cost_formula (z h R B v : PTm n) :
    let a := ofGaussian h B
    let b := squareStep z h B
    Γ ⊢[PRAAx] FCost z h R B v ≐
      num 12+U C a+U S (sd zero)+U C negativeHalf+U polynomialF (polynomialOf a b)+
        U C negativeHalf*(num 4+U C b+U Q qd) := by
  let a := ofGaussian h B
  let b := squareStep z h B
  let u := U C a
  let s : PTm n := U S (sd zero)
  let v' := U C b
  let g := U Q (qd : PTm n)
  let c := U C (negativeHalf : PTm n)
  let w := U polynomialF (polynomialOf a b)
  let L := (u+s+one)+(zero*s+u*zero)
  let J := (v'+g+one)+(zero*g+v'*zero)
  let K := (c+w+one)+(zero*w+c*(GaussianNameRingLaws.three+(zero+J)))
  change Γ ⊢[PRAAx] one+(GaussianNameRingLaws.three+((GaussianNameRingLaws.three+
    ((GaussianNameRingLaws.three+(L+K))+zero))+zero)) ≐ num 12+u+s+c+w+c*(num 4+v'+g)
  dsimp only [L,J,K,GaussianNameRingLaws.three]
  ipra_ring

theorem cost_bound (z h R B H v M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    Γ ⊢[PRAAx] le (FCost z h R B v) (uniformCost R H) := by
  let a := ofGaussian h B
  let b := squareStep z h B
  let s : PTm n := U S (sd zero)
  let c := U C (negativeHalf : PTm n)
  let g := U Q (qd : PTm n)
  have hB := hs.andE₁.andE₁
  have ha := step_bound h B H hB hs.andE₂.andE₂.andE₁
  have hb := square_step_bound z h R B hB hs.andE₁.andE₂ hs.andE₂.andE₁.andE₂
  have ua : Γ ⊢[PRAAx] le (U C a) (stepClockCap H) :=
    GaussianNamedExponentialTaylorTransport.radius_from_sample C a H
      (bound_congr (constant_at zero a).eqSymm (.eqRefl _) (.eqRefl _) ha)
  have ub : Γ ⊢[PRAAx] le (U C b) (squareClockCap R) :=
    GaussianNamedExponentialTaylorTransport.radius_from_sample C b (squareCap R)
      (bound_congr (constant_at zero b).eqSymm (.eqRefl _) (.eqRefl _) hb)
  have up : Γ ⊢[PRAAx] le (U polynomialF (polynomialOf a b)) (polynomialClockCap R H) :=
    GaussianNamedExponentialTaylorTransport.radius_from_sample polynomialF (polynomialOf a b) (H+squareCap R*g)
      (polynomial_sample_bound zero a b H (squareCap R) ha hb)
  have first := add_le_add₂ (add_le_add_right c (add_le_add_right s (add_le_add₂ (le_refl (num 12)) ua))) up
  have last := le_mul_mono (le_refl c) (add_le_add_right g (add_le_add₂ (le_refl (num 4)) ub))
  exact le_congr (cost_formula z h R B v).eqSymm (.eqRefl _) (add_le_add₂ first last)

theorem precision_budget (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    Γ ⊢[PRAAx] le (GaussianBarnesCanonicalExponentTaylorSchedule.prefactorCost p z h R B M*unit p) (unit (precision p R H)) :=
  le_trans (mul_le_mul_right (unit p) (cost_bound z h R B H _ M hs)) (query_budget (uniformCost R H) p)

private theorem radius_comparison (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    let q := precision p R H
    let r := tailCutoff p R
    Γ ⊢[PRAAx] le (FNum p q z h R B H r M*denominator p R B M)
      (numerator p R B H M*FDen p q R B M) := by
  let q := precision p R H
  let D := analyticDenominator (previous M) R B
  let E := denominator p R B M
  let V := unit q
  let A := scheduledNumerator p (previous M) R B H
  have joined := add_le_add_right (A*V*E) (mul_le_mul_right (D*E) (precision_budget p z h R B H M hs))
  exact le_congr (by
    dsimp only [D,E,denominator,scheduledDenominator,V,A,GaussianBarnesCanonicalExponentTaylorSchedule.prefactorCost,
      GaussianBarnesCanonicalExponentTaylorFrozen.numerator,GaussianNamedRateComposition.leadingNumerator,q]
    ipra_ring) (by
      dsimp only [D,E,denominator,scheduledDenominator,V,A,numerator,GaussianBarnesCanonicalExponentTaylorFrozen.denominator,
        GaussianNamedRateComposition.leadingDenominator,scheduledNumerator,GaussianNamedRateComposition.leadingNumerator,q]
      ipra_ring) joined

theorem rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input (previous M) z h R B H) :
    Γ ⊢[PRAAx] independentRate nameF constantF (data z h R B) (value p z h R B H M)
      (numerator p R B H M) (denominator p R B M) := by
  let q := precision p R H
  let r := tailCutoff p R
  have hD := denominator_positive p R B M hs.andE₁.andE₁
  have oldPos : Γ ⊢[PRAAx] le one (FDen p q R B M) := positive_product _ _ hD (unit_positive q)
  have raw := GaussianBarnesCanonicalExponentTaylorHorner.rate_of_cutoff p q z h R B H r M hs (cutoff_budget p R)
  exact GaussianNamedRateRadius.weaken nameF constantF (data z h R B) (value p z h R B H M)
    (FNum p q z h R B H r M) (FDen p q R B M) (numerator p R B H M) (denominator p R B M)
    oldPos hD (radius_comparison p z h R B H M hs) raw

theorem actual_Barnes_exponent_Taylor_ball_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     input (previous M) z h R B H ⟶ independentRate nameF constantF (data z h R B) (value p z h R B H M)
       (numerator p R B H M) (denominator p R B M)) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBallSchedule

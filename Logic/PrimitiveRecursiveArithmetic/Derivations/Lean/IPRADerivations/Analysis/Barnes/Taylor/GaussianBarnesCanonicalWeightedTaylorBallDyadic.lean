import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalWeightedTaylorBall
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# A separated dyadic error for the original weighted Barnes Taylor ball

The leading error has one term for the schedule and one for the Taylor
degree. Both constants depend only on the certified center and disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallDyadic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalExponentTaylorWeightedMass (massCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalWeightedTaylorBall (nameF approxData headMass)
open GaussianBarnesCanonicalWeightedTaylorBallSource (input stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "G" => GaussianBarnesCanonicalCenteredProductRate.gain
local notation "K" => GaussianBarnesCanonicalTaylorRecomposition.capGain
local notation "E" => GaussianRadiusExponentialName.nameF GaussianBarnesCanonicalSingleExponential.exponentF
local notation "baseData" => GaussianBarnesCanonicalCenteredExponentialShift.baseData

private def centralCap (z R B : PTm n) : PTm n := GaussianNameBounds.U E (baseData z R B)
private def exponentialCap (R : PTm n) : PTm n := pw (num 3) (massCap R)

def precisionGain (z R B : PTm n) : PTm n := G z R B*K (num 3)
def degreeGain (z R B : PTm n) : PTm n :=
  precisionGain z R B+G z R B*(two+exponentialCap R)+centralCap z R B*(headMass z R B*exponentialCap R)

def numerator (p z R B M : PTm n) : PTm n :=
  precisionGain z R B*(two*unit (succ (previous M)))+degreeGain z R B*unit p

def denominator (p M : PTm n) : PTm n := unit p*unit (succ (previous M))

private theorem half_power (X B j : PTm n) (h : Γ ⊢[PRAAx] le (two*X) B) :
    Γ ⊢[PRAAx] le (unit j*pw X j) (pw B j) :=
  le_congr (AnalyticNumberTheory.LocalFactor.pw_mul_base two X j) (.eqRefl _) (pw_le_pw j h)

private theorem analytic_half_power (R B H M : PTm n) (hs : Γ ⊢[PRAAx] le (num 4*H) B) :
    Γ ⊢[PRAAx] le (unit (succ (previous M))*GaussianBarnesCanonicalCorrectedMercator.numerator (previous M) H)
      (GaussianBarnesCanonicalCorrectedMercatorCofinal.analyticDenominator (previous M) R B) := by
  let j := succ (previous M)
  let b := pw B j
  let t := pw (two*H) j
  have h2 : Γ ⊢[PRAAx] le (two*(two*H)) B := le_congr (by ipra_ring) (.eqRefl _) hs
  have hp : Γ ⊢[PRAAx] le (unit j*t) b := half_power (two*H) B j h2
  have hj : Γ ⊢[PRAAx] le two j :=
    le_trans (Common.succ_le_succ (zero_lt_succ M)) (le_succ_self _)
  have twoBound : Γ ⊢[PRAAx] le (unit j*(two*t)) (two*b) :=
    le_congr (by ipra_ring) (.eqRefl _) (Common.mul_le_mul (le_refl two) hp)
  have jBound : Γ ⊢[PRAAx] le (two*b) (j*b) := mul_le_mul_right b hj
  have initialBound : Γ ⊢[PRAAx] le (j*b) ((j*b)*initial R) := by
    have e : Γ ⊢[PRAAx] (j*b)*one ≐ j*b := by ipra_ring
    exact le_congr e (.eqRefl _) (Common.mul_le_mul (le_refl _) (initial_positive R))
  exact le_trans twoBound (le_trans jBound initialBound)

private theorem radius_comparison (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] le (GaussianBarnesCanonicalWeightedTaylorBall.numerator p z R B H M*denominator p M)
      (numerator p z R B M*GaussianBarnesCanonicalWeightedTaylorBall.denominator p R B M) := by
  let m := previous M
  let j := succ m
  let U := unit p
  let W := unit j
  let L := massCap R
  let H4 := num 4*H
  let b := pw B j
  let t := two*pw (two*H) j
  let Q := j*b*initial R
  let D := U*Q
  let g := G z R B
  let k := K (num 3 : PTm n)
  let P := exponentialCap R
  let A := headMass z R B
  let F := centralCap z R B
  let u := pw H4 j
  let v := pw L j
  have hA : Γ ⊢[PRAAx] le (W*t) Q := analytic_half_power R B H M hs.andE₂.andE₁
  have hL : Γ ⊢[PRAAx] le one L :=
    le_trans (le_succ_self one) (le_add_left two (GaussianBarnesCanonicalExponentTaylorMass.linearCap R+
      GaussianBarnesCanonicalExponentTaylorMass.squareCap R))
  have hH4 : Γ ⊢[PRAAx] le (two*H4) B := by
    have leOne : Γ ⊢[PRAAx] le (two*H4) (two*(L*H4)) :=
      le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*H4) hL)
    exact le_trans leOne hs.andE₂.andE₂
  have hU : Γ ⊢[PRAAx] le (W*u) b := half_power H4 B j hH4
  have hV : Γ ⊢[PRAAx] le (W*(v*u)) b :=
    le_congr (congrMul (.eqRefl W) (AnalyticNumberTheory.LocalFactor.pw_mul_base L H4 j)) (.eqRefl _)
      (half_power (L*H4) B j hs.andE₂.andE₂)
  change Γ ⊢[PRAAx] le
    ((g*((k*(t*U+two*Q))*b+((two*v+P)*u)*D)+D*(F*((A*P)*u)))*(U*W))
    (((g*k)*(two*W)+(g*k+g*(two+P)+F*(A*P))*U)*(D*b))
  dsimp only [D]
  let 𝔞 := fun x : PTm n => Groth.ι (IPRA.Q.mk Γ x)
  ipra_le (𝔞 g*𝔞 k*𝔞 b*𝔞 U*𝔞 U)*sl hA+
    ((𝔞 g*𝔞 P+𝔞 F*𝔞 A*𝔞 P)*𝔞 U*𝔞 U*𝔞 Q)*sl hU+
    (2*𝔞 g*𝔞 U*𝔞 U*𝔞 Q)*sl hV

theorem rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (add z h) R B) (approxData p z h R B H M)
      (numerator p z R B M) (denominator p M) := by
  have hB := hs.andE₁.andE₁.andE₁
  have old : Γ ⊢[PRAAx] le one (GaussianBarnesCanonicalWeightedTaylorBall.denominator p R B M) :=
    positive_product _ _ (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive p R B M hB)
      (GaussianFactorBudget.power_positive B (succ (previous M)) hB)
  have next := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive (succ (previous M)))
  exact GaussianNamedRateRadius.weaken V nameF (vd (add z h) R B) (approxData p z h R B H M)
    _ _ _ _ old next (radius_comparison p z h R B H M hs)
    (GaussianBarnesCanonicalWeightedTaylorBall.rate p z h R B H M hs)

theorem shared_rate (p z h R B H M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H)
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (add z h) (R+one) B) (approxData p z h (R+one) B H M)
      (numerator p z (R+one) B M) (denominator p M) :=
  rate p z h (R+one) B H M (GaussianBarnesCanonicalWeightedTaylorBallSource.admission z h R B H M hz hh hsmall)

theorem actual_Barnes_shared_Taylor_ball_dyadic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     source z R B ⟶ ComplexLogarithmRemainder.bounded h H ⟶ le (stepDivisor R*H) B ⟶
       independentRate V nameF (vd (add z h) (R+one) B) (approxData p z h (R+one) B H M)
         (numerator p z (R+one) B M) (denominator p M)) :=
  closeUniv 7 (.impI (.impI (.impI (shared_rate _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallDyadic

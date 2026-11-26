import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalTaylorBall
import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalWeightedTaylorBallSource
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalWeightedTaylorProduct

/-!
# The original Barnes Taylor evaluator on the shared weighted ball

The weighted exponent and head budgets control the original scheduled
buffer and the original degree-truncated value polynomial.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBall

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalExponentTaylorBallSchedule
  (buffer buffer_length buffer_zero precision)
open GaussianBarnesCanonicalExponentTaylorSchedule (tailCutoff)
open GaussianBarnesCanonicalExponentTaylorWeightedMass (point massCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial headDegree)
open GaussianBarnesCanonicalWeightedTaylorBallSource (input stepDivisor)
open GaussianEuclideanDistanceName (fraction)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalPolynomialDilation (dilated weightedNorm)
open RationalArgmin (rationalLE)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "J" => GaussianBarnesCanonicalExponentTaylorSchedule.numerator
local notation "D" => GaussianBarnesCanonicalExponentTaylorSchedule.denominator

abbrev nameF : PR 2 := GaussianBarnesCanonicalTaylorBall.nameF
abbrev polynomial (p z R B H M : PTm n) : PTm n := GaussianBarnesCanonicalTaylorBall.polynomial p z R B H M
abbrev approxData (p z h R B H M : PTm n) : PTm n := GaussianBarnesCanonicalTaylorBall.approxData p z h R B H M

def headMass (z R B : PTm n) : PTm n :=
  GaussianRationalPolynomialExponentialRecomposition.coefficientBudget
    (dilated (headPolynomial z R B) (headDegree R) point)

def numerator (p z R B H M : PTm n) : PTm n :=
  GaussianBarnesCanonicalWeightedTaylorProduct.error z R B (headMass z R B) (massCap R) H (previous M)
    (J p R B H M) (D p R B M) (num 3)

abbrev denominator (p R B M : PTm n) : PTm n := GaussianBarnesCanonicalTaylorBall.denominator p R B M

theorem head_mass (z R B : PTm n) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (headPolynomial z R B) (headDegree R) point) (fraction (headMass z R B) one) :=
  GaussianRationalPolynomialExponentialRecomposition.computed_mass _

theorem recomposition_input (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalWeightedTaylorRecomposition.input
      (buffer p z R B H M) (previous M) (previous M) (ofGaussian h B) H B (massCap R) := by
  let m := previous M
  have hB := hs.andE₁.andE₁.andE₁
  have hm : Γ ⊢[PRAAx] le m (m*m) :=
    le_congr (one_mul m) (.eqRefl _) (mul_le_mul_right m (zero_lt_succ (succ M)))
  have hw := GaussianBarnesCanonicalHeadPolynomialDerivative.step_bound h B H hB hs.andE₁.andE₂.andE₂.andE₁
  have mass := GaussianBarnesCanonicalExponentTaylorWeightedMass.mass
    (precision p R H) z R B (tailCutoff p R) M hs.andE₁.andE₁
  exact .andI (buffer_length p z R B H M) (.andI (buffer_zero p z R B H M)
    (.andI hm (.andI hB (.andI hs.andE₂.andE₁ (.andI hs.andE₂.andE₂ (.andI mass hw))))))

theorem rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (add z h) R B) (approxData p z h R B H M)
      (numerator p z R B H M) (denominator p R B M) := by
  let m := previous M
  let C := buffer p z R B H M
  have hB := hs.andE₁.andE₁.andE₁
  exact GaussianBarnesCanonicalWeightedTaylorProduct.rate z h R B H C m m (massCap R) (headMass z R B)
    (J p R B H M) (D p R B M) (num 3)
    hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁ (recomposition_input p z h R B H M hs)
    (head_mass z R B)
    (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive p R B M hB)
    (GaussianBarnesCanonicalExponentTaylorSchedule.radius_le_three p R B H M hs.andE₂.andE₁)
    (GaussianBarnesCanonicalExponentTaylorBallSchedule.rate p z h R B H M hs.andE₁)

theorem shared_rate (p z h R B H M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H)
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (add z h) (R+one) B) (approxData p z h (R+one) B H M)
      (numerator p z (R+one) B H M) (denominator p (R+one) B M) :=
  rate p z h (R+one) B H M (GaussianBarnesCanonicalWeightedTaylorBallSource.admission z h R B H M hz hh hsmall)

theorem shared_rate_all_degrees (p z h R B H : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded h H)
    (hsmall : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    Γ ⊢[PRAAx] .all (independentRate V nameF
      (vd (add (Syn.shift z) (Syn.shift h)) (Syn.shift (R+one)) (Syn.shift B))
      (approxData (Syn.shift p) (Syn.shift z) (Syn.shift h) (Syn.shift (R+one)) (Syn.shift B) (Syn.shift H) (var 0))
      (numerator (Syn.shift p) (Syn.shift z) (Syn.shift (R+one)) (Syn.shift B) (Syn.shift H) (var 0))
      (denominator (Syn.shift p) (Syn.shift (R+one)) (Syn.shift B) (var 0))) := by
  let sh (a : PTm n) := Syn.shift a
  let Δ := Γ.map Fm.shift
  have z' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Δ,Fm.shift,sh,Syn.shift] using hz.shift
  have h' : Δ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sh h) (sh H) := by
    simpa [Δ,Fm.shift,sh,Syn.shift] using hh.shift
  have small' : Δ ⊢[PRAAx] le (stepDivisor (sh R)*sh H) (sh B) := by
    simpa [Δ,Fm.shift,sh,Syn.shift] using hsmall.shift
  exact .allI (by simpa [sh,Syn.shift,one] using
    (shared_rate (sh p) (sh z) (sh h) (sh R) (sh B) (sh H) (var 0) z' h' small'))

theorem actual_Barnes_weighted_Taylor_ball_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     input z h R B H M ⟶ independentRate V nameF (vd (add z h) R B) (approxData p z h R B H M)
       (numerator p z R B H M) (denominator p R B M)) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_Barnes_shared_weighted_Taylor_ball_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     source z R B ⟶ ComplexLogarithmRemainder.bounded h H ⟶ le (stepDivisor R*H) B ⟶
       .all (independentRate V nameF
         (vd (add (Syn.shift z) (Syn.shift h)) (Syn.shift (R+one)) (Syn.shift B))
         (approxData (Syn.shift p) (Syn.shift z) (Syn.shift h) (Syn.shift (R+one)) (Syn.shift B) (Syn.shift H) (var 0))
         (numerator (Syn.shift p) (Syn.shift z) (Syn.shift (R+one)) (Syn.shift B) (Syn.shift H) (var 0))
         (denominator (Syn.shift p) (Syn.shift (R+one)) (Syn.shift B) (var 0)))) :=
  closeUniv 6 (.impI (.impI (.impI (shared_rate_all_degrees _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBall

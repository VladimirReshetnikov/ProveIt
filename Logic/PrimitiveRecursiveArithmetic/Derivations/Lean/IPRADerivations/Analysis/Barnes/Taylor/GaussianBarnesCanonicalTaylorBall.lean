import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorMass
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorSchedule
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorBallSchedule
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorProduct

/-!
# A stored Taylor polynomial on a disk for the original Barnes evaluator

The exponent coefficient clocks are uniform on the admitted step disk.
Recompose that stored polynomial through the exponential, and truncate
its product with the actual centered head. The central exponential
is a fixed scalar name at all displacement queries.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorBall

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalExponentTaylorMass (massCap)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial)
open GaussianBarnesCanonicalValue (data)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian)
open GaussianRationalSyntheticDivision (canonicalCoefficients)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "E" => GaussianBarnesCanonicalExponentTaylorBallSchedule.buffer
local notation "J" => GaussianBarnesCanonicalExponentTaylorSchedule.numerator
local notation "D" => GaussianBarnesCanonicalExponentTaylorSchedule.denominator
local notation "V" => GaussianBarnesCanonicalValue.nameF

def input (z h R B H M : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalCorrectedMercatorCofinal.input (previous M) z h R B H ⋏
    (le (num 4*H) B ⋏ le (two*(massCap R M*H)) B)

def headMass (z R B : PTm n) : PTm n :=
  GaussianRationalPolynomialExponentialRecomposition.coefficientBudget (headPolynomial z R B)

def polynomial (p z R B H M : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProduct.polynomial z R B (E p z R B H M) (previous M) (previous M)

abbrev nameF : PR 2 := GaussianBarnesCanonicalTaylorProduct.nameF

def approxData (p z h R B H M : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProduct.data z h R B (E p z R B H M) (previous M) (previous M)

def numerator (p z R B H M : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorProduct.error z R B (headMass z R B) (massCap R M) H (previous M)
    (J p R B H M) (D p R B M) (num 3)

def denominator (p R B M : PTm n) : PTm n :=
  GaussianBarnesCanonicalTaylorRecomposition.denominator (D p R B M) (previous M) B

theorem polynomial_length (p z R B H M : PTm n) :
    Γ ⊢[PRAAx] length (polynomial p z R B H M) ≐ succ (previous M) :=
  GaussianRationalPolynomialExponentialProductTruncation.polynomial_length _ _ _ _ _

theorem polynomial_canonical (p z R B H M : PTm n) :
    Γ ⊢[PRAAx] canonicalCoefficients (polynomial p z R B H M) :=
  GaussianRationalPolynomialExponentialProductTruncation.polynomial_canonical _ _ _ _ _

theorem rate (p z h R B H M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H M) :
    Γ ⊢[PRAAx] independentRate V nameF (data (add z h) R B) (approxData p z h R B H M)
      (numerator p z R B H M) (denominator p R B M) := by
  let m := previous M
  let C := E p z R B H M
  let L := massCap R M
  let w := ofGaussian h B
  let A := headMass z R B
  have hb := hs.andE₁.andE₁.andE₁
  have hsmall := hs.andE₂.andE₁
  have hHB : Γ ⊢[PRAAx] le H B :=
    le_trans (le_of_eq_add (d := num 3*H) (by ipra_ring : Γ ⊢[PRAAx] num 4*H ≐ H+(num 3*H))) hsmall
  have hp : Γ ⊢[PRAAx] le one m := zero_lt_succ (succ M)
  have hm : Γ ⊢[PRAAx] le m (m*m) := le_congr (one_mul m) (.eqRefl _) (mul_le_mul_right m hp)
  have wBound := GaussianBarnesCanonicalHeadPolynomialDerivative.step_bound h B H hb hs.andE₁.andE₂.andE₂.andE₁
  have bound := GaussianBarnesCanonicalExponentTaylorMass.mass
    (GaussianBarnesCanonicalExponentTaylorBallSchedule.precision p R H) z R B
    (GaussianBarnesCanonicalExponentTaylorSchedule.tailCutoff p R) M hs.andE₁.andE₁
  have hRec : Γ ⊢[PRAAx] GaussianRationalPolynomialExponentialRecomposition.input C m m w H B L :=
    .andI (GaussianBarnesCanonicalExponentTaylorBallSchedule.buffer_length p z R B H M)
      (.andI (GaussianBarnesCanonicalExponentTaylorBallSchedule.buffer_zero p z R B H M)
        (.andI hm (.andI hb (.andI hHB (.andI hs.andE₂.andE₂ (.andI bound wBound))))))
  exact GaussianBarnesCanonicalTaylorProduct.rate z h R B H C m m L A _ _ (num 3)
    hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁ hRec
    (GaussianBarnesCanonicalExponentTaylorBallSchedule.buffer_canonical p z R B H M)
    (GaussianRationalPolynomialExponentialRecomposition.computed_mass (headPolynomial z R B))
    (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive p R B M hb)
    (GaussianBarnesCanonicalExponentTaylorSchedule.radius_le_three p R B H M hsmall)
    (GaussianBarnesCanonicalExponentTaylorBallSchedule.rate p z h R B H M hs.andE₁)

theorem actual_Barnes_Taylor_ball_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let M := var 6
     input z h R B H M ⟶ independentRate V nameF (data (add z h) R B) (approxData p z h R B H M)
       (numerator p z R B H M) (denominator p R B M)) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorBall

import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalWeightedTaylorBallCoefficient
import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalWeightedTaylorBallDyadic
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# One weighted Barnes Taylor polynomial for every retained derivative

The bounded maximum of the coefficient clocks is itself primitive
recursive. The original value evaluator and every retained factorial
coefficient may therefore read the same polynomial at that clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily

open_ipra
open ComplexLogarithmRemainder (add bounded)
open GaussianBarnesCanonicalCentralUniformBound (centralUGain)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (prefactorGain tailGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit)
open GaussianFastValueCut (exponent)
open GaussianNamedInverseRate (independentRate)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.FiniteQueryDemand (finiteMaximum finiteMaximum_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "D" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "dd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "W" => GaussianBarnesCanonicalWeightedTaylorBall.nameF
local notation "wa" => GaussianBarnesCanonicalWeightedTaylorBall.approxData
local notation "cd" => GaussianBarnesCanonicalWeightedTaylorBallCoefficient.data
local notation "coefficientClock" => GaussianBarnesCanonicalWeightedTaylorBallCoefficient.clock
local notation "valueNumerator" => GaussianBarnesCanonicalWeightedTaylorBallDyadic.numerator
local notation "valueDenominator" => GaussianBarnesCanonicalWeightedTaylorBallDyadic.denominator

private def clockWithBounds (P z R B M a b c e : PTm n) : PTm n :=
  exponent (a+b) (GaussianBarnesCanonicalTaylorProductCoefficientName.clock (exponent ((c+two)*fact e) P) z R B M e)

private def parameters (P z R B M : PTm n) : PTm n :=
  pairT P (pairT z (pairT R (pairT B (pairT M (pairT (prefactorGain R) (pairT (tailGain R M) (centralUGain R)))))))

private def clockBody : PTm 2 :=
  let x := var 1
  let a := sndT x
  let b := sndT a
  let c := sndT b
  let d := sndT c
  let f := sndT d
  let g := sndT f
  clockWithBounds (fstT x) (fstT a) (fstT b) (fstT c) (fstT d) (fstT f) (fstT g) (sndT g) (var 0)

def clock (P z R B M : PTm n) : PTm n :=
  P+finiteMaximum clockBody (succ (previous M)) (parameters P z R B M)

private theorem body_at (P z R B M e : PTm n) :
    Γ ⊢[PRAAx] inst2 clockBody e (parameters P z R B M) ≐ coefficientClock P z R B M e := by
  let C := centralUGain R
  let T := tailGain R M
  let A := prefactorGain R
  let g := pairT T C
  let f := pairT A g
  let d := pairT M f
  let c := pairT B d
  let b := pairT R c
  let a := pairT z b
  have t₁ := snd_pair (Γ := Γ) P a
  have t₂ := (congrSnd t₁).eqTrans (snd_pair z b)
  have t₃ := (congrSnd t₂).eqTrans (snd_pair R c)
  have t₄ := (congrSnd t₃).eqTrans (snd_pair B d)
  have t₅ := (congrSnd t₄).eqTrans (snd_pair M f)
  have t₆ := (congrSnd t₅).eqTrans (snd_pair A g)
  ipra_congr (clockWithBounds (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) : PTm 9) with
    [fst_pair P a, (congrFst t₁).eqTrans (fst_pair z b), (congrFst t₂).eqTrans (fst_pair R c),
      (congrFst t₃).eqTrans (fst_pair B d), (congrFst t₄).eqTrans (fst_pair M f), (congrFst t₅).eqTrans (fst_pair A g),
      (congrFst t₆).eqTrans (fst_pair T C), (congrSnd t₆).eqTrans (snd_pair T C), .eqRefl e]
    using [clockWithBounds,clockBody,parameters,inst2,a,b,c,d,f,g,A,T,C,LeanProofs.IPRA.Analysis.Products.fact,one,two,
      GaussianBarnesCanonicalWeightedTaylorBallCoefficient.clock,GaussianBarnesCanonicalWeightedTaylorBallCoefficient.readinessClock,
      GaussianBarnesCanonicalWeightedTaylorBallCoefficient.coefficientClock,GaussianBarnesCanonicalWeightedTaylorBallCoefficient.coefficientBudget]

theorem precision_le_clock (P z R B M : PTm n) : Γ ⊢[PRAAx] le P (clock P z R B M) :=
  le_add_right _ _

theorem coefficient_clock_le (P z R B M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) :
    Γ ⊢[PRAAx] le (coefficientClock P z R B M e) (clock P z R B M) :=
  le_trans
    (le_congr (body_at P z R B M e) (.eqRefl _) (finiteMaximum_at clockBody (Common.lt_succ_of_le he)))
    (le_add_left _ _)

theorem rate (P z R B H M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) :
    let S := R+one
    Γ ⊢[PRAAx] independentRate D W (dd z S B M e) (cd (clock P z S B M) z S B H M e) one (unit P) :=
  GaussianBarnesCanonicalWeightedTaylorBallCoefficient.shared_rate_of_le P (clock P z (R+one) B M)
    z R B H M e hz he (coefficient_clock_le P z (R+one) B M e he)

theorem certificate (P z h R B H M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (stepDivisor R*H) B) :
    let S := R+one
    let p := clock P z S B M
    Γ ⊢[PRAAx] independentRate V W (vd (add z h) S B) (wa p z h S B H M)
      (valueNumerator p z S B M) (valueDenominator p M) ⋏
      (le e (previous M) ⟶ independentRate D W (dd z S B M e) (cd p z S B H M e) one (unit P)) :=
  .andI (GaussianBarnesCanonicalWeightedTaylorBallDyadic.shared_rate (clock P z (R+one) B M) z h R B H M hz hh hs)
    (.impI (rate P z R B H M e hz.wk Prf.hyp0))

theorem actual_Barnes_weighted_Taylor_ball_value_and_all_retained_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let P := var 0
       let z := var 1
       let h := var 2
       let R := var 3
       let B := var 4
       let H := var 5
       let M := var 6
       let e := var 7
       let S := R+one
       let p := clock P z S B M
       (source z R B ⋏ bounded h H ⋏ le (stepDivisor R*H) B) ⟶
         (independentRate V W (vd (add z h) S B) (wa p z h S B H M)
           (valueNumerator p z S B M) (valueDenominator p M) ⋏
           (le e (previous M) ⟶ independentRate D W (dd z S B M e) (cd p z S B H M e) one (unit P)))) :=
  closeUniv 8 (.impI (certificate _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCoefficientFamily

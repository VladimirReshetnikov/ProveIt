import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorBall
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalProperness

/-!
# Compare the stored Barnes Taylor values where two balls overlap

Both Taylor evaluations compare to the same original Barnes value.
Rational input properness identifies their evaluations even when the
centers, displacement denominators, disk radii, orders and clocks
differ. The comparison carries the two explicit Taylor errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorBallOverlap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalTaylorBall (nameF approxData numerator denominator input)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (ofGaussian positive_product)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalValue.nameF
local notation "fd" => GaussianBarnesCanonicalValue.data

theorem proper_rate (p q z w h k R S B D H K M N : PTm n)
    (hs : Γ ⊢[PRAAx] input z h R B H M) (ht : Γ ⊢[PRAAx] input w k S D K N)
    (he : Γ ⊢[PRAAx] ofGaussian (add z h) B ≐ ofGaussian (add w k) D) :
    Γ ⊢[PRAAx] independentRate nameF nameF (approxData p z h R B H M) (approxData q w k S D K N)
      (leadingNumerator (numerator p z R B H M) (denominator p R B M)
        (numerator q w S D K N) (denominator q S D N))
      (leadingDenominator (denominator p R B M) (denominator q S D N)) := by
  let x := fd (add z h) R B
  let y := fd (add w k) S D
  let a := approxData p z h R B H M
  let b := approxData q w k S D K N
  let A := numerator p z R B H M
  let L := denominator p R B M
  let C := numerator q w S D K N
  let J := denominator q S D N
  have hb := hs.andE₁.andE₁.andE₁
  have hd := ht.andE₁.andE₁.andE₁
  have hl : Γ ⊢[PRAAx] le one L := positive_product _ _
    (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive p R B M hb)
    (GaussianFactorBudget.power_positive _ (succ (previous M)) hb)
  have hj : Γ ⊢[PRAAx] le one J := positive_product _ _
    (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive q S D N hd)
    (GaussianFactorBudget.power_positive _ (succ (previous N)) hd)
  have hx := GaussianBarnesCanonicalTaylorBall.rate p z h R B H M hs
  have hy := GaussianBarnesCanonicalTaylorBall.rate q w k S D K N ht
  have agree := GaussianBarnesCanonicalProperness.proper (add z h) (add w k) R S B D
    hs.andE₁.andE₂.andE₁ ht.andE₁.andE₂.andE₁ he
  have bRegular : Γ ⊢[PRAAx] pointCN nameF b :=
    GaussianNameArithmetic.multiply_fast _ _ _ _
      (GaussianBarnesCanonicalCenteredExponentialShift.base_regular w S D ht.andE₁.andE₁)
      (GaussianGammaCanonicalExponent.constant_regular _)
  have hy' : Γ ⊢[PRAAx] independentRate F nameF x b C J :=
    GaussianNamedRateTransport.transport F nameF F nameF y b x b C J hj hy agree
      (GaussianNameEquivalence.cross_refl _ _ bRegular)
  exact GaussianNamedRateComposition.compose nameF F nameF a x b A L C J hl hj
    (GaussianNamedRateComposition.symmetric F nameF x a A L hl hx) hy'

theorem actual_Barnes_Taylor_ball_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
    (let p := var 0
     let q := var 1
     let z := var 2
     let w := var 3
     let h := var 4
     let k := var 5
     let R := var 6
     let S := var 7
     let B := var 8
     let D := var 9
     let H := var 10
     let K := var 11
     let M := var 12
     let N := var 13
     input z h R B H M ⟶ input w k S D K N ⟶ (ofGaussian (add z h) B ≐ ofGaussian (add w k) D) ⟶
       independentRate nameF nameF (approxData p z h R B H M) (approxData q w k S D K N)
        (leadingNumerator (numerator p z R B H M) (denominator p R B M)
          (numerator q w S D K N) (denominator q S D N))
        (leadingDenominator (denominator p R B M) (denominator q S D N))) :=
  closeUniv 14 (.impI (.impI (.impI (proper_rate _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorBallOverlap

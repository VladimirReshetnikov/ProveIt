import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalWeightedTaylorBall
import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalTaylorBallOverlap

/-!
# Compare the stored Barnes Taylor values on shared-radius balls

Both Taylor evaluations compare to the same original Barnes value.
Rational input properness identifies their evaluations even when the
centers, displacement denominators, disk radii, orders and clocks
differ. The comparison carries the two explicit Taylor errors.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallOverlap

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalWeightedTaylorBall (nameF approxData numerator denominator)
open GaussianBarnesCanonicalWeightedTaylorBallSource (input)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (ofGaussian positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem proper_rate (p q z w h k R S B D H K M N : PTm n)
    (hs : Γ ⊢[PRAAx] input z h R B H M) (ht : Γ ⊢[PRAAx] input w k S D K N)
    (he : Γ ⊢[PRAAx] ofGaussian (add z h) B ≐ ofGaussian (add w k) D) :
    Γ ⊢[PRAAx] independentRate nameF nameF (approxData p z h R B H M) (approxData q w k S D K N)
      (leadingNumerator (numerator p z R B H M) (denominator p R B M)
        (numerator q w S D K N) (denominator q S D N))
      (leadingDenominator (denominator p R B M) (denominator q S D N)) := by
  let L := denominator p R B M
  let J := denominator q S D N
  have hb := hs.andE₁.andE₁.andE₁
  have hd := ht.andE₁.andE₁.andE₁
  have hl : Γ ⊢[PRAAx] le one L := positive_product _ _
    (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive p R B M hb)
    (GaussianFactorBudget.power_positive _ (succ (previous M)) hb)
  have hj : Γ ⊢[PRAAx] le one J := positive_product _ _
    (GaussianBarnesCanonicalExponentTaylorSchedule.denominator_positive q S D N hd)
    (GaussianFactorBudget.power_positive _ (succ (previous N)) hd)
  exact GaussianBarnesCanonicalTaylorBallOverlap.compare _ _ (add z h) (add w k) R S B D _ L _ J
    hs.andE₁.andE₂.andE₁ ht.andE₁.andE₂.andE₁ he hl hj
    (GaussianBarnesCanonicalTaylorBallOverlap.approximation_regular q w k S D K N ht.andE₁.andE₁)
    (GaussianBarnesCanonicalWeightedTaylorBall.rate p z h R B H M hs)
    (GaussianBarnesCanonicalWeightedTaylorBall.rate q w k S D K N ht)

theorem actual_Barnes_weighted_Taylor_ball_overlap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 14
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

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallOverlap

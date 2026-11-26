import IPRADerivations.Analysis.Barnes.Taylor.TaylorBalls.GaussianBarnesCanonicalTaylorBall
import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProperness

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

open_ipra
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalTaylorBall (nameF approxData numerator denominator input)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (leadingNumerator leadingDenominator)
open GaussianRationalHorner (ofGaussian positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalValue.nameF
local notation "fd" => GaussianBarnesCanonicalValue.data

theorem approximation_regular (p z h R B H M : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] pointCN nameF (approxData p z h R B H M) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _
    (GaussianBarnesCanonicalCenteredExponentialShift.base_regular z R B hz)
    (GaussianGammaCanonicalExponent.constant_regular _)

theorem compare (a b x y R S B D A L C J : PTm n)
    (hx : Γ ⊢[PRAAx] source x R B) (hy : Γ ⊢[PRAAx] source y S D)
    (he : Γ ⊢[PRAAx] ofGaussian x B ≐ ofGaussian y D)
    (hl : Γ ⊢[PRAAx] le one L) (hj : Γ ⊢[PRAAx] le one J)
    (hr : Γ ⊢[PRAAx] pointCN nameF b)
    (ha : Γ ⊢[PRAAx] independentRate F nameF (fd x R B) a A L)
    (hb : Γ ⊢[PRAAx] independentRate F nameF (fd y S D) b C J) :
    Γ ⊢[PRAAx] independentRate nameF nameF a b (leadingNumerator A L C J) (leadingDenominator L J) := by
  have agree := GaussianBarnesCanonicalProperness.proper x y R S B D hx hy he
  have next : Γ ⊢[PRAAx] independentRate F nameF (fd x R B) b C J :=
    GaussianNamedRateTransport.transport F nameF F nameF (fd y S D) b (fd x R B) b C J hj hb agree
      (GaussianNameEquivalence.cross_refl _ _ hr)
  exact GaussianNamedRateComposition.compose nameF F nameF a (fd x R B) b A L C J hl hj
    (GaussianNamedRateComposition.symmetric F nameF (fd x R B) a A L hl ha) next

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
  exact compare _ _ (add z h) (add w k) R S B D _ L _ J
    hs.andE₁.andE₂.andE₁ ht.andE₁.andE₂.andE₁ he hl hj
    (approximation_regular q w k S D K N ht.andE₁.andE₁)
    (GaussianBarnesCanonicalTaylorBall.rate p z h R B H M hs)
    (GaussianBarnesCanonicalTaylorBall.rate q w k S D K N ht)

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

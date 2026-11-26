import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalWeightedTaylorBallDyadic
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalWeightedTaylorBallOverlap
import IPRADerivations.Analysis.RationalArithmetic.Grids.GaussianRationalSquareGrid

/-!
# A finite rational cover for the Barnes Taylor balls

The mesh is chosen from the shared Taylor step divisor. At a rational
point in the original disk, the finite square grid supplies a center
and a common-denominator displacement. Their Taylor ball evaluates
the original Barnes name at that point.
-/

set_option autoImplicit false
set_option maxHeartbeats 1250000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCover

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add scale)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBall (nameF approxData)
open GaussianBarnesCanonicalWeightedTaylorBallDyadic (numerator denominator)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor stepDivisor_positive)
open GaussianFastValueCut (recode recode_canonical recode_represents)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product represents_congr represents_rescale)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalMetric (bounded bounded_iff)
open GaussianRationalSquareGrid (grid nearest nativePoint nearestX nearestY nearestIndex nativeError)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_add im_add re_sub im_sub)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

def mesh (R : PTm n) : PTm n := stepDivisor (two*R)
def centers (R : PTm n) : PTm n := grid R (mesh R)
def index (q R : PTm n) : PTm n := nearestIndex R (mesh R) q
def chartDen (q R : PTm n) : PTm n := rawDen q*mesh R
def center (q R : PTm n) : PTm n :=
  scale (rawDen q) (nativePoint R (mesh R) (nearestX R (mesh R) q) (nearestY R (mesh R) q))
def step (q R : PTm n) : PTm n := nativeError R (mesh R) q

private theorem source_of_representation (q z R B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B)
    (hr : Γ ⊢[PRAAx] GaussianRationalHorner.represents q z B)
    (hq : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx] source z R B := by
  have h := (bounded_iff q z B R one hB (le_refl one) hr).iffMp hq
  exact .andI hB (le_congr (by ipra_ring) (by ipra_ring) h)

theorem center_fraction (q R : PTm n) :
    Γ ⊢[PRAAx] ofGaussian (center q R) (chartDen q R) ≐ nearest R (mesh R) q := by
  let d := rawDen q
  let m := mesh R
  let z := nativePoint R m (nearestX R m q) (nearestY R m q)
  change Γ ⊢[PRAAx] ofGaussian (scale d z) (d*m) ≐ ofGaussian z m
  exact GaussianGammaEncodingRescaling.fraction_rescale z m d
    (stepDivisor_positive (two*R)) (raw_den_positive q)

theorem endpoint_fraction (q R : PTm n) :
    Γ ⊢[PRAAx] ofGaussian (add (center q R) (step q R)) (chartDen q R) ≐ recode q := by
  let d := rawDen q
  let m := mesh R
  let z := add (center q R) (step q R)
  let B := chartDen q R
  have hm := stepDivisor_positive (Γ := Γ) (two*R)
  have hB := positive_product _ _ (raw_den_positive (Γ := Γ) q) hm
  have hz : Γ ⊢[PRAAx] equal (scale m (rawGaussian q)) z := by
    apply equal_of_values <;> simp only [z,step,nativeError,center,re_add,im_add,re_sub,im_sub] <;> ring
  have hr := represents_congr (.eqRefl (recode q)) hz (.eqRefl B)
    (represents_rescale (recode q) (rawGaussian q) d m (recode_represents (Γ := Γ) q))
  exact canonical_unique _ _ z B (ofGaussian_canonical z B hB) (recode_canonical q) hB
    (ofGaussian_represents z B hB) hr

theorem center_listed (q R : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] lt (index q R) (length (centers R)) ⋏
      (ofGaussian (center q R) (chartDen q R) ≐ entry (centers R) (index q R)) :=
  .andI (GaussianRationalSquareGrid.nearest_index_bound R (mesh R) q hq)
    ((center_fraction q R).eqTrans (GaussianRationalSquareGrid.nearest_lookup R (mesh R) q hq).eqSymm)

theorem center_source (q R : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] source (center q R) (two*R) (chartDen q R) := by
  have hm := stepDivisor_positive (Γ := Γ) (two*R)
  have hB := positive_product _ _ (raw_den_positive (Γ := Γ) q) hm
  have bound := GaussianRationalSquareGrid.nearest_bound R (mesh R) q hm hq
  exact source_of_representation _ _ _ _ hB
    (represents_congr (center_fraction q R) (equal_refl _) (.eqRefl _) (ofGaussian_represents _ _ hB)) bound

theorem admission (q R M : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] GaussianBarnesCanonicalWeightedTaylorBallSource.input
      (center q R) (step q R) (two*R+one) (chartDen q R) (rawDen q) M :=
  GaussianBarnesCanonicalWeightedTaylorBallSource.admission
    (center q R) (step q R) (two*R) (chartDen q R) (rawDen q) M
    (center_source q R hq) (GaussianRationalSquareGrid.native_error_bound R (mesh R) q hq)
    (le_congr (mul_comm _ _) (.eqRefl _) (le_refl (chartDen q R)))

theorem rate (p q R M : PTm n) (hq : Γ ⊢[PRAAx] bounded q R one) :
    Γ ⊢[PRAAx] independentRate V nameF (vd (rawGaussian q) R (rawDen q))
      (approxData p (center q R) (step q R) (two*R+one) (chartDen q R) (rawDen q) M)
      (numerator p (center q R) (two*R+one) (chartDen q R) M) (denominator p M) := by
  let z := center q R
  let h := step q R
  let S := two*R+one
  let d := rawDen q
  let B := chartDen q R
  let x := vd (add z h) S B
  let y := vd (rawGaussian q) R d
  let t := approxData p z h S B d M
  let A := numerator p z S B M
  let D := denominator p M
  have hq' := source_of_representation q (rawGaussian q) R d (raw_den_positive q) (raw_represents q) hq
  have chart := admission q R M hq
  have same := GaussianBarnesCanonicalProperness.proper (rawGaussian q) (add z h) R S d B hq'
    chart.andE₁.andE₂.andE₁ (endpoint_fraction q R).eqSymm
  have ht := GaussianBarnesCanonicalTaylorBallOverlap.approximation_regular p z h S B d M chart.andE₁.andE₁
  have hD := positive_product _ _ (GaussianCoefficientNameBounds.unit_positive (Γ := Γ) p)
    (GaussianCoefficientNameBounds.unit_positive (ConciseIPRA.PTm.succ (GaussianBarnesCanonicalHigherRows.previous M)))
  exact GaussianNamedRateTransport.transport V nameF V nameF x t y t A D hD
    (GaussianBarnesCanonicalWeightedTaylorBallDyadic.rate p z h S B d M chart)
    same (cross_refl _ _ ht)

theorem actual_Barnes_Taylor_ball_cover_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let q := var 0
       let R := var 1
       let p := var 2
       let M := var 3
       bounded q R one ⟶
         ((lt (index q R) (length (centers R)) ⋏
           (ofGaussian (center q R) (chartDen q R) ≐ entry (centers R) (index q R))) ⋏
           independentRate V nameF (vd (rawGaussian q) R (rawDen q))
             (approxData p (center q R) (step q R) (two*R+one) (chartDen q R) (rawDen q) M)
             (numerator p (center q R) (two*R+one) (chartDen q R) M) (denominator p M))) :=
  closeUniv 4 (.impI (.andI (center_listed _ _ Prf.hyp0) (rate _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalWeightedTaylorBallCover

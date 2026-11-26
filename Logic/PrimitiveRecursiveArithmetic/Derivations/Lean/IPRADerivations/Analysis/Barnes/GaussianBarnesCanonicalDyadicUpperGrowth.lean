import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDyadicCentralExponent
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalDyadicHeadPower
import IPRADerivations.Analysis.Barnes.Names.GaussianBarnesCanonicalNamed
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedBoundedProductObservation

/-!
# Dyadic upper growth of the original Barnes evaluator

The kept powers and the single exponential have separate dyadic caps.
Their product bounds the original evaluator on a dyadic disk, with a
fixed allowance for the two independent observation errors. The same
bound holds when the input is given by a regular Gaussian name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicUpperGrowth

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open BarnesCutoff (maximum_of_right)
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalDyadicCentralBound (centralCap central_samples)
open GaussianBarnesCanonicalDyadicCentralExponent (dyadicGrowthConstant dyadic_unit_cap_bound)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (exponentF exponentData)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianNamedMultiplyRate (sample_bound_at)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawDen rawGaussian)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data
local notation "S" => GaussianBarnesCanonicalSingleExponential.nameF
local notation "sd" => GaussianBarnesCanonicalSingleExponential.data
local notation "E" => GaussianRadiusExponentialName.nameF exponentF

def growthConstant : PTm n := (num 4+dyadicGrowthConstant)+two
private def factorExponent (j : PTm n) : PTm n := (num 4+dyadicGrowthConstant)*succ j*(unit j*unit j)
def exponent (j : PTm n) : PTm n := growthConstant*succ j*(unit j*unit j)

private theorem initial_le (j : PTm n) : Γ ⊢[PRAAx] le (initial (unit j)) (unit (succ j)) := by
  have one_le_double : Γ ⊢[PRAAx] le one (two*unit j) :=
    le_trans (unit_positive j) (le_of_eq_add (d := unit j) (by ipra_ring))
  have hN : Γ ⊢[PRAAx] initial (unit j) ≐ two*unit j := maximum_of_right one_le_double
  exact le_congr hN.eqSymm (pw_succ two j).eqSymm (le_congr (.eqRefl _) (mul_comm _ _) (le_refl _))

theorem factorized_bound (p z B j : PTm n) (hz : Γ ⊢[PRAAx] source z (unit j) B) :
    Γ ⊢[PRAAx] bounded (ap2 S p (sd z (unit j) B)) (unit (factorExponent j)) one := by
  let R := unit j
  let a := powerProduct z B (initial R)
  let b := exponentialInputData exponentF (exponentData z R B)
  let k := GaussianNamedBoundedProductObservation.clock constantF E p a b
  let H := num 4*R*R*succ j
  let C := dyadicGrowthConstant*succ j*(R*R)
  have ha : Γ ⊢[PRAAx] bounded (ap2 constantF k a) (unit H) one :=
    bound_congr (constant_at k a).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianBarnesCanonicalDyadicHeadPower.initial_dyadic_bound z B j hz)
  have hb := sample_bound_at E b (centralCap R (succ j)) k (central_samples z R B (succ j) hz (initial_le j))
  have hc := bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (mul_le_mul_right one (dyadic_unit_cap_bound j)) hb
  have read := GaussianNamedBoundedProductObservation.name_at (Γ := Γ) constantF E p a b
  have sum : Γ ⊢[PRAAx] H+C ≐ factorExponent j := by dsimp [H,C,R,factorExponent]; ipra_ring
  have power := (pw_add two H C).eqSymm.eqTrans (congrAp2 powF sum (.eqRefl _))
  exact bound_congr read.eqSymm power (one_mul one)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) ha hc)

private theorem allowance (j : PTm n) : Γ ⊢[PRAAx] le (factorExponent j+two) (exponent j) := by
  have h := positive_product _ _ (zero_lt_succ (Γ := Γ) j)
    (positive_product _ _ (unit_positive j) (unit_positive j))
  have two_le := le_congr (one_mul two) (.eqRefl _) (mul_le_mul_right two h)
  exact le_congr (.eqRefl _) (by unfold exponent factorExponent growthConstant; ipra_ring)
    (add_le_add₂ (le_refl (factorExponent j)) two_le)

theorem transfer_bound (f g : PR 2) (p x y a : PTm n)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) (hg : Γ ⊢[PRAAx] bounded (ap2 g p y) (unit a) one) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) (unit (a+two)) one := by
  let H := unit a
  let U := unit p
  have dp := cross_at f g x y p p he
  have hp := unit_positive (Γ := Γ) p
  have hOne : Γ ⊢[PRAAx] le one one := le_refl one
  have errors : Γ ⊢[PRAAx] le ((U+U)*one) (two*(U*U)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*U) hp)
  have near := distance_radius_mono _ _ _ _ two one (positive_product _ _ hp hp) hOne errors dp
  have old := GaussianReconstructionRoots.norm_from_distance _ _ two one H one hOne hOne near hg
  have four : Γ ⊢[PRAAx] unit (a+two) ≐ H*(two*two) :=
    (pw_add two a two).eqTrans
      (congrMul (.eqRefl _) ((pw_succ two one).eqTrans (congrMul (pw_one two) (.eqRefl _))))
  have absorb : Γ ⊢[PRAAx] le (two+H) (H*(two*two)) :=
    le_trans
      (add_le_add₂ (le_congr (one_mul two) (.eqRefl _) (mul_le_mul_right two (unit_positive a))) (le_refl H))
      (le_of_eq_add (d := H) (by ipra_ring))
  have fit : Γ ⊢[PRAAx] le ((two*one+H*one)*one) (unit (a+two)*(one*one)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (le_congr (.eqRefl _) four.eqSymm absorb)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hOne hOne) hOne fit old

theorem sample_bound (p z B j : PTm n) (hz : Γ ⊢[PRAAx] source z (unit j) B) :
    Γ ⊢[PRAAx] bounded (ap2 V p (vd z (unit j) B)) (unit (exponent j)) one := by
  have near := transfer_bound V S p (vd z (unit j) B) (sd z (unit j) B) (factorExponent j)
    (GaussianBarnesCanonicalSingleExponential.factorization z (unit j) B hz) (factorized_bound p z B j hz)
  exact bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
    (mul_le_mul_right one (unit_monotone (allowance j))) near

theorem named_sample_bound (f : PR 2) (p x j : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianBarnesCanonicalNamedDemand.source f x (unit j)) :
    Γ ⊢[PRAAx] bounded (ap2 (GaussianBarnesCanonicalNamed.nameF f) p
      (GaussianBarnesCanonicalNamedDemand.data x (unit j))) (unit (exponent j)) one := by
  let k := GaussianBarnesCanonicalNamed.clock p (unit j)
  let q := ap2 f k x
  have h := GaussianBarnesCanonicalNamedDemand.native_source f k x (unit j) hf
  exact bound_congr (GaussianBarnesCanonicalNamed.sample_at f p x (unit j)).eqSymm (.eqRefl _) (.eqRefl _)
    (sample_bound (succ p) (rawGaussian q) (rawDen q) j h)

theorem actual_Barnes_canonical_dyadic_disk_growth_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let p := var 0
     let z := var 1
     let B := var 2
     let j := var 3
     source z (unit j) B ⟶ bounded (ap2 V p (vd z (unit j) B)) (unit (exponent j)) one) :=
  closeUniv 4 (.impI (sample_bound _ _ _ _ Prf.hyp0))

theorem actual_Barnes_named_dyadic_disk_growth_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let p := var 0
       let x := var 1
       let j := var 2
       GaussianBarnesCanonicalNamedDemand.source f x (unit j) ⟶
         bounded (ap2 (GaussianBarnesCanonicalNamed.nameF f) p
           (GaussianBarnesCanonicalNamedDemand.data x (unit j))) (unit (exponent j)) one) :=
  closeUniv 3 (.impI (named_sample_bound f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicUpperGrowth

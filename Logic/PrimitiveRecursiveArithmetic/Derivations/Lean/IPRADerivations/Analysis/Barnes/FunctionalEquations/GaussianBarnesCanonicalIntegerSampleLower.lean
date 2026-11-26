import IPRADerivations.Analysis.Barnes.FunctionalEquations.GaussianBarnesCanonicalIntegerValues
import IPRADerivations.Analysis.Barnes.BarnesIntegerGrowth
import IPRADerivations.Analysis.Exponential.GaussianExponentialReference
import IPRADerivations.Analysis.FiniteOperations.GaussianBoundedInverseApartness
import IPRADerivations.Core.CommonLemmas

/-!
# Integer lower growth in observations of the original Barnes sampler

At precision at least two, the original Barnes sample is within one half
of the exact superfactorial. Every positive integer lower bound for that
superfactorial therefore gives half that bound for the sample's norm.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerSampleLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalValue (nameF data)
open GaussianBarnesCanonicalIntegerValues (integerValue original_integer_value)
open GaussianGammaCanonicalExponent (constant_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product represents)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (bounded_difference_iff distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalLowerBounds (lower lower_from_representation)
open ComplexLogarithmRemainder (normSq normSq_scale normSq_one scale oneCode)
open GaussianRootAlgebra (sub)
open BarnesInteger (barnes)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sample (p i : PTm n) : PTm n := ap2 nameF p (data (scale i oneCode) i one)

private theorem sample_distance (p i : PTm n) (hp : Γ ⊢[PRAAx] le two p) :
    Γ ⊢[PRAAx] distanceBounded (sample p i) (integerValue i) one two := by
  let U := unit p
  have hU := unit_positive (Γ := Γ) p
  have four : Γ ⊢[PRAAx] le (two*two) U :=
    le_congr (LeanProofs.IPRA.Common.pw_two (Γ := Γ) two) (.eqRefl _)
      (GaussianExponentialReference.unit_monotone hp)
  have budget : Γ ⊢[PRAAx] le ((U+U)*two) (one*(U*U)) :=
    le_congr (by ipra_ring) (one_mul _).eqSymm (mul_le_mul_right U four)
  have h := GaussianNameEquivalence.cross_at _ _ _ _ p p (original_integer_value (Γ := Γ) i)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hU) (le_succ_self one)
    budget (distance_congr (.eqRefl _) (constant_at p (integerValue i)) (.eqRefl _) (.eqRefl _) h)

theorem sample_lower (p i A : PTm n) (hp : Γ ⊢[PRAAx] le two p)
    (hA : Γ ⊢[PRAAx] le one A) (hi : Γ ⊢[PRAAx] le A (barnes i)) :
    Γ ⊢[PRAAx] lower (sample p i) A two := by
  let q := sample p i
  let x := integerValue i
  let D := rawDen q
  let T := barnes i
  let r := scale D (scale T oneCode)
  let t := rawGaussian q
  have hd := raw_den_positive (Γ := Γ) q
  have ht := raw_represents (Γ := Γ) q
  have htwo := le_succ_self (Γ := Γ) one
  have hr : Γ ⊢[PRAAx] represents x r D :=
    GaussianRationalSyntheticDivision.rescale_to _ _ one D D
      (GaussianRationalNaturalScale.natural_point_represents T) (one_mul D)
  have nr : Γ ⊢[PRAAx] normSq r ≐ D*D*(T*T) :=
    (normSq_scale D _).eqTrans (congrMul (.eqRefl _)
      ((normSq_scale T oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))))
  have ref : Γ ⊢[PRAAx] le (two*two*((A*D)*(A*D))) (two*two*normSq r) :=
    le_congr (by ipra_ring)
      ((by ipra_ring : Γ ⊢[PRAAx] (T*T)*(two*two*(D*D)) ≐ (two*two)*(D*D*(T*T))).eqTrans
        (congrMul (.eqRefl _) nr.eqSymm))
      (mul_le_mul_right (two*two*(D*D)) (sq_le_sq hi))
  have err := (bounded_difference_iff x q r t D one two hd htwo hr ht).iffMp
    (distance_symmetric _ _ _ _ htwo (sample_distance p i hp))
  have diff : Γ ⊢[PRAAx] le (two*two*normSq (sub r t)) ((A*D)*(A*D)) :=
    le_trans err (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right (D*D) (sq_le_sq hA)))
  exact lower_from_representation q t D A two hd htwo ht
    (le_congr (by ipra_ring) (.eqRefl _)
      (GaussianGeneralCoefficientNames.native_apart_tail r t (A*D) two ref diff))

theorem tiled_sample_lower (p m : PTm n) (hp : Γ ⊢[PRAAx] le two p) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] lower (sample p (num 4*m)) (pw (two*m) (m*m)) two := by
  have hm' : Γ ⊢[PRAAx] le m (two*m) := le_of_eq_add (d := m) (by ipra_ring)
  exact sample_lower p (num 4*m) (pw (two*m) (m*m)) hp
    (GaussianFactorBudget.power_positive _ _ (le_trans hm hm'))
    (BarnesIntegerGrowth.tiled_lower m hm)

theorem actual_Barnes_integer_tiled_sample_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (let p := var 0
     let m := var 1
     le two p ⟶ le one m ⟶ lower (sample p (num 4*m)) (pw (two*m) (m*m)) two) :=
  closeUniv 2 (.impI (.impI (tiled_sample_lower _ _ Prf.hyp0.wk Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalIntegerSampleLower

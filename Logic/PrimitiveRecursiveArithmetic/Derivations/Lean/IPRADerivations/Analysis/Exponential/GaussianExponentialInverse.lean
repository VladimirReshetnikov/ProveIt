import IPRADerivations.Analysis.Exponential.GaussianExponentialAddition
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalTailExponential
import IPRADerivations.Analysis.Names.GaussianNameRingLaws
import IPRADerivations.Analysis.Polynomials.RootFinding.Descent.GaussianMonicResidualRadius

/-!
# The actual named exponential multiplied by the exponential of its negative

The existing actual negative-name constructor retains its true sampling
clock. Original bounded input samples derive the SAME radius for its
outputs. Actual exponential addition, independent-radius transport and
the genuine additive-inverse name law reduce the product to the actual
finite scalar exponential at zero. No inverse/output law is assumed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianExponentialInverse

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (bounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianNameRingLaws (negativeF negativeData zeroF oneF zero_at one_at zero_fast one_fast)
open GaussianRadiusExponentialName (input nameF data)
open GaussianNameEquivalence (diagonalEquivalent crossEquivalent cross_refl cross_trans cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem negative_sample_bound (f : PR 2) (R x p : PTm n) (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    bounded (ap2 (negativeF f) p (negativeData x)) R one := by
  have raw := GaussianRationalReciprocal.bounded_difference qzero
    (ap2 f (GaussianFastValueCut.exponent (one+one) p) x) zero one R one (le_refl _) (le_refl _)
    (GaussianMonicResidualRadius.zero_bounded zero one (le_refl _))
    (GaussianRadiusExponentialName.bounded_samples_at f R x _ hf.andE₂)
  have exactRadius : Γ ⊢[PRAAx] bounded
      (qsub qzero (ap2 f (GaussianFastValueCut.exponent (one+one) p) x)) R one :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring) raw
  exact bound_congr (GaussianNameRingLaws.negative_at f x p).eqSymm (.eqRefl _) (.eqRefl _)
    ((GaussianFastValueCut.recode_bound_iff _ R one (le_refl _)).iffMpr exactRadius)

theorem negative_input (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    input (negativeF f) R (negativeData x) := by
  refine .andI (GaussianNameRingLaws.negative_fast f x hf.andE₁) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRadiusExponentialName.subst_input,Syn.shift] using hf.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,GaussianNameRingLaws.subst_negativeData] using
    negative_sample_bound f (Syn.shift R) (Syn.shift x) (var 0) hs

theorem zero_input (R x : PTm n) : Γ ⊢[PRAAx] input zeroF R x := by
  refine .andI (zero_fast x) (.allI ?_)
  exact bound_congr (zero_at (var 0) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianMonicResidualRadius.zero_bounded (Syn.shift R) one (le_refl _))

theorem zero_exponential_at (R x p : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF zeroF) p (data R x) ≐ GaussianRationalSyntheticDivision.qone :=
  (GaussianRadiusExponentialName.sample_at zeroF R p x).eqTrans
    ((GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody
      (.eqRefl _) (zero_at _ _)).eqTrans (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

theorem zero_exponential_cross (R x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (nameF zeroF) oneF (data R x) x := by
  refine GaussianNameEquivalence.diagonal_to_cross _ _ _ _
    (GaussianRadiusExponentialName.name_regular zeroF R x (zero_input R x)) (one_fast x) (.allI ?_)
  have e := distance_radius_mono (Γ := Γ.map Fm.shift) _ _ zero (unit (var 0)) two (unit (var 0))
    (unit_positive _) (unit_positive _) (le_of_eq_add (d := two*unit (var 0)) (by ipra_ring))
    (GaussianRationalPowerDifference.distance_refl_zero (GaussianRationalSyntheticDivision.qone : PTm (n+1))
      (unit (var 0)) (unit_positive _))
  simpa only [diagonalEquivalent,Syn.shift,GaussianRadiusExponentialName.subst_data] using
    distance_congr (zero_exponential_at (Syn.shift R) (Syn.shift x) (var 0)).eqSymm
      (one_at (var 0) (Syn.shift x)).eqSymm (.eqRefl _) (.eqRefl _) e

def productF (f : PR 2) : PR 2 := GaussianNameArithmetic.multiplyF (nameF f) (nameF (negativeF f))
def productData (f : PR 2) (R x : PTm n) : PTm n :=
  GaussianNameArithmetic.multiplyData (nameF f) (nameF (negativeF f)) (data R x) (data R (negativeData x))
@[simp] theorem subst_productData {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (R x : PTm n) :
    Syn.subst σ (productData f R x) = productData f (Syn.subst σ R) (Syn.subst σ x) := by simp [productData]

theorem product_regular (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    pointCN (productF f) (productData f R x) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianRadiusExponentialName.name_regular f R x hf)
    (GaussianRadiusExponentialName.name_regular (negativeF f) R (negativeData x) (negative_input f R x hf))

theorem inverse_positive_radius (f : PR 2) (R x : PTm n) (hR : Γ ⊢[PRAAx] le one R)
    (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx] crossEquivalent (productF f) oneF (productData f R x) x := by
  have hn := negative_input f R x hf
  have addition := GaussianExponentialAddition.exponential_add_cross f (negativeF f) R x (negativeData x) hR hf hn
  have summed := GaussianExponentialRadiusIndependence.independent_radii_proper
    (GaussianNameArithmetic.addF f (negativeF f)) zeroF (R+R) zero
    (GaussianNameArithmetic.addData x (negativeData x)) x
    (GaussianExponentialReference.add_input f (negativeF f) R x (negativeData x) hf hn) (zero_input zero x)
    (GaussianNameRingLaws.add_negative f x hf.andE₁)
  exact cross_trans _ _ _ _ _ _ addition (cross_trans _ _ _ _ _ _ summed (zero_exponential_cross zero x))

/-- Actual exp(f) times actual exp(-f) is one at every original numerical
radius, including zero, with each original operation clock retained. -/
theorem exponential_inverse (f : PR 2) (R x : PTm n) (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    crossEquivalent (productF f) oneF (productData f R x) x := by
  let W := R+one
  have hw := GaussianExponentialRadiusIndependence.input_widen f R W x hf (le_add_right _ _)
  have hn := negative_input f R x hf
  have hnw := negative_input f W x hw
  have change := GaussianNameArithmetic.multiply_equivalent (nameF f) (nameF f)
    (nameF (negativeF f)) (nameF (negativeF f)) (data R x) (data W x) (data R (negativeData x)) (data W (negativeData x))
    (GaussianRadiusExponentialName.name_regular f R x hf) (GaussianRadiusExponentialName.name_regular f W x hw)
    (GaussianRadiusExponentialName.name_regular (negativeF f) R (negativeData x) hn)
    (GaussianRadiusExponentialName.name_regular (negativeF f) W (negativeData x) hnw)
    (cross_to_diagonal _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross f R W x hf hw))
    (cross_to_diagonal _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross (negativeF f) R W (negativeData x) hn hnw))
  exact cross_trans _ _ _ _ _ _ change
    (inverse_positive_radius f W x (le_of_eq_add (d := R) (by unfold W; ipra_ring)) hw)

theorem original_negative_exponential_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ input (negativeF f) (var 0) (negativeData (var 1))) :=
  closeUniv 2 (.impI (negative_input f _ _ Prf.hyp0))
theorem actual_zero_named_exponential_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (nameF zeroF) (var 2) (data (var 0) (var 1)) ≐ GaussianRationalSyntheticDivision.qone) :=
  closeUniv 3 (zero_exponential_at _ _ _)
theorem original_exponential_inverse_product_regular_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ pointCN (productF f) (productData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (product_regular f _ _ Prf.hyp0))
theorem original_actual_named_exponential_inverse_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (input f (var 0) (var 1) ⟶ crossEquivalent (productF f) oneF (productData f (var 0) (var 1)) (var 1)) :=
  closeUniv 2 (.impI (exponential_inverse f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianExponentialInverse

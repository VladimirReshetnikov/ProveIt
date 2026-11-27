import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianRealNameExponentialUnitReflection
import IPRADerivations.Analysis.Exponential.Names.Derivatives.GaussianNamedExponentialDifferenceIdentity

/-!
# Injectivity of the actual exponential on real regular Gaussian names

The original exponential programs may use independent input radii.
Only regular input names, their sample disks, and real-axis membership
of every raw input observation are required. Actual exponential addition
and inverse identities reduce equality to exp(f-g)=exp(-(f-g))=1.
Finite positive separation and rational finite-gap removal then recover
the original independently queried inputs. No external real semantics or
completed exponential injectivity theorem is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRealNameExponentialInjectivity

open_ipra
open GaussianRadiusExponentialName (input nameF data)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalHorner (positive_product)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def axisSamples (f : PR 2) (x : PTm n) : Fm PTm n := .all
  (RationalGaussianEmbedding.axis (ap2 f (var 0) (Syn.shift x)))
def source (f g : PR 2) (R x y : PTm n) : Fm PTm n :=
  (input f R x ⋏ input g R y) ⋏ (axisSamples f x ⋏ axisSamples g y)

ipra_subst axisSamples [Syn.subst_shift, Syn.shift_subst]
ipra_subst source

theorem axis_sample_at (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] axisSamples f x) : Γ ⊢[PRAAx]
    RationalGaussianEmbedding.axis (ap2 f p x) := by simpa [axisSamples] using h.allE p

theorem difference_sample_real (f g : PR 2) (p x y : PTm n)
    (hf : Γ ⊢[PRAAx] axisSamples f x) (hg : Γ ⊢[PRAAx] axisSamples g y) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (GaussianNamedDifference.nameF f g) p (GaussianNamedDifference.data x y)) ⋏
      RationalGaussianEmbedding.axis (ap2 (GaussianNamedDifference.nameF f g) p (GaussianNamedDifference.data x y)) := by
  let q := GaussianFastValueCut.exponent two p
  let r := GaussianFastValueCut.exponent (one+one) q
  have neg := RationalGaussianEmbedding.axis_congr
    (GaussianRealNameExponentialUnitReflection.negative_sample_at g q y).eqSymm
    (RationalGaussianEmbedding.axis_negative _ (axis_sample_at g y r hg))
  have sum := RationalGaussianEmbedding.axis_add _ _ (axis_sample_at f x q hf) neg
  have read := (GaussianNameArithmetic.add_at (Γ := Γ) f (GaussianNameRingLaws.negativeF g) x (GaussianNameRingLaws.negativeData y) p).eqTrans
    (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qadd_canonical _ _))
  exact .andI (GaussianNameArithmetic.add_canonical _ _ _ _ _)
    (RationalGaussianEmbedding.axis_congr read.eqSymm sum)

theorem difference_real_samples (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] axisSamples f x) (hg : Γ ⊢[PRAAx] axisSamples g y) : Γ ⊢[PRAAx]
    realSamples (GaussianNamedDifference.nameF f g) (GaussianNamedDifference.data x y) := by
  have fs : Γ.map Fm.shift ⊢[PRAAx] axisSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have gs : Γ.map Fm.shift ⊢[PRAAx] axisSamples g (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using hg.shift
  refine .allI ?_
  simpa only [realSamples,GaussianNamedDifference.subst_data,Syn.shift] using difference_sample_real f g (var 0) (Syn.shift x) (Syn.shift y) fs gs

/-- The actual normalized difference, at its original query, is zero. -/
theorem difference_observation_zero (f g : PR 2) (R x y p : PTm n)
    (h : Γ ⊢[PRAAx] source f g R x y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianNamedDifference.nameF f g) p (GaussianNamedDifference.data x y)) one (unit p) :=
  GaussianRealNameExponentialUnitReflection.original_observation_zero _ (R+R) (GaussianNamedDifference.data x y) p y
    (GaussianNamedExponentialDifferenceIdentity.difference_input f g R x y h.andE₁.andE₁ h.andE₁.andE₂)
    (difference_real_samples f g x y h.andE₂.andE₁ h.andE₂.andE₂)
    (GaussianNamedExponentialDifferenceIdentity.difference_exponential_one f g R x y h.andE₁.andE₁ h.andE₁.andE₂ he)
    (GaussianNamedExponentialDifferenceIdentity.negative_difference_exponential_one f g R x y h.andE₁.andE₁ h.andE₁.andE₂ he)

theorem original_diagonal (f g : PR 2) (R x y p : PTm n)
    (h : Γ ⊢[PRAAx] source f g R x y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 g p y) (num 7) (unit p) := by
  let a := qsub (ap2 f p x) (ap2 g p y)
  let b := ap2 (GaussianNamedDifference.nameF f g) p (GaussianNamedDifference.data x y)
  have sample := GaussianNamedDifference.sample_error f g x y p h.andE₁.andE₁.andE₁ h.andE₁.andE₂.andE₁
  have other := difference_observation_zero f g R x y p h he
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _ (unit_positive p) (unit_positive p)
    (distance_symmetric _ _ _ _ (unit_positive p) sample) other
  have recover : Γ ⊢[PRAAx] GaussianRationalHorner.qadd (qsub a b) b ≐ a :=
    (GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans
      (GaussianRationalLinearProduct.add_sub_right _ _ (GaussianRationalMetric.qsub_canonical _ _))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by ipra_ring)) (bound_congr recover (.eqRefl _) (.eqRefl _) sum)

theorem diagonal_envelope (f g : PR 2) (R x y : PTm n)
    (h : Γ ⊢[PRAAx] source f g R x y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    GaussianNamedLipschitzRate.diagonalEnvelope f g x y zero one (num 7) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f g (Syn.shift R) (Syn.shift x) (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using h.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data (Syn.shift R) (Syn.shift x)) (data (Syn.shift R) (Syn.shift y)) := by
    simpa [Fm.shift,Syn.shift] using he.shift
  refine .allI ?_
  have raw := original_diagonal f g (Syn.shift R) (Syn.shift x) (Syn.shift y) (var 0) hs es
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,Syn.shift] using
    distance_congr (.eqRefl _) (.eqRefl _)
      (by simp only [one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,PTm.subst_num]
          unfold GaussianNamedLipschitzRate.diagonalNumerator; ipra_ring)
      (by simp only [one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero]
          unfold GaussianNamedLipschitzRate.diagonalDenominator; ipra_ring) raw

theorem original_zero_rate (f g : PR 2) (R x y : PTm n)
    (h : Γ ⊢[PRAAx] source f g R x y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    independentRate f g x y zero one :=
  GaussianNamedLipschitzRate.independent_rate f g x y zero one (num 7) (le_refl one)
    h.andE₁.andE₁.andE₁ h.andE₁.andE₂.andE₁ (diagonal_envelope f g R x y h he)

/-- Exact independent observations of the original inputs. -/
theorem original_observations (f g : PR 2) (R x y p q : PTm n)
    (h : Γ ⊢[PRAAx] source f g R x y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 g q y) (unit p+unit q) (unit p*unit q) :=
  distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring)
    (GaussianNamedInverseRate.rate_at f g x y zero one p q (original_zero_rate f g R x y h he))

theorem original_injective (f g : PR 2) (R x y : PTm n)
    (h : Γ ⊢[PRAAx] source f g R x y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data R y)) : Γ ⊢[PRAAx]
    crossEquivalent f g x y := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f g (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have es : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent (nameF f) (nameF g)
      (data (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x))) (data (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift y))) := by
    simpa [Fm.shift,Syn.shift] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,Syn.shift] using original_observations f g (Syn.shift (Syn.shift R))
    (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (var 0) hs es

theorem independent_radii_injective (f g : PR 2) (R S x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g S y)
    (fr : Γ ⊢[PRAAx] axisSamples f x) (gr : Γ ⊢[PRAAx] axisSamples g y)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data R x) (data S y)) : Γ ⊢[PRAAx]
    crossEquivalent f g x y := by
  have fw := GaussianExponentialRadiusIndependence.input_widen f R (R+S) x hf (le_add_right _ _)
  have gw := GaussianExponentialRadiusIndependence.input_widen g S (R+S) y hg (le_congr (.eqRefl _) (add_comm _ _) (le_add_right _ _))
  exact original_injective f g (R+S) x y (.andI (.andI fw gw) (.andI fr gr))
    (cross_trans _ _ _ _ _ _ (GaussianExponentialRadiusIndependence.same_input_cross f (R+S) R x fw hf)
      (cross_trans _ _ _ _ _ _ he (GaussianExponentialRadiusIndependence.same_input_cross g S (R+S) y hg gw)))

theorem actual_original_real_named_exponential_injective_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((input f (var 0) (var 2) ⋏ input g (var 1) (var 3)) ⟶
      (axisSamples f (var 2) ⋏ axisSamples g (var 3)) ⟶
      crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 3)) ⟶ crossEquivalent f g (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (independent_radii_injective f g _ _ _ _
    Prf.hyp0.wk.wk.andE₁ Prf.hyp0.wk.wk.andE₂ Prf.hyp0.wk.andE₁ Prf.hyp0.wk.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianRealNameExponentialInjectivity

import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialSeparation
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.Exponential.GaussianExponentialInverse
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference

/-!
# Reflect the value one through the actual real named exponential

For a regular real input on a fixed disk, actual equivalence of both
signed exponentials with one implies that the input is zero. The finite
positive Taylor lower slope is applied to each original observation or
its actual negative. Only the auxiliary observation precision disappears.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRealNameExponentialUnitReflection

open_ipra
open GaussianRadiusExponentialName (input nameF data)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameRingLaws (negativeF negativeData oneF one_at zeroF zero_at)
open GaussianRationalHorner (qzero canonical positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def cost (R : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor R+num 4
ipra_subst cost

theorem negative_sample_at (f : PR 2) (p x : PTm n) : Γ ⊢[PRAAx]
    ap2 (negativeF f) p (negativeData x) ≐ qnegative (ap2 f (GaussianFastValueCut.exponent (one+one) p) x) :=
  (GaussianNameRingLaws.negative_at f x p).eqTrans
    ((GaussianNameArithmetic.recode_congr
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalMetric.qnegative_canonical _)))

theorem negative_sample_rate_at (f : PR 2) (x j p q : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (negativeF f) p (negativeData x)) (ap2 constantF q (qnegative (ap2 f j x)))
      (rateNumerator one (unit j) p q) (rateDenominator (unit j) p q) := by
  let r := GaussianFastValueCut.exponent (one+one) p
  have old := GaussianNamedDifference.negative_distance _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive j))
    (GaussianNameEquivalence.point_at f x r j hf)
  have grow : Γ ⊢[PRAAx] le (unit p) (unit r) := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have small := distance_radius_mono _ _ _ _ (unit p+unit j) (unit p*unit j)
    (positive_product _ _ (unit_positive r) (unit_positive j)) (positive_product _ _ (unit_positive p) (unit_positive j))
    (by ipra_le (𝔞(unit j)^2)*sl grow) old
  have result := distance_radius_mono _ _ _ _ (rateNumerator one (unit j) p q) (rateDenominator (unit j) p q)
    (positive_product _ _ (unit_positive p) (unit_positive j))
    (GaussianNamedInverseRate.denominator_positive _ p q (unit_positive j))
    (le_of_eq_add (d := unit j*unit j*unit p*unit p) (by unfold rateNumerator rateDenominator; ipra_ring)) small
  exact distance_congr (negative_sample_at f p x).eqSymm (constant_at q _).eqSymm (.eqRefl _) (.eqRefl _) result

theorem negative_sample_rate (f : PR 2) (x j : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx]
    independentRate (negativeF f) constantF (negativeData x) (qnegative (ap2 f j x)) one (unit j) := by
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa [Fm.shift,Syn.shift] using hf.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianNameRingLaws.subst_negativeData,GaussianRationalMetric.subst_qnegative,
    subst_ap2,GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    negative_sample_rate_at f (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift j)) (var 1) (var 0) hs

theorem negative_exponential_sample_rate (f : PR 2) (R x j : PTm n) (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    independentRate (nameF (negativeF f)) (nameF constantF) (data R (negativeData x)) (data R (qnegative (ap2 f j x)))
      (GaussianRadiusExponentialLipschitzRate.factor R*one) (unit j) :=
  GaussianRadiusExponentialLipschitzRate.independent_rate (negativeF f) constantF R (negativeData x) (qnegative (ap2 f j x)) one (unit j)
    (.andI (unit_positive j) (.andI (GaussianExponentialInverse.negative_input f R x hf)
      (.andI (GaussianSignedNameExponentialOrder.constant_input _ R
        (GaussianRationalReciprocal.bounded_negative _ _ _ (le_refl one)
          (GaussianRadiusExponentialName.bounded_samples_at f R x j hf.andE₂)))
        (negative_sample_rate f x j hf.andE₁))))

/-- A fixed actual constant observation, with its own original cutoff. -/
theorem constant_near_one (f : PR 2) (R x c j anchor : PTm n)
    (hr : Γ ⊢[PRAAx] independentRate (nameF f) (nameF constantF) (data R x) (data R c)
      (GaussianRadiusExponentialLipschitzRate.factor R*one) (unit j))
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor) : Γ ⊢[PRAAx]
    distanceBounded (GaussianRadiusExponentialName.sample constantF R j c) qone (cost R) (unit j) := by
  have uj := unit_positive (Γ := Γ) j
  have own := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ j j hr
  have close := distance_radius_mono _ _ _ _ (GaussianRadiusExponentialLipschitzRate.factor R+two) (unit j)
    (GaussianNamedInverseRate.denominator_positive _ j j uj) uj
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) own
  have oneNear := distance_congr (.eqRefl _) (one_at j anchor) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ j j he)
  have oneSmall := distance_radius_mono _ _ _ _ two (unit j) (positive_product _ _ uj uj) uj
    (le_of_eq_add (d := zero) (by ipra_ring)) oneNear
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ uj (distance_symmetric _ _ _ _ uj close) oneSmall)

theorem real_sign_cases (q : PTm n) (hq : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis q) : Γ ⊢[PRAAx]
    GaussianPositiveRealArithmetic.positive q ⋎ GaussianPositiveRealArithmetic.positive (qnegative q) := by
  let c := fstT q
  let u := RationalSupMetric.numeratorOf c
  refine .orE (le_total u.neg u.pos) (.orI₁ (.andI hq.wk Prf.hyp0)) ?_
  have h : (le u.pos u.neg)::Γ ⊢[PRAAx] le u.pos u.neg := Prf.hyp0
  have eq := natEq (eq_add_of_le h)
  have native : (le u.pos u.neg)::Γ ⊢[PRAAx] ZT.eq (-u) (ZT.ofNat (monus u.neg u.pos)) := by
    apply ZT.derive
    simp only [ZT.toZ_neg,ZT.toZ_ofNat]
    simp only [ZT.toZ]
    ipra_simps
    linear_combination eq
  have rep := GaussianRationalHorner.scalar_congr (.eqRefl _) native (.eqRefl _)
    (RationalArithmetic.negative_value (Γ := (le u.pos u.neg)::Γ) c)
  have sign := GaussianRationalL1.nonnegative_of_representation _ _ _ (RationalArgmin.denominator_positive c) rep
  exact .orI₂ (GaussianPositiveRealArithmetic.positive_congr
    (RationalGaussianEmbedding.axis_negative_representation q hq.wk).eqSymm
    (GaussianPositiveRealArithmetic.positive_embed _ sign))

theorem original_sample_bound (f : PR 2) (R x j anchor : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hr : Γ ⊢[PRAAx] realSamples f x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor)
    (hn : Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) oneF (data R (negativeData x)) anchor) : Γ ⊢[PRAAx]
    bounded (ap2 f j x) (cost R) (unit j) := by
  let q := ap2 f j x
  have real := real_sample_at f x j hr
  have pos := constant_near_one f R x q j anchor (GaussianSignedNameExponentialOrder.exponential_own_sample_rate f R x j hf) he
  have neg := constant_near_one (negativeF f) R (negativeData x) (qnegative q) j anchor
    (negative_exponential_sample_rate f R x j hf) hn
  refine .orE (real_sign_cases q real.andE₂) ?_ ?_
  · exact GaussianPositiveExponentialSeparation.original_constant_distance_reflection _ _ _ _ _
      (unit_positive j) real.andE₁.wk Prf.hyp0 pos.wk
  · have b := GaussianPositiveExponentialSeparation.original_constant_distance_reflection _ _ _ _ _
      (unit_positive j) (GaussianRationalMetric.qnegative_canonical q) Prf.hyp0 neg.wk
    exact bound_congr (GaussianDeterminantSignTransport.negative_involution q real.andE₁.wk) (.eqRefl _) (.eqRefl _)
      (GaussianRationalReciprocal.bounded_negative _ _ _ (unit_positive j) b)

theorem requested_observation_slack (f : PR 2) (R x p j anchor : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hr : Γ ⊢[PRAAx] realSamples f x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor)
    (hn : Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) oneF (data R (negativeData x)) anchor) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (ap2 f p x) one (unit p) (cost R+one) j := by
  have old := GaussianNameEquivalence.point_at f x p j hf.andE₁
  have sample := original_sample_bound f R x j anchor hf hr he hn
  have sum := GaussianRationalReciprocal.bounded_sum _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive j)) (unit_positive j) old sample
  have eq : Γ ⊢[PRAAx] GaussianRationalHorner.qadd (qsub (ap2 f p x) (ap2 f j x)) (ap2 f j x) ≐ ap2 f p x :=
    (GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans
      (GaussianRationalLinearProduct.add_sub_right _ _ (real_sample_at f x p hr).andE₁)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive j)) (unit_positive j))
    (positive_product _ _ (unit_positive p) (unit_positive j))
    (le_of_eq_add (d := zero) (by unfold unit; ipra_ring))
    (bound_congr eq (.eqRefl _) (.eqRefl _) sum)

theorem original_observation_zero (f : PR 2) (R x p anchor : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hr : Γ ⊢[PRAAx] realSamples f x)
    (he : Γ ⊢[PRAAx] crossEquivalent (nameF f) oneF (data R x) anchor)
    (hn : Γ ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) oneF (data R (negativeData x)) anchor) : Γ ⊢[PRAAx]
    bounded (ap2 f p x) one (unit p) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (cost R+one) (unit_positive p)
  have fs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hr.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent (nameF f) oneF (data (Syn.shift R) (Syn.shift x)) (Syn.shift anchor) := by
    simpa [Fm.shift,Syn.shift] using he.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] crossEquivalent (nameF (negativeF f)) oneF (data (Syn.shift R) (negativeData (Syn.shift x))) (Syn.shift anchor) := by
    simpa [Fm.shift,Syn.shift] using hn.shift
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,subst_cost,PTm.subst_add,GaussianCoefficientNameBounds.subst_unit,
    subst_ap2,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    requested_observation_slack f (Syn.shift R) (Syn.shift x) (Syn.shift p) (var 0) (Syn.shift anchor) fs rs es ns

theorem real_named_exponential_unit_observation_reflection_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((input f (var 0) (var 1) ⋏ realSamples f (var 1)) ⟶
      (crossEquivalent (nameF f) oneF (data (var 0) (var 1)) (var 3) ⋏
       crossEquivalent (nameF (negativeF f)) oneF (data (var 0) (negativeData (var 1))) (var 3)) ⟶
        bounded (ap2 f (var 2) (var 1)) one (unit (var 2))) :=
  closeUniv 4 (.impI (.impI (original_observation_zero f _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianRealNameExponentialUnitReflection

import IPRADerivations.Analysis.Exponential.GaussianSignedRealExponentialOrder
import IPRADerivations.Analysis.Exponential.GaussianRadiusExponentialLipschitzRate

/-!
# Original signed real name order through the actual exponential

At one numerical auxiliary precision, compare the original input names
with their own actual constant observations. Signed rational exponential
order compares those constants; the verified common-radius Lipschitz
rate bounds both original names against them. A single finite scalar gap
removes the common auxiliary error. The source predicates concern only
the actual input samples, with no output-order or output-sign premise.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianSignedNameExponentialOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at sampleOrder order_at scalar_coordinate_distance)
open GaussianRadiusExponentialName (input nameF data)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realSamples (f : PR 2) (x : PTm n) : Fm PTm n := .all
  (GaussianRationalHorner.canonical (ap2 f (var 0) (Syn.shift x)) ⋏
    RationalGaussianEmbedding.axis (ap2 f (var 0) (Syn.shift x)))
@[simp] theorem subst_realSamples {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x : PTm n) :
    (realSamples f x).subst σ = realSamples f (Syn.subst σ x) := by simp [realSamples,Syn.subst_shift,Syn.shift_subst]
theorem real_sample_at (f : PR 2) (x j : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 f j x) ⋏ RationalGaussianEmbedding.axis (ap2 f j x) := by
  simpa [realSamples] using h.allE j

theorem constant_input (q R : PTm n) (h : Γ ⊢[PRAAx] bounded q R one) : Γ ⊢[PRAAx] input constantF R q := by
  refine .andI (constant_regular q) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift q) (Syn.shift R) one := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (Syn.shift q)).eqSymm (.eqRefl _) (.eqRefl _) hs

theorem constant_equal_cross (q r : PTm n) (e : Γ ⊢[PRAAx] q ≐ r) : Γ ⊢[PRAAx] crossEquivalent constantF constantF q r := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (constant_regular _) (constant_regular _)
  refine .allI ?_
  have es : Γ.map Fm.shift ⊢[PRAAx] Syn.shift q ≐ Syn.shift r := by simpa [Fm.shift,Syn.shift] using e.shift
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift] using
    (constant_at (var 0) (Syn.shift q)).eqTrans (es.eqTrans (constant_at (var 0) (Syn.shift r)).eqSymm)

theorem constant_real_order (q r R : PTm n)
    (hq : Γ ⊢[PRAAx] GaussianRationalHorner.canonical q ⋏ RationalGaussianEmbedding.axis q)
    (hr : Γ ⊢[PRAAx] GaussianRationalHorner.canonical r ⋏ RationalGaussianEmbedding.axis r)
    (bq : Γ ⊢[PRAAx] bounded q R one) (br : Γ ⊢[PRAAx] bounded r R one)
    (h : Γ ⊢[PRAAx] RationalArgmin.rationalLE (fstT q) (fstT r)) : Γ ⊢[PRAAx]
    realOrder (nameF constantF) (nameF constantF) (data R q) (data R r) := by
  let Q := RationalGaussianEmbedding.embed (fstT q)
  let T := RationalGaussianEmbedding.embed (fstT r)
  have qeq := RationalGaussianEmbedding.canonical_axis_roundtrip (Γ := Γ) q hq.andE₁ hq.andE₂
  have req := RationalGaussianEmbedding.canonical_axis_roundtrip (Γ := Γ) r hr.andE₁ hr.andE₂
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF R
    (GaussianNameBounds.U constantF Q) q Q (constant_input q R bq) (exponential_input constantF Q (constant_regular _))
    (constant_equal_cross q Q qeq.eqSymm)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF
    (GaussianNameBounds.U constantF T) R T r (exponential_input constantF T (constant_regular _)) (constant_input r R br)
    (constant_equal_cross T r req)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ left right
    (GaussianSignedRealExponentialOrder.original_signed_exponential_order (fstT q) (fstT r) h)

theorem own_sample_rate_at (f : PR 2) (x j p q : PTm n) (hf : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 constantF q (ap2 f j x))
      (rateNumerator one (unit j) p q) (rateDenominator (unit j) p q) := by
  have old := GaussianNameEquivalence.point_at f x p j hf
  apply GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (constant_at q (ap2 f j x)).eqSymm (.eqRefl _) (.eqRefl _)
  apply GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive j))
    (GaussianNamedInverseRate.denominator_positive _ p q (unit_positive j)) _ old
  exact le_of_eq_add (d := unit j*unit j*unit p*unit p) (by unfold rateNumerator rateDenominator; ipra_ring)

theorem own_sample_rate (f : PR 2) (x j : PTm n) (hf : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f x) : Γ ⊢[PRAAx]
    independentRate f constantF x (ap2 f j x) one (unit j) := by
  refine .allI (.allI ?_)
  have fs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN f (Syn.shift (Syn.shift x)) :=
    by simpa [Fm.shift,Syn.shift] using hf.shift.shift
  simpa only [independentRate,Syn.shift,subst_ap2,GaussianCoefficientNameBounds.subst_unit,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using own_sample_rate_at f
    (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift j)) (var 1) (var 0) fs

theorem exponential_own_sample_rate (f : PR 2) (R x j : PTm n) (hf : Γ ⊢[PRAAx] input f R x) : Γ ⊢[PRAAx]
    independentRate (nameF f) (nameF constantF) (data R x) (data R (ap2 f j x))
      (GaussianRadiusExponentialLipschitzRate.factor R*one) (unit j) :=
  GaussianRadiusExponentialLipschitzRate.independent_rate f constantF R x (ap2 f j x) one (unit j)
    (.andI (unit_positive j) (.andI hf (.andI
      (constant_input _ R (GaussianRadiusExponentialName.bounded_samples_at f R x j hf.andE₂))
      (own_sample_rate f x j hf.andE₁))))

def cost (R : PTm n) : PTm n := two*GaussianRadiusExponentialLipschitzRate.factor R+num 4
@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (cost R) = cost (Syn.subst σ R) := by simp [cost]

theorem budget (f g : PR 2) (R x y p q j : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (ho : Γ ⊢[PRAAx] sampleOrder f g x y) : Γ ⊢[PRAAx]
    GaussianNamedRealOrderTransport.upperSlack
      (fstT (ap2 (nameF f) p (data R x))) (fstT (ap2 (nameF g) q (data R y)))
      (unit p+unit q) (unit p*unit q) (cost R) j := by
  have dl := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p j (exponential_own_sample_rate f R x j hf)
  have dr := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ q j (exponential_own_sample_rate g R y j hg)
  have lp := GaussianNamedInverseRate.denominator_positive (Γ := Γ) (unit j) p j (unit_positive j)
  have rp := GaussianNamedInverseRate.denominator_positive (Γ := Γ) (unit j) q j (unit_positive j)
  have left := RationalValueBounds.upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ lp dl)
  have right := RationalValueBounds.upper_of_radius _ _ _ _ (RationalValueBounds.radius_symmetric _ _ _ _
    (scalar_coordinate_distance _ _ _ _ rp dr))
  have middle := real_order_at _ _ _ _ j j (constant_real_order (ap2 f j x) (ap2 g j y) R
    (real_sample_at f x j fr) (real_sample_at g y j gr)
    (GaussianRadiusExponentialName.bounded_samples_at f R x j hf.andE₂)
    (GaussianRadiusExponentialName.bounded_samples_at g R y j hg.andE₂) (order_at f g x y j ho))
  have joined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _
    (RationalValueBounds.upper_triangle _ _ _ _ _ _ _ left middle) right
  apply RationalValueBounds.upper_mono _ _ _ _ _ _
    (GaussianRationalHorner.positive_product _ _
      (GaussianRationalHorner.positive_product _ _ lp
        (GaussianRationalHorner.positive_product _ _ (unit_positive j) (unit_positive j))) rp) joined
  exact le_of_eq_add (d := zero) (by unfold cost rateNumerator rateDenominator; ipra_ring)

theorem observations (f g : PR 2) (R x y p q : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (ho : Γ ⊢[PRAAx] sampleOrder f g x y) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (ap2 (nameF f) p (data R x))) (fstT (ap2 (nameF g) q (data R y)))
      (unit p+unit q) (unit p*unit q) :=
  GaussianNamedRealOrderTransport.remove_upper_slack _ _ _ _ (cost R)
    (budget f g R x y p q (GaussianNamedRealOrderTransport.precision
      (fstT (ap2 (nameF f) p (data R x))) (fstT (ap2 (nameF g) q (data R y))) (unit p*unit q) (cost R)) hf hg fr gr ho)

theorem original_signed_name_order (f g : PR 2) (R x y : PTm n)
    (hf : Γ ⊢[PRAAx] input f R x) (hg : Γ ⊢[PRAAx] input g R y)
    (fr : Γ ⊢[PRAAx] realSamples f x) (gr : Γ ⊢[PRAAx] realSamples g y)
    (ho : Γ ⊢[PRAAx] sampleOrder f g x y) : Γ ⊢[PRAAx]
    realOrder (nameF f) (nameF g) (data R x) (data R y) := by
  refine .allI (.allI ?_)
  have fs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input f (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) :=
    by simpa [Fm.shift,Syn.shift] using hf.shift.shift
  have gs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] input g (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift y)) :=
    by simpa [Fm.shift,Syn.shift] using hg.shift.shift
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift (Syn.shift x)) :=
    by simpa [Fm.shift,Syn.shift] using fr.shift.shift
  have ts : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] realSamples g (Syn.shift (Syn.shift y)) :=
    by simpa [Fm.shift,Syn.shift] using gr.shift.shift
  have os : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] sampleOrder f g (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) :=
    by simpa [Fm.shift,Syn.shift] using ho.shift.shift
  simpa only [realOrder,Syn.shift,GaussianRadiusExponentialName.subst_data] using observations f g
    (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y)) (var 1) (var 0) fs gs rs ts os

theorem original_signed_name_exponential_order_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (input f (var 0) (var 1) ⟶ input g (var 0) (var 2) ⟶ realSamples f (var 1) ⟶ realSamples g (var 2) ⟶
      sampleOrder f g (var 1) (var 2) ⟶ realOrder (nameF f) (nameF g) (data (var 0) (var 1)) (data (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (.impI (.impI
    (original_signed_name_order f g _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianSignedNameExponentialOrder

import IPRADerivations.Analysis.RationalArithmetic.Distances.Scalar.RationalPointDistance
import IPRADerivations.Analysis.RationalArithmetic.Intervals.RationalHausdorffConcat
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalValueBounds

/-!
# Point-to-list distance variation at original rational coordinates

Finite-demand `lem:aggregate-calculus`, clause 5. The two minima use their
actual independently normalized point/list pools. The actual nearest target
index is followed by an actual nearest cover index in the other list. Both
directions are proved on the original coordinates before independent
denominators are combined. No distance comparison or cover is assumed in
the own-value theorem.

The point/point metric is the actual point-distance program with a singleton
target. Its exact radius interpretation is proved by singleton lookup. All
numerical points, lists, dimensions, indices and rational budgets are internal.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalPointDistanceVariation

open_ipra
open LeanProofs.IPRA.Analysis.RationalHausdorff
  (pointRadius coordinateRadius crossNumerator denominatorProduct originalClose)
open LeanProofs.IPRA.Analysis.RationalHausdorffTriangle (pointRadius_triangle)
open LeanProofs.IPRA.Analysis.RationalHausdorffConcat (pointRadius_congr)
open LeanProofs.IPRA.Analysis.RationalSupMetric (rationalCode numeratorOf denominatorOf)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (ad_le_of ad_mul)
export RationalHausdorff (reverse_close)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Original-coordinate symmetry and the actual point/point metric -/

theorem coordinate_radius_symmetric (x y k A B : PTm n)
    (h : Γ ⊢[PRAAx] coordinateRadius x y k A B) : Γ ⊢[PRAAx] coordinateRadius y x k A B := by
  have e : Γ ⊢[PRAAx] zabs (crossNumerator y x k) ≐ zabs (crossNumerator x y k) :=
    (zabs_congr (v := -(crossNumerator x y k)) (by
      simp only [crossNumerator,ZT.toZ_sub,ZT.toZ_neg]
      ring)).eqTrans (zabs_neg _)
  exact le_congr (congrMul (.eqRefl _) e).eqSymm (by unfold denominatorProduct; ipra_ring) h

theorem point_radius_symmetric (x y d A B : PTm n)
    (h : Γ ⊢[PRAAx] pointRadius x y d A B) : Γ ⊢[PRAAx] pointRadius y x d A B := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] pointRadius (Syn.shift x) (Syn.shift y) (Syn.shift d) (Syn.shift A) (Syn.shift B) := by
    simpa only [Fm.shift,RationalHausdorff.subst_pointRadius,Syn.shift] using h.shift.wk
  exact coordinate_radius_symmetric _ _ _ _ _ (RationalHausdorff.pointRadius_at _ _ _ _ _ _ hs Prf.hyp0)

theorem singleton_entry (w i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length (RationalPointDistance.singleton w))) :
    Γ ⊢[PRAAx] entry (RationalPointDistance.singleton w) i ≐ w := by
  have bound := lt_congr (.eqRefl _) (RationalPointDistance.singleton_length w) hi
  simpa [RationalPointDistance.singleton,inst2] using
    sequence_decode (Γ := Γ) (var 1 : PTm 2) (x := w) bound

def pointNumerator (z w d : PTm n) : PTm n :=
  RationalPointDistance.numerator z (RationalPointDistance.singleton w) d
def pointDenominator (z w d : PTm n) : PTm n :=
  RationalPointDistance.denominator z (RationalPointDistance.singleton w) d
def pointCode (z w d : PTm n) : PTm n := pairT (pointNumerator z w d) (pointDenominator z w d)

ipra_subst pointNumerator
ipra_subst pointDenominator
ipra_subst pointCode

theorem point_denominator_positive (z w d : PTm n) : Γ ⊢[PRAAx] le one (pointDenominator z w d) :=
  RationalPointDistance.denominator_positive _ _ _

theorem point_radius_of_bound (z w d A B : PTm n)
    (h : Γ ⊢[PRAAx] le (B*pointNumerator z w d) (A*pointDenominator z w d)) :
    Γ ⊢[PRAAx] pointRadius z w d A B := by
  have nonempty : Γ ⊢[PRAAx] le one (length (RationalPointDistance.singleton w)) :=
    le_congr (.eqRefl _) (RationalPointDistance.singleton_length w).eqSymm (le_refl _)
  have selected := RationalPointDistance.selected_radius z (RationalPointDistance.singleton w) d A B nonempty h
  exact pointRadius_congr (.eqRefl _)
    (singleton_entry w _ (RationalPointDistance.selected_spec _ _ _ nonempty)) selected

theorem point_bound_of_radius (z w d A B : PTm n)
    (h : Γ ⊢[PRAAx] pointRadius z w d A B) :
    Γ ⊢[PRAAx] le (B*pointNumerator z w d) (A*pointDenominator z w d) :=
  RationalPointDistance.bound_of_point_hit _ _ _ _ _
    (RationalPointDistance.pointHit_intro _ _ _ _ _ zero (RationalPointDistance.singleton_index w)
      (pointRadius_congr (.eqRefl _) (RationalPointDistance.singleton_zero w).eqSymm h))

theorem point_own_radius (z w d : PTm n) :
    Γ ⊢[PRAAx] pointRadius z w d (pointNumerator z w d) (pointDenominator z w d) :=
  point_radius_of_bound _ _ _ _ _ (le_congr (.eqRefl _) (mul_comm _ _) (le_refl _))

/-! ## Actual witness transfer from one point/list minimum to the other -/

def transferIndex (w S T d : PTm n) : PTm n :=
  RationalNearest.selected T S d (RationalPointDistance.selected w T d)

ipra_subst transferIndex

theorem transfer_index_range (w S T d : PTm n) (hS : Γ ⊢[PRAAx] le one (length S)) :
    Γ ⊢[PRAAx] lt (transferIndex w S T d) (length S) := RationalNearest.selected_spec _ _ _ _ hS

def transferNumerator (w T d A B C D : PTm n) : PTm n :=
  (A*RationalPointDistance.denominator w T d+RationalPointDistance.numerator w T d*B)*D+
    C*(B*RationalPointDistance.denominator w T d)
def transferDenominator (w T d B D : PTm n) : PTm n :=
  (B*RationalPointDistance.denominator w T d)*D

theorem transfer_radius (z w S T d A B C D : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hpoint : Γ ⊢[PRAAx] pointRadius z w d A B) (hclose : Γ ⊢[PRAAx] originalClose S T d C D) :
    Γ ⊢[PRAAx] pointRadius z (entry S (transferIndex w S T d)) d
      (transferNumerator w T d A B C D) (transferDenominator w T d B D) := by
  have target := RationalPointDistance.selected_spec w T d hT
  have nearest := RationalPointDistance.selected_radius w T d
    (RationalPointDistance.numerator w T d) (RationalPointDistance.denominator w T d) hT
    (le_congr (.eqRefl _) (mul_comm _ _) (le_refl _))
  have cover := RationalNearest.cover_selected_radius T S d (RationalPointDistance.selected w T d) C D
    target hS (reverse_close S T d C D hclose)
  exact pointRadius_triangle _ _ _ _ _ _ _ _ (pointRadius_triangle _ _ _ _ _ _ _ _ hpoint nearest) cover

theorem transfer_bound (z w S T d A B C D : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hpoint : Γ ⊢[PRAAx] pointRadius z w d A B) (hclose : Γ ⊢[PRAAx] originalClose S T d C D) :
    Γ ⊢[PRAAx] le (transferDenominator w T d B D*RationalPointDistance.numerator z S d)
      (transferNumerator w T d A B C D*RationalPointDistance.denominator z S d) :=
  RationalPointDistance.bound_of_point_hit _ _ _ _ _ (RationalPointDistance.pointHit_intro _ _ _ _ _
    (transferIndex w S T d) (transfer_index_range w S T d hS)
      (transfer_radius _ _ _ _ _ _ _ _ _ hS hT hpoint hclose))

/-! ## Both directional inequalities on independent rational scales -/

theorem directional_bound (z w S T d A B C D : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hpoint : Γ ⊢[PRAAx] pointRadius z w d A B) (hclose : Γ ⊢[PRAAx] originalClose S T d C D) :
    Γ ⊢[PRAAx] le
      ((B*D)*(RationalPointDistance.numerator z S d*RationalPointDistance.denominator w T d))
      ((B*D)*(RationalPointDistance.numerator w T d*RationalPointDistance.denominator z S d)+
        (A*D+C*B)*(RationalPointDistance.denominator z S d*RationalPointDistance.denominator w T d)) :=
  le_congr (by unfold transferDenominator; ipra_ring) (by unfold transferNumerator; ipra_ring)
    (transfer_bound _ _ _ _ _ _ _ _ _ hS hT hpoint hclose)

theorem variation_cross (z w S T d A B C D : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hpoint : Γ ⊢[PRAAx] pointRadius z w d A B) (hclose : Γ ⊢[PRAAx] originalClose S T d C D) :
    Γ ⊢[PRAAx] le
      ((B*D)*ad (RationalPointDistance.numerator z S d*RationalPointDistance.denominator w T d)
        (RationalPointDistance.numerator w T d*RationalPointDistance.denominator z S d))
      ((A*D+C*B)*(RationalPointDistance.denominator z S d*RationalPointDistance.denominator w T d)) := by
  have forward := directional_bound _ _ _ _ _ _ _ _ _ hS hT hpoint hclose
  have reverse := directional_bound w z T S d A B C D hT hS
    (point_radius_symmetric _ _ _ _ _ hpoint) (reverse_close _ _ _ _ _ hclose)
  have both := ad_le_of forward (le_congr (.eqRefl _) (by ipra_ring) reverse)
  exact le_congr (ad_mul _ _ _) (.eqRefl _) both

/-- Standard scalar code for the actual rational point/list distance. -/
def scalarCode (z S d : PTm n) : PTm n :=
  rationalCode (ZT.ofNat (RationalPointDistance.numerator z S d)) (RationalPointDistance.denominator z S d)

ipra_subst scalarCode [rationalCode, ZT.ofNat]

theorem scalar_numerator (z S d : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (numeratorOf (scalarCode z S d)) (ZT.ofNat (RationalPointDistance.numerator z S d)) :=
  RationalSupMetric.rationalCode_numerator _ _

theorem scalar_denominator (z S d : PTm n) :
    Γ ⊢[PRAAx] denominatorOf (scalarCode z S d) ≐ RationalPointDistance.denominator z S d :=
  RationalSupMetric.rationalCode_denominator _ _ (RationalPointDistance.denominator_positive _ _ _)

theorem scalar_cross_absolute (z w S T d : PTm n) :
    Γ ⊢[PRAAx] zabs (RationalValueBounds.cross (scalarCode z S d) (scalarCode w T d)) ≐
      ad (RationalPointDistance.numerator z S d*RationalPointDistance.denominator w T d)
        (RationalPointDistance.numerator w T d*RationalPointDistance.denominator z S d) := by
  apply zabs_congr (v := ⟨RationalPointDistance.numerator z S d*RationalPointDistance.denominator w T d,
    RationalPointDistance.numerator w T d*RationalPointDistance.denominator z S d⟩)
  have a := ZT.toZ_eq (scalar_numerator (Γ := Γ) z S d)
  have b := ZT.toZ_eq (scalar_numerator (Γ := Γ) w T d)
  simp only [RationalValueBounds.cross,ZT.toZ_sub,ZT.toZ_mul,ZT.toZ_ofNat] at a b ⊢
  rw [a,b,natEq (scalar_denominator (Γ := Γ) z S d),natEq (scalar_denominator (Γ := Γ) w T d)]
  simp only [ZT.toZ,Q.mk_mul,map_mul]

/-- Literal source clause 5 with genuine point-radius and Hausdorff-radius
input contracts. The two distance samples retain their independent positive
denominators; the budget is exactly `A/B+C/D`. -/
theorem variation_radius (z w S T d A B C D : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (_hB : Γ ⊢[PRAAx] le one B) (_hD : Γ ⊢[PRAAx] le one D)
    (hpoint : Γ ⊢[PRAAx] pointRadius z w d A B) (hclose : Γ ⊢[PRAAx] originalClose S T d C D) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (scalarCode z S d) (scalarCode w T d) (A*D+C*B) (B*D) := by
  have assoc : Γ ⊢[PRAAx]
      (A*D+C*B)*(RationalPointDistance.denominator z S d*RationalPointDistance.denominator w T d) ≐
        (A*D+C*B)*RationalPointDistance.denominator z S d*RationalPointDistance.denominator w T d := by ipra_ring
  exact le_congr (congrMul (.eqRefl _) (scalar_cross_absolute z w S T d)).eqSymm
    (assoc.eqTrans (congrMul (congrMul (.eqRefl _) (scalar_denominator z S d)) (scalar_denominator w T d)).eqSymm)
      (variation_cross _ _ _ _ _ _ _ _ _ hS hT hpoint hclose)

/-- Source clause 5 evaluated at the actual point/point and original-pair
Hausdorff programs. No bound, cover or successful-search premise is given. -/
theorem own_value_variation (z w S T d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] RationalValueBounds.radius (scalarCode z S d) (scalarCode w T d)
      (pointNumerator z w d*RationalHausdorff.denominator S T d+
        RationalHausdorff.numerator S T d*pointDenominator z w d)
      (pointDenominator z w d*RationalHausdorff.denominator S T d) :=
  variation_radius _ _ _ _ _ _ _ _ _ hS hT (point_denominator_positive _ _ _)
    (RationalSupMetric.commonDenominator_one_le _ _) (point_own_radius _ _ _)
      (RationalHausdorffTriangle.own_cover S T d hS hT)

/-! ## Actual rational difference/budget output and public program metadata -/

def differenceNumerator (z w S T d : PTm n) : PTm n :=
  ad (RationalPointDistance.numerator z S d*RationalPointDistance.denominator w T d)
    (RationalPointDistance.numerator w T d*RationalPointDistance.denominator z S d)
def differenceDenominator (z w S T d : PTm n) : PTm n :=
  RationalPointDistance.denominator z S d*RationalPointDistance.denominator w T d
def budgetNumerator (z w S T d : PTm n) : PTm n :=
  pointNumerator z w d*RationalHausdorff.denominator S T d+
    RationalHausdorff.numerator S T d*pointDenominator z w d
def budgetDenominator (z w S T d : PTm n) : PTm n :=
  pointDenominator z w d*RationalHausdorff.denominator S T d
def variationCode (z w S T d : PTm n) : PTm n :=
  pairT (pairT (differenceNumerator z w S T d) (differenceDenominator z w S T d))
    (pairT (budgetNumerator z w S T d) (budgetDenominator z w S T d))

ipra_subst differenceNumerator [ad]
ipra_subst differenceDenominator
ipra_subst budgetNumerator
ipra_subst budgetDenominator
ipra_subst variationCode

theorem output_denominators_positive (z w S T d : PTm n) :
    Γ ⊢[PRAAx] le one (differenceDenominator z w S T d) ⋏ le one (budgetDenominator z w S T d) :=
  .andI (le_congr (one_mul one) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (RationalPointDistance.denominator_positive z S d)
      (RationalPointDistance.denominator_positive w T d)))
    (le_congr (one_mul one) (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (point_denominator_positive z w d)
        (RationalSupMetric.commonDenominator_one_le _ _)))

theorem own_value_cross (z w S T d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] le (budgetDenominator z w S T d*differenceNumerator z w S T d)
      (budgetNumerator z w S T d*differenceDenominator z w S T d) :=
  variation_cross _ _ _ _ _ _ _ _ _ hS hT (point_own_radius z w d)
    (RationalHausdorffTriangle.own_cover S T d hS hT)

def scalarF : PR 3 := PTm.toPR (scalarCode (var 0) (var 1) (var 2))
def pointF : PR 3 := PTm.toPR (pointCode (var 0) (var 1) (var 2))
def transferF : PR 4 := PTm.toPR (transferIndex (var 0) (var 1) (var 2) (var 3))
def programF : PR 5 := PTm.toPR (variationCode (var 0) (var 1) (var 2) (var 3) (var 4))

theorem scalar_at (z S d : PTm n) : Γ ⊢[PRAAx] ap3 scalarF z S d ≐ scalarCode z S d := by
  simpa [scalarF,ap3] using toPR_eq (Γ := Γ) (scalarCode (var 0) (var 1) (var 2) : PTm 3) ![z,S,d]
theorem point_at (z w d : PTm n) : Γ ⊢[PRAAx] ap3 pointF z w d ≐ pointCode z w d := by
  simpa [pointF,ap3] using toPR_eq (Γ := Γ) (pointCode (var 0) (var 1) (var 2) : PTm 3) ![z,w,d]
theorem transfer_at (w S T d : PTm n) :
    Γ ⊢[PRAAx] ConciseIPRA.PTm.app transferF ![w,S,T,d] ≐ transferIndex w S T d := by
  simpa [transferF] using toPR_eq (Γ := Γ) (transferIndex (var 0) (var 1) (var 2) (var 3) : PTm 4) ![w,S,T,d]
theorem program_at (z w S T d : PTm n) :
    Γ ⊢[PRAAx] RationalHausdorff.apply5 programF z w S T d ≐ variationCode z w S T d := by
  simpa [programF,RationalHausdorff.apply5] using
    toPR_eq (Γ := Γ) (variationCode (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,w,S,T,d]

theorem program_difference_numerator (z w S T d : PTm n) : Γ ⊢[PRAAx]
    fstT (fstT (RationalHausdorff.apply5 programF z w S T d)) ≐ differenceNumerator z w S T d :=
  (program_at _ _ _ _ _).fstE.fstE
theorem program_difference_denominator (z w S T d : PTm n) : Γ ⊢[PRAAx]
    sndT (fstT (RationalHausdorff.apply5 programF z w S T d)) ≐ differenceDenominator z w S T d :=
  (program_at _ _ _ _ _).fstE.sndE
theorem program_budget_numerator (z w S T d : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (RationalHausdorff.apply5 programF z w S T d)) ≐ budgetNumerator z w S T d :=
  (program_at _ _ _ _ _).sndE.fstE
theorem program_budget_denominator (z w S T d : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (RationalHausdorff.apply5 programF z w S T d)) ≐ budgetDenominator z w S T d :=
  (program_at _ _ _ _ _).sndE.sndE

theorem code_variation (z w S T d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) : Γ ⊢[PRAAx]
    le (sndT (sndT (RationalHausdorff.apply5 programF z w S T d))*fstT (fstT (RationalHausdorff.apply5 programF z w S T d)))
      (fstT (sndT (RationalHausdorff.apply5 programF z w S T d))*sndT (fstT (RationalHausdorff.apply5 programF z w S T d))) :=
  le_congr (congrMul (program_budget_denominator _ _ _ _ _).eqSymm (program_difference_numerator _ _ _ _ _).eqSymm)
    (congrMul (program_budget_numerator _ _ _ _ _).eqSymm (program_difference_denominator _ _ _ _ _).eqSymm)
      (own_value_cross z w S T d hS hT)

def checkerTerm (z w S T d : PTm n) : PTm n :=
  eqb (monus (budgetDenominator z w S T d*differenceNumerator z w S T d)
    (budgetNumerator z w S T d*differenceDenominator z w S T d)) zero
def checkerF : PR 5 := PTm.toPR (checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4))

theorem checker_at (z w S T d : PTm n) :
    Γ ⊢[PRAAx] RationalHausdorff.apply5 checkerF z w S T d ≐ checkerTerm z w S T d := by
  simpa [checkerF,checkerTerm,RationalHausdorff.apply5] using
    toPR_eq (Γ := Γ) (checkerTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![z,w,S,T,d]

theorem checker_accepts (z w S T d : PTm n)
    (hS : Γ ⊢[PRAAx] le one (length S)) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] RationalHausdorff.apply5 checkerF z w S T d ≐ one :=
  (checker_at z w S T d).eqTrans (eqb_of_eq (own_value_cross z w S T d hS hT))

theorem point_metric_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (Fm.iff (pointRadius (var 0) (var 1) (var 2) (var 3) (var 4))
      (le (var 4*pointNumerator (var 0) (var 1) (var 2)) (var 3*pointDenominator (var 0) (var 1) (var 2)))) :=
  closeUniv 5 (.iffI (.impI (point_bound_of_radius _ _ _ _ _ Prf.hyp0))
    (.impI (point_radius_of_bound _ _ _ _ _ Prf.hyp0)))

theorem parameterized_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le one (length (var 2)) ⟶ le one (length (var 3)) ⟶ le one (var 6) ⟶ le one (var 8) ⟶
      pointRadius (var 0) (var 1) (var 4) (var 5) (var 6) ⟶
      originalClose (var 2) (var 3) (var 4) (var 7) (var 8) ⟶
        RationalValueBounds.radius (scalarCode (var 0) (var 2) (var 4)) (scalarCode (var 1) (var 3) (var 4))
          (var 5*var 8+var 7*var 6) (var 6*var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI
    (variation_radius _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

theorem variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      le (budgetDenominator (var 0) (var 1) (var 2) (var 3) (var 4)*differenceNumerator (var 0) (var 1) (var 2) (var 3) (var 4))
        (budgetNumerator (var 0) (var 1) (var 2) (var 3) (var 4)*differenceDenominator (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (own_value_cross _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem own_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      RationalValueBounds.radius (scalarCode (var 0) (var 2) (var 4)) (scalarCode (var 1) (var 3) (var 4))
        (budgetNumerator (var 0) (var 1) (var 2) (var 3) (var 4))
        (budgetDenominator (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (own_value_variation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem code_variation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      le (sndT (sndT (RationalHausdorff.apply5 programF (var 0) (var 1) (var 2) (var 3) (var 4)))*
          fstT (fstT (RationalHausdorff.apply5 programF (var 0) (var 1) (var 2) (var 3) (var 4))))
        (fstT (sndT (RationalHausdorff.apply5 programF (var 0) (var 1) (var 2) (var 3) (var 4)))*
          sndT (fstT (RationalHausdorff.apply5 programF (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.impI (.impI (code_variation _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem programs_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((RationalHausdorff.apply5 programF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ variationCode (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((ap3 scalarF (var 0) (var 2) (var 4) ≐ scalarCode (var 0) (var 2) (var 4)) ⋏
        ((ap3 pointF (var 0) (var 1) (var 4) ≐ pointCode (var 0) (var 1) (var 4)) ⋏
          ((ConciseIPRA.PTm.app transferF ![var 1,var 2,var 3,var 4] ≐ transferIndex (var 1) (var 2) (var 3) (var 4)) ⋏
            (le one (differenceDenominator (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
              le one (budgetDenominator (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (scalar_at _ _ _) (.andI (point_at _ _ _)
    (.andI (transfer_at _ _ _ _) (output_denominators_positive _ _ _ _ _)))))

theorem checker_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (length (var 2)) ⟶ le one (length (var 3)) ⟶
      RationalHausdorff.apply5 checkerF (var 0) (var 1) (var 2) (var 3) (var 4) ≐ one) :=
  closeUniv 5 (.impI (.impI (checker_accepts _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalPointDistanceVariation

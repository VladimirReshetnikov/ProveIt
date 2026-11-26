import IPRADerivations.Analysis.Gamma.Taylor.GaussianGammaShrinkingGridCoefficientComparison

/-!
# Radius independence of the actual all-degree Gamma coefficient names

The original computed shrinking-grid comparison is joined to the two
ordinary name regularity legs. One actual rational integer-gap query
removes the remaining dyadic error. All original coefficient samplers
are preserved, and no restriction on the coefficient degree remains.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCoefficientRadiusIndependence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaRadiusCoefficientName (nameF data sample)
open GaussianGammaShrinkingGridCoefficientComparison (precision budget)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem later_observation (f : PR 2) (x p t Q : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (ht : Γ ⊢[PRAAx] le t Q) : Γ ⊢[PRAAx]
    distanceBounded (ap2 f p x) (ap2 f Q x) (unit p+unit t) (unit p*unit t) := by
  have grow : Γ ⊢[PRAAx] le (unit t) (unit Q) :=
    GaussianFactorBudget.power_monotone_length two t Q (le_succ_self one) ht
  have radius : Γ ⊢[PRAAx] le ((unit p+unit Q)*(unit p*unit t)) ((unit p+unit t)*(unit p*unit Q)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (unit p*unit Q*unit t) (mul_le_mul_right (unit p*unit p) grow))
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive Q))
    (positive_product _ _ (unit_positive p) (unit_positive t)) radius (GaussianNameEquivalence.point_at f x p Q h)

theorem cofinal_slack (p q t R S e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (sample p R e) (sample q S e))
      (unit p+unit q) (unit p*unit q) (budget R S e+two) t := by
  let Q := precision t e
  let Z := unit p*unit q*unit t
  have hZ : Γ ⊢[PRAAx] le one Z := positive_product _ _
    (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)
  have left := later_observation nameF (data R e) p t Q
    (GaussianGammaAllDegreeCoefficientVariation.name_regular R e hR)
    (GaussianGammaShrinkingGridCoefficientComparison.precision_later t e)
  have right := distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive t))
    (later_observation nameF (data S e) q t Q (GaussianGammaAllDegreeCoefficientVariation.name_regular S e hS)
      (GaussianGammaShrinkingGridCoefficientComparison.precision_later t e))
  have middle := GaussianGammaShrinkingGridCoefficientComparison.original_dyadic_coefficient_comparison t R S e hR hS
  have first : Γ ⊢[PRAAx] distanceBounded (sample p R e) (sample Q R e) ((unit p+unit t)*unit q) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive t)) hZ
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) left
  have second : Γ ⊢[PRAAx] distanceBounded (sample Q R e) (sample Q S e) (budget R S e*(unit p*unit q)) Z :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive t) hZ
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) middle
  have third : Γ ⊢[PRAAx] distanceBounded (sample Q S e) (sample q S e) ((unit q+unit t)*unit p) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive t)) hZ
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) right
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold unit; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ (distance_triangle_same _ _ _ _ _ _ hZ first second) third)

theorem original_observation_overlap (p q R S e : PTm n)
    (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    distanceBounded (sample p R e) (sample q S e) (unit p+unit q) (unit p*unit q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (budget R S e+two)
    (positive_product _ _ (unit_positive p) (unit_positive q))
  have rs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift R) := by simpa [Fm.shift,Syn.shift] using hR.shift
  have ss : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift S) := by simpa [Fm.shift,Syn.shift] using hS.shift
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,
    GaussianGammaRadiusCoefficientName.subst_sample,GaussianGammaShrinkingGridCoefficientComparison.subst_budget,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_add,PTm.subst_mul,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero,Syn.shift] using
      cofinal_slack (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift R) (Syn.shift S) (Syn.shift e) rs ss

theorem original_radius_identity (R S e : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data R e) (data S e) := by
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift R)) := by simpa [Fm.shift,Syn.shift] using hR.shift.shift
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift S)) := by simpa [Fm.shift,Syn.shift] using hS.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,sample,GaussianGammaRadiusCoefficientName.subst_data,Syn.shift,unit,
    GaussianEuclideanPointDistance.unit] using original_observation_overlap (var 1) (var 0)
      (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift e)) rs ss

theorem original_canonical_identity (R e : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    crossEquivalent nameF GaussianGammaHigherCoefficientName.nameF (data R e) (GaussianGammaHigherCoefficientName.data e) :=
  GaussianNameEquivalence.cross_trans _ _ _ _ _ _
    (original_radius_identity R (succ e) e hR (zero_lt_succ e)) (GaussianGammaRadiusCoefficientName.canonical_identity e)

theorem original_all_degree_Gamma_coefficient_radius_independence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 0) ⟶ le one (var 1) ⟶ crossEquivalent nameF nameF (data (var 0) (var 2)) (data (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (original_radius_identity _ _ _ Prf.hyp1 Prf.hyp0)))
theorem original_all_degree_Gamma_coefficient_canonical_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ crossEquivalent nameF GaussianGammaHigherCoefficientName.nameF
      (data (var 0) (var 1)) (GaussianGammaHigherCoefficientName.data (var 1))) :=
  closeUniv 2 (.impI (original_canonical_identity _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCoefficientRadiusIndependence

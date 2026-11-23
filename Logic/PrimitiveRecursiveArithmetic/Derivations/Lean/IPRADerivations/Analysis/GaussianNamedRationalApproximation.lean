import IPRADerivations.Analysis.GaussianNamedInverseRate
import IPRADerivations.Analysis.GaussianGammaCanonicalExponent

/-!
# A regular complex name and its frozen rational observation

A query to a fixed regular input name supplies an actual encoded rational
point. The constant name for that point approximates the original name
within the queried dyadic error. Recoding changes only the representation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRationalApproximation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianEuclideanDistanceName (pointCN)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (recode recode_distance)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- Recode only the frozen query. The observation of the moving input is
the original raw one at p. -/
theorem frozen_observation (f : PR 2) (p x t : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (recode (ap2 f t x))
      (unit p+unit t) (unit p*unit t) := by
  let a := ap2 f p x
  let b := ap2 f t x
  let D := unit p*unit t
  have pos : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive p) (unit_positive t)
  have recoded := distance_symmetric _ _ zero one (le_refl (Γ := Γ) one) (recode_distance b)
  have last := distance_radius_mono _ _ zero one zero D (le_refl one) pos
    (le_of_eq_add (d := zero) (by ipra_ring)) recoded
  have combined := distance_triangle_same a b (recode b) (unit p+unit t) zero D pos
    (GaussianNameEquivalence.point_at f x p t h) last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) combined

theorem frozen_constant_observations (f : PR 2) (p q x t : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 constantF q (recode (ap2 f t x)))
      (rateNumerator one (unit t) p q) (rateDenominator (unit t) p q) := by
  have eps := distance_radius_mono _ _ _ _ (rateNumerator one (unit t) p q) (rateDenominator (unit t) p q)
    (positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive t))
    (denominator_positive _ _ _ (unit_positive t))
    (le_of_eq_add (d := unit p*unit p*unit t*unit t) (by unfold rateNumerator rateDenominator; ipra_ring))
    (frozen_observation f p x t h)
  exact distance_congr (.eqRefl _) (constant_at q _).eqSymm (.eqRefl _) (.eqRefl _) eps

theorem frozen_constant_rate (f : PR 2) (x t : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] independentRate f constantF x (recode (ap2 f t x)) one (unit t) := by
  refine .allI (.allI ?_)
  have hp : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift (Syn.shift x)) := by
    simpa only [Fm.shift,Syn.shift,GaussianEuclideanDistanceName.subst_pointCN] using h.shift.shift
  simpa only [independentRate,Syn.shift,GaussianFastValueCut.subst_recode,
    subst_ap2,GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    frozen_constant_observations f (var 1) (var 0) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift t)) hp

theorem original_named_rational_approximation_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (pointCN f (var 0) ⟶ independentRate f constantF (var 0) (recode (ap2 f (var 1) (var 0)))
        one (unit (var 1))) :=
  closeUniv 2 (.impI (frozen_constant_rate f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedRationalApproximation

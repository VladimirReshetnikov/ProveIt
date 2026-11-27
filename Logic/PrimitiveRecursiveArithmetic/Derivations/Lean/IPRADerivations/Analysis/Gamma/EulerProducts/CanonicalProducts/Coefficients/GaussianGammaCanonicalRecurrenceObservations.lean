import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Coefficients.GaussianGammaCanonicalRecurrenceTerms
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.SlackRemoval.GaussianRationalSlackRemoval

/-!
# Original Gamma coefficient recurrence at independent named observations

The proved original finite recurrence is observed through one arbitrarily
late original source clock. Its canonical current-coefficient error and
the genuine canonical product-sum error retain both actual queries p,q.
Only the auxiliary source-clock error is eliminated by the existing
finite Euclidean gap proof. The resulting bound is
s*2^-p+(s+1)*queryFactor(s+1)*2^-q between the actual scaled canonical
c_(s+1) observation and the literal canonical gamma/zeta coefficient sum.
No recurrence, limit identity or target comparison is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceObservations

open_ipra
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaRecurrenceSourceObservations (cap denominator_positive sourceSum)
open GaussianGammaCanonicalRecurrenceTerms (canonicalSum queryFactor sourceFactor termNumerator)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p q s : PTm n) : PTm n := s*unit q+succ s*queryFactor (succ s)*unit p
def slackCost (s : PTm n) : PTm n := s*cap (succ s)+succ s*sourceFactor (succ s)
ipra_subst numerator
ipra_subst slackCost

theorem original_source_slack (p q t s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (natScale s (sample p (succ s))) (canonicalSum q (succ s)))
      (numerator p q s) (unit p*unit q) (slackCost s) t := by
  have first := distance_congr (Γ := Γ) (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm (unit t) (unit p))
    (GaussianGammaRecurrenceSourceObservations.original_canonical_recurrence_source_error p t s)
  have second := distance_congr (Γ := Γ) (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm (unit t) (unit q))
    (GaussianGammaCanonicalRecurrenceTerms.original_sum_error t q (succ s))
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by unfold numerator slackCost termNumerator unit; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_common_factor _ _ _ _ (unit p) _ (unit q) (unit t)
      (unit_positive p) (unit_positive q) (unit_positive t) first second)

theorem original_canonical_coefficient_recurrence_error (p q s : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (natScale s (sample p (succ s))) (canonicalSum q (succ s))
      (numerator p q s) (unit p*unit q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (slackCost s) (denominator_positive p q)
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,
    GaussianRationalNaturalScale.subst_natScale,GaussianGammaHigherCoefficientName.subst_sample,
    GaussianGammaCanonicalRecurrenceTerms.subst_canonicalSum,subst_numerator,subst_slackCost,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_succ,Syn.shift] using
      original_source_slack (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift s)

theorem original_Gamma_canonical_coefficient_recurrence_independent_named_observations_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (distanceBounded (natScale (var 2) (sample (var 0) (succ (var 2)))) (canonicalSum (var 1) (succ (var 2)))
        (numerator (var 0) (var 1) (var 2)) (unit (var 0)*unit (var 1))) :=
  closeUniv 3 (original_canonical_coefficient_recurrence_error _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceObservations

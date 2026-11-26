import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.GaussianGammaCanonicalRecurrenceTerms
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSlackRemoval

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaRecurrenceSourceObservations (cap denominator_positive sourceSum)
open GaussianGammaCanonicalRecurrenceTerms (canonicalSum queryFactor sourceFactor termNumerator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (p q s : PTm n) : PTm n := s*unit q+succ s*queryFactor (succ s)*unit p
def slackCost (s : PTm n) : PTm n := s*cap (succ s)+succ s*sourceFactor (succ s)
@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (p q s : PTm n) :
    Syn.subst σ (numerator p q s) = numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ s) := by simp [numerator]
@[simp] theorem subst_slackCost {l : ℕ} (σ : Fin n → PTm l) (s : PTm n) :
    Syn.subst σ (slackCost s) = slackCost (Syn.subst σ s) := by simp [slackCost]

theorem original_source_slack (p q t s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (natScale s (sample p (succ s))) (canonicalSum q (succ s)))
      (numerator p q s) (unit p*unit q) (slackCost s) t := by
  let Z := (unit p*unit q)*unit t
  have positive : Γ ⊢[PRAAx] le one Z := GaussianRationalHorner.positive_product _ _
    (denominator_positive p q) (unit_positive t)
  have first : Γ ⊢[PRAAx] distanceBounded (natScale s (sample p (succ s))) (sourceSum t (succ s))
      (s*(cap (succ s)*unit p+unit t)*unit q) Z :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive t p) positive
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
      (GaussianGammaRecurrenceSourceObservations.original_canonical_recurrence_source_error p t s)
  have second : Γ ⊢[PRAAx] distanceBounded (sourceSum t (succ s)) (canonicalSum q (succ s))
      (succ s*termNumerator t q (succ s)*unit p) Z :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive t q) positive
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
      (GaussianGammaCanonicalRecurrenceTerms.original_sum_error t q (succ s))
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by unfold numerator slackCost termNumerator unit; ipra_ring)
    (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ positive first second)

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

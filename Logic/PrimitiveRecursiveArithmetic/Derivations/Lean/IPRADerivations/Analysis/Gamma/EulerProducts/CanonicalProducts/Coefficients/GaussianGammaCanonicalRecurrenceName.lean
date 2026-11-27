import IPRADerivations.Analysis.Gamma.EulerProducts.CanonicalProducts.Coefficients.GaussianGammaCanonicalRecurrenceObservations
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut

/-!
# The literal canonical Gamma coefficient recurrence sum is an actual name

The SAME actual finite sum of global canonical coefficient observations
and full original gamma/zeta weight observations has computed modulus
(s+1)*queryFactor(s+1). Its genuine regularity follows from the proved
independent coefficient recurrence error; only an auxiliary actual
coefficient observation is eliminated by the finite gap theorem. The
original FastValueCut program retimes this SAME sum to a point CN name,
with literal source samples and its computed query budget exposed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceName

open_ipra
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaRecurrenceSourceObservations (denominator_positive)
open GaussianGammaCanonicalRecurrenceTerms (canonicalSum queryFactor)
open GaussianGammaCanonicalRecurrenceObservations (numerator original_canonical_coefficient_recurrence_error)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def modulus (s : PTm n) : PTm n := succ s*queryFactor (succ s)
ipra_subst modulus

theorem regularity_slack (p q t s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (canonicalSum p (succ s)) (canonicalSum q (succ s)))
      (modulus s*(unit p+unit q)) (unit p*unit q) (two*s) t := by
  have first := distance_congr (Γ := Γ) (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm (unit t) (unit p))
    (distance_symmetric _ _ _ _ (denominator_positive t p) (original_canonical_coefficient_recurrence_error t p s))
  have second := distance_congr (Γ := Γ) (.eqRefl _) (.eqRefl _) (.eqRefl _) (mul_comm (unit t) (unit q))
    (original_canonical_coefficient_recurrence_error t q s)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by unfold numerator modulus unit; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_common_factor _ _ _ _ (unit p) _ (unit q) (unit t)
      (unit_positive p) (unit_positive q) (unit_positive t) first second)

theorem original_sum_regularity (p q s : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (canonicalSum p (succ s)) (canonicalSum q (succ s))
      (modulus s*(unit p+unit q)) (unit p*unit q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (two*s) (denominator_positive p q)
  refine .allI ?_
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,
    GaussianGammaCanonicalRecurrenceTerms.subst_canonicalSum,subst_modulus,GaussianCoefficientNameBounds.subst_unit,
    PTm.subst_add,PTm.subst_mul,PTm.subst_succ,PTm.subst_zero,Syn.shift] using
      regularity_slack (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift s)

def rawF : PR 2 := PTm.toPR (canonicalSum (var 0) (succ (var 1)))
def nameF : PR 2 := GaussianFastValueCut.nameF rawF
def data (s : PTm n) : PTm n := GaussianFastValueCut.nameData (modulus s) s
def clock (p s : PTm n) : PTm n := GaussianFastValueCut.exponent (modulus s) p
def sumSample (p s : PTm n) : PTm n := ap2 nameF p (data s)
ipra_subst data
ipra_subst clock
ipra_subst sumSample

theorem raw_at (p s : PTm n) : Γ ⊢[PRAAx] ap2 rawF p s ≐ canonicalSum p (succ s) := by
  simpa [rawF,ap2] using toPR_eq (Γ := Γ) (canonicalSum (var 0) (succ (var 1)) : PTm 2) ![p,s]

theorem raw_regular (s : PTm n) : Γ ⊢[PRAAx] GaussianFastValueCut.regular rawF (modulus s) s := by
  refine .allI (.allI ?_)
  have h := distance_congr (raw_at (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (Syn.shift (Syn.shift s))).eqSymm
    (raw_at (var 0) _).eqSymm (.eqRefl _) (.eqRefl _) (original_sum_regularity _ _ _)
  simpa only [GaussianFastValueCut.regular,subst_modulus,Syn.shift,unit] using h

theorem name_regular (s : PTm n) : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF (data s) :=
  GaussianFastValueCut.name_fast rawF (modulus s) s (raw_regular s)

theorem sample_at (p s : PTm n) : Γ ⊢[PRAAx] sumSample p s ≐ canonicalSum (clock p s) (succ s) :=
  (GaussianFastValueCut.name_at rawF (modulus s) s p).eqTrans
    ((GaussianNameArithmetic.recode_congr (raw_at (clock p s) s)).eqTrans
      (GaussianNamedSmallPerturbationTransport.recode_fixed _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem query_budget (p s : PTm n) : Γ ⊢[PRAAx] le (modulus s*unit p) (unit (clock p s)) :=
  GaussianFastValueCut.query_budget _ _

theorem original_Gamma_literal_canonical_coefficient_recurrence_sum_name_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (GaussianEuclideanDistanceName.pointCN nameF (data (var 0))) :=
  closeUniv 1 (name_regular _)

theorem original_Gamma_literal_recurrence_sum_named_source_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (sumSample (var 0) (var 1) ≐ canonicalSum (clock (var 0) (var 1)) (succ (var 1))) := closeUniv 2 (sample_at _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalRecurrenceName

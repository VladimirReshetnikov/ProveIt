import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaCanonicalRecurrenceObservations
import IPRADerivations.Analysis.Names.GaussianFastValueCut

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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaHigherCoefficientName (sample)
open GaussianGammaRecurrenceSourceObservations (denominator_positive)
open GaussianGammaCanonicalRecurrenceTerms (canonicalSum queryFactor)
open GaussianGammaCanonicalRecurrenceObservations (numerator original_canonical_coefficient_recurrence_error)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def modulus (s : PTm n) : PTm n := succ s*queryFactor (succ s)
@[simp] theorem subst_modulus {l : ℕ} (σ : Fin n → PTm l) (s : PTm n) :
    Syn.subst σ (modulus s) = modulus (Syn.subst σ s) := by simp [modulus]

theorem regularity_slack (p q t s : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (canonicalSum p (succ s)) (canonicalSum q (succ s)))
      (modulus s*(unit p+unit q)) (unit p*unit q) (two*s) t := by
  let Z := (unit p*unit q)*unit t
  have positive : Γ ⊢[PRAAx] le one Z := GaussianRationalHorner.positive_product _ _
    (denominator_positive p q) (unit_positive t)
  have first : Γ ⊢[PRAAx] distanceBounded (canonicalSum p (succ s)) (natScale s (sample t (succ s)))
      (numerator t p s*unit q) Z :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive t p) positive
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring))
      (distance_symmetric _ _ _ _ (denominator_positive t p) (original_canonical_coefficient_recurrence_error t p s))
  have second : Γ ⊢[PRAAx] distanceBounded (natScale s (sample t (succ s))) (canonicalSum q (succ s))
      (numerator t q s*unit p) Z :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive t q) positive
      (le_of_eq_add (d := zero) (by dsimp only [Z]; ipra_ring)) (original_canonical_coefficient_recurrence_error t q s)
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by unfold numerator modulus unit; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ positive first second)

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
@[simp] theorem subst_data {l : ℕ} (σ : Fin n → PTm l) (s : PTm n) :
    Syn.subst σ (data s) = data (Syn.subst σ s) := by simp [data]
@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (p s : PTm n) :
    Syn.subst σ (clock p s) = clock (Syn.subst σ p) (Syn.subst σ s) := by simp [clock]
@[simp] theorem subst_sumSample {l : ℕ} (σ : Fin n → PTm l) (p s : PTm n) :
    Syn.subst σ (sumSample p s) = sumSample (Syn.subst σ p) (Syn.subst σ s) := by simp [sumSample]

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

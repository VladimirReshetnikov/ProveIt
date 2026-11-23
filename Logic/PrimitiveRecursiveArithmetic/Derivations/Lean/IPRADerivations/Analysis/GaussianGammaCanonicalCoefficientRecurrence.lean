import IPRADerivations.Analysis.GaussianGammaCanonicalRecurrenceName
import IPRADerivations.Analysis.GaussianNameEquivalence

/-!
# Actual named canonical Gamma coefficient recurrence C42

The SAME global all-degree coefficient name c_(s+1) is scaled by s with
the original actual named natural-scale program. The actual regular
right name is the literal finite sum of canonical c_j and full original
gamma/zeta weights. Genuine computed clocks spend both proven original
observation errors and establish cross equivalence of these actual names.
Every name regularity/input is proved internally. The zero coefficient
and zero first summand are exact, so the displayed sum is precisely the
original C42 recurrence (including its empty low-degree boundary cases).
No recurrence, coefficient identification or equality of limits is input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCanonicalCoefficientRecurrence

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalNaturalScale (natScale)
open GaussianGammaCanonicalRecurrenceName (modulus sumSample)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def leftF : PR 2 := GaussianNamedNaturalScale.nameF GaussianGammaHigherCoefficientName.nameF
def leftData (s : PTm n) : PTm n := GaussianNamedNaturalScale.data s s (GaussianGammaHigherCoefficientName.data (succ s))
def leftClock (p s : PTm n) : PTm n := GaussianNamedNaturalScale.clock p s
def leftSample (p s : PTm n) : PTm n := ap2 leftF p (leftData s)
@[simp] theorem subst_leftData {l : ℕ} (σ : Fin n → PTm l) (s : PTm n) :
    Syn.subst σ (leftData s) = leftData (Syn.subst σ s) := by simp [leftData]
@[simp] theorem subst_leftClock {l : ℕ} (σ : Fin n → PTm l) (p s : PTm n) :
    Syn.subst σ (leftClock p s) = leftClock (Syn.subst σ p) (Syn.subst σ s) := by simp [leftClock]
@[simp] theorem subst_leftSample {l : ℕ} (σ : Fin n → PTm l) (p s : PTm n) :
    Syn.subst σ (leftSample p s) = leftSample (Syn.subst σ p) (Syn.subst σ s) := by simp [leftSample]

theorem coefficient_input (e : PTm n) : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input
    GaussianGammaHigherCoefficientName.nameF
    (GaussianNameBounds.U GaussianGammaHigherCoefficientName.nameF (GaussianGammaHigherCoefficientName.data e))
    (GaussianGammaHigherCoefficientName.data e) :=
  .andI (GaussianGammaHigherCoefficientName.name_regular e)
    (GaussianNameBounds.all_samples_bounded _ _ (GaussianGammaHigherCoefficientName.name_regular e))

theorem left_regular (s : PTm n) : Γ ⊢[PRAAx] pointCN leftF (leftData s) :=
  GaussianNamedNaturalScale.name_regular _ _ _ _ _ (coefficient_input (succ s)) (le_refl s)

theorem left_sample_at (p s : PTm n) : Γ ⊢[PRAAx]
    leftSample p s ≐ natScale s (GaussianGammaHigherCoefficientName.sample (leftClock p s) (succ s)) :=
  GaussianNamedNaturalScale.sample_at _ _ _ _ _

theorem left_query_budget (p s : PTm n) : Γ ⊢[PRAAx] le (s*unit p) (unit (leftClock p s)) :=
  le_congr (.eqRefl _)
    ((mul_comm _ _).eqTrans (GaussianNamedNaturalScale.clock_unit p s).eqSymm)
      (mul_le_mul_right (unit p) (GaussianNamedNaturalScale.cap_budget s s (le_refl s)))

theorem original_named_observation (p q s : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (leftSample p s) (sumSample q s) (unit p+unit q) (unit p*unit q) := by
  let a := leftClock p s
  let b := GaussianGammaCanonicalRecurrenceName.clock q s
  have first : Γ ⊢[PRAAx] le (s*unit p) (unit a) := left_query_budget p s
  have second : Γ ⊢[PRAAx] le (modulus s*unit q) (unit b) := GaussianGammaCanonicalRecurrenceName.query_budget q s
  have budget : Γ ⊢[PRAAx]
      le (GaussianGammaCanonicalRecurrenceObservations.numerator a b s*(unit p*unit q))
        ((unit p+unit q)*(unit a*unit b)) :=
    le_congr (by unfold GaussianGammaCanonicalRecurrenceObservations.numerator modulus; ipra_ring) (by ipra_ring)
      (add_le_add₂ (mul_le_mul_right (unit b*unit q) first) (mul_le_mul_right (unit a*unit p) second))
  exact distance_congr (left_sample_at p s).eqSymm (GaussianGammaCanonicalRecurrenceName.sample_at q s).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ (GaussianGammaRecurrenceSourceObservations.denominator_positive a b)
      (GaussianGammaRecurrenceSourceObservations.denominator_positive p q) budget
        (GaussianGammaCanonicalRecurrenceObservations.original_canonical_coefficient_recurrence_error a b s))

theorem original_C42 (s : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent leftF GaussianGammaCanonicalRecurrenceName.nameF (leftData s) (GaussianGammaCanonicalRecurrenceName.data s) := by
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,leftSample,GaussianGammaCanonicalRecurrenceName.sumSample,subst_leftData,
    GaussianGammaCanonicalRecurrenceName.subst_data,Syn.shift] using
      original_named_observation (Γ := (Γ.map Fm.shift).map Fm.shift) (var 1) (var 0) (Syn.shift (Syn.shift s))

theorem canonical_zero (p : PTm n) : Γ ⊢[PRAAx] GaussianGammaHigherCoefficientName.sample p zero ≐ qzero :=
  (GaussianGammaHigherCoefficientName.sample_fixed_coefficient p zero).eqTrans
    ((GaussianGammaPolynomialConstantLinear.constant_reader _ _).eqTrans (GaussianGammaPolynomialConstantLinear.whole_constant _ _ _ _))

theorem original_zero_summand (p e : PTm n) : Γ ⊢[PRAAx] GaussianGammaCanonicalRecurrenceTerms.canonicalTerm p e zero ≐ qzero :=
  (qmul_congr (.eqRefl _) (canonical_zero p)).eqTrans (GaussianRationalSyntheticDivision.qmul_zero_right _)

theorem original_nonzero_sum (p s : PTm n) : Γ ⊢[PRAAx]
    GaussianGammaCanonicalRecurrenceTerms.canonicalSum p (succ s) ≐
      GaussianRationalFiniteSum.sum (shiftBody GaussianGammaCanonicalRecurrenceTerms.body) s
        (GaussianGammaCanonicalRecurrenceTerms.data p (succ s)) :=
  (GaussianRationalFiniteSum.sum_shift_first _ _ _).eqTrans
    ((qadd_congr ((GaussianGammaCanonicalRecurrenceTerms.canonical_term_at _ _ _).eqTrans (original_zero_summand _ _)) (.eqRefl _)).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalFiniteSum.sum_canonical _ _ _)))

theorem original_Gamma_canonical_coefficient_recurrence_C42_named_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN leftF (leftData (var 0)) ⋏
      (pointCN GaussianGammaCanonicalRecurrenceName.nameF (GaussianGammaCanonicalRecurrenceName.data (var 0)) ⋏
        crossEquivalent leftF GaussianGammaCanonicalRecurrenceName.nameF (leftData (var 0)) (GaussianGammaCanonicalRecurrenceName.data (var 0)))) :=
  closeUniv 1 (.andI (left_regular _) (.andI (GaussianGammaCanonicalRecurrenceName.name_regular _) (original_C42 _)))

theorem original_Gamma_C42_canonical_zero_summand_vanishes_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianGammaCanonicalRecurrenceTerms.canonicalSum (var 0) (succ (var 1)) ≐
      GaussianRationalFiniteSum.sum (shiftBody GaussianGammaCanonicalRecurrenceTerms.body) (var 1)
        (GaussianGammaCanonicalRecurrenceTerms.data (var 0) (succ (var 1)))) := closeUniv 2 (original_nonzero_sum _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaCanonicalCoefficientRecurrence

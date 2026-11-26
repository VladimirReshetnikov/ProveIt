import IPRADerivations.Analysis.Polynomials.RootFinding.GaussianTranslatedNonconstant
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalSumAlgebra
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianRationalPowerAlgebra

/-!
# Actual synthetic coefficient identities for arbitrary raw fractions

The constructed quotient and remainder recover the canonical value of
each original coefficient. No raw input is identified with its normal
form, and no coefficient identity or common denominator is supplied.
All degrees, coefficient positions, lists and points are internal inputs.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalSyntheticCoefficientValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner
  (qzero qadd qmul horner evaluate canonical positive_product)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant
  (recode recode_congr recode_canonical recode_represents recode_eq)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (quotient qadd_congr qmul_congr qsub_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_represents raw_den_positive)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem qadd_recode_left (a b : PTm n) : Γ ⊢[PRAAx] qadd (recode a) b ≐ qadd a b :=
  (GaussianRationalSumAlgebra.qadd_associative qzero a b).eqTrans
    (recode_eq _ (GaussianRationalHorner.qadd_canonical a b))

theorem qadd_recode_right (a b : PTm n) : Γ ⊢[PRAAx] qadd a (recode b) ≐ qadd a b :=
  (GaussianReciprocalHorner.qadd_commutative a (recode b)).eqTrans
    ((qadd_recode_left b a).eqTrans (GaussianReciprocalHorner.qadd_commutative b a))

theorem qmul_recode_left (a b : PTm n) : Γ ⊢[PRAAx] qmul (recode a) b ≐ qmul a b :=
  GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.qmul_canonical _ _)
    (GaussianRationalHorner.qmul_canonical _ _) (positive_product _ _ (raw_den_positive a) (raw_den_positive b))
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (raw_den_positive a) (raw_den_positive b)
      (recode_represents a) (raw_represents b))
    (GaussianRationalHorner.qmul_represents _ _ _ _ _ _ (raw_den_positive a) (raw_den_positive b)
      (raw_represents a) (raw_represents b))

theorem qmul_recode_right (a b : PTm n) : Γ ⊢[PRAAx] qmul a (recode b) ≐ qmul a b :=
  (GaussianRationalPowerAlgebra.qmul_commutative a (recode b)).eqTrans
    ((qmul_recode_left b a).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative b a))

/-- Cancellation for raw b recovers its canonical value. -/
theorem qadd_sub_recode (a b : PTm n) : Γ ⊢[PRAAx]
    qsub (qadd a b) a ≐ recode b :=
  (qsub_congr (qadd_recode_right a b).eqSymm (.eqRefl _)).eqTrans
    (GaussianRationalSyntheticDivision.qadd_sub_cancel a (recode b) (recode_canonical b))

theorem quotient_recode (C z M i : PTm n) (hi : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    recode (entry (quotient C z M) i) ≐ entry (quotient C z M) i :=
  recode_eq _ (GaussianRationalSyntheticDivision.quotient_coefficient_canonical C z M i hi)

/-- Actual leading coefficient recovery; no canonical input guard. -/
theorem leading_coefficient (C z M : PTm n) (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    recode (entry C zero) ≐ recode (entry (quotient C z M) zero) :=
  ((GaussianRationalSyntheticDivision.quotient_lookup C z M zero hM).eqTrans
    (GaussianRationalSyntheticDivision.first_prefix C z)).eqSymm.eqTrans (quotient_recode C z M zero hM).eqSymm

theorem preceding_prefix (C z M i : PTm n) (hi : Γ ⊢[PRAAx] le one i)
    (hiM : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    horner C z i ≐ entry (quotient C z M) (pred i) := by
  have hp : Γ ⊢[PRAAx] lt (pred i) M := lt_of_le_of_lt
    (le_of_eq_add (d := one) ((RationalIntegerNormalization.positive_form hi).eqTrans (by ipra_ring))) hiM
  exact (congrAp3 GaussianRationalHorner.hornerF (RationalIntegerNormalization.positive_form hi)
    (.eqRefl _) (.eqRefl _)).eqTrans (GaussianRationalSyntheticDivision.quotient_lookup C z M (pred i) hp).eqSymm

/-- Interior descending coefficient reconstruction from the actual two
adjacent quotient entries. All stored original fractions may be raw. -/
theorem interior_coefficient (C z M i : PTm n) (hi : Γ ⊢[PRAAx] le one i)
    (hiM : Γ ⊢[PRAAx] lt i M) : Γ ⊢[PRAAx]
    recode (entry C i) ≐ qsub (recode (entry (quotient C z M) i))
      (qmul z (recode (entry (quotient C z M) (pred i)))) := by
  have recurrence := GaussianRationalSyntheticDivision.quotient_recurrence C z M i hiM
  have hp := preceding_prefix C z M i hi hiM
  have product : Γ ⊢[PRAAx] qmul z (recode (entry (quotient C z M) (pred i))) ≐
      qmul (horner C z i) z :=
    (qmul_recode_right z _).eqTrans ((GaussianRationalPowerAlgebra.qmul_commutative z _).eqTrans
      (qmul_congr hp.eqSymm (.eqRefl _)))
  exact (qadd_sub_recode (qmul (horner C z i) z) (entry C i)).eqSymm.eqTrans
    (qsub_congr (recurrence.eqSymm.eqTrans (quotient_recode C z M i hiM).eqSymm) product.eqSymm)

/-- The tail uses the actual Horner remainder, not a supplied value. -/
theorem constant_coefficient (C z M : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ succ M)
    (hM : Γ ⊢[PRAAx] le one M) : Γ ⊢[PRAAx]
    recode (entry C M) ≐ qsub (evaluate C z)
      (qmul z (recode (entry (quotient C z M) (pred M)))) := by
  have recurrence := GaussianRationalSyntheticDivision.remainder_recurrence C z M hLen hM
  have product : Γ ⊢[PRAAx] qmul z (recode (entry (quotient C z M) (pred M))) ≐
      qmul (entry (quotient C z M) (pred M)) z :=
    (qmul_recode_right z _).eqTrans (GaussianRationalPowerAlgebra.qmul_commutative _ _)
  exact (qadd_sub_recode _ (entry C M)).eqSymm.eqTrans (qsub_congr recurrence.eqSymm product.eqSymm)

theorem singleton_evaluation (C z : PTm n) (hLen : Γ ⊢[PRAAx] length C ≐ one) : Γ ⊢[PRAAx]
    recode (entry C zero) ≐ evaluate C z :=
  (GaussianRationalSyntheticDivision.first_prefix C z).eqSymm.eqTrans
    (congrAp3 GaussianRationalHorner.hornerF hLen.eqSymm (.eqRefl _) (.eqRefl _))

theorem raw_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (qsub (qadd (var 0) (var 1)) (var 0) ≐ recode (var 1)) :=
  closeUniv 2 (qadd_sub_recode _ _)
theorem raw_recoding_arithmetic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((qadd (recode (var 0)) (var 1) ≐ qadd (var 0) (var 1)) ⋏
      ((qmul (recode (var 0)) (var 1) ≐ qmul (var 0) (var 1)) ⋏
        (qmul (var 0) (recode (var 1)) ≐ qmul (var 0) (var 1)))) :=
  closeUniv 2 (.andI (qadd_recode_left _ _) (.andI (qmul_recode_left _ _) (qmul_recode_right _ _)))
theorem actual_leading_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ recode (entry (var 0) zero) ≐ recode (entry (quotient (var 0) (var 1) (var 2)) zero)) :=
  closeUniv 3 (.impI (leading_coefficient _ _ _ Prf.hyp0))
theorem actual_interior_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ lt (var 3) (var 2) ⟶ recode (entry (var 0) (var 3)) ≐
      qsub (recode (entry (quotient (var 0) (var 1) (var 2)) (var 3)))
        (qmul (var 1) (recode (entry (quotient (var 0) (var 1) (var 2)) (pred (var 3)))))) :=
  closeUniv 4 (.impI (.impI (interior_coefficient _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_constant_coefficient_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 2) ⟶ le one (var 2) ⟶ recode (entry (var 0) (var 2)) ≐
      qsub (evaluate (var 0) (var 1))
        (qmul (var 1) (recode (entry (quotient (var 0) (var 1) (var 2)) (pred (var 2)))))) :=
  closeUniv 3 (.impI (.impI (constant_coefficient _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_singleton_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (length (var 0) ≐ one ⟶ recode (entry (var 0) zero) ≐ evaluate (var 0) (var 1)) :=
  closeUniv 2 (.impI (singleton_evaluation _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRationalSyntheticCoefficientValues

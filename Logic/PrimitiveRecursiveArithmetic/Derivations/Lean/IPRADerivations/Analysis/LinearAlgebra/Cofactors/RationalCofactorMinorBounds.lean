import IPRADerivations.Analysis.RationalArithmetic.Spans.Minors.RationalMinorAugmentation
import IPRADerivations.Analysis.RationalArithmetic.Spans.Minors.RationalMinorMaskDeletion
import IPRADerivations.Analysis.LinearAlgebra.Cofactors.RationalIntegerMinorDeterminants
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.DiophantineNumberTheory.IntegerRootBound

/-!
# The actual square minors for the cofactor vector

Each column in the augmented support determines a square minor on the
original independent rows, with that column omitted. In the free-column
case the minor is exactly the chosen maximum minor. We obtain the same
integer determinant bound for every retained column, and lift it to the
original dimension's uniform bound.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorMinorBounds

open_ipra
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.Foundations.RuntimePermutationFactorialBound (factorial factorial_succ subst_factorial)
open RationalSelectedMinors (count normalized)
open RationalSubtupleSpan (bit)
open RationalMinorFreeColumn (free)
open RationalMinorAugmentation (extendedColumn extended_column_size)
open RationalMinorMaskDeletion (erase erase_count)
open RationalMaximalMinors (rank bestRow bestColumn best_valid best_cleared_nonzero)
open RationalArithmetic (select select_one select_zero)
open RationalScalarDeterminantGaussianEmbedding (determinant)
open RationalIntegerMinorDeterminants (content cleared_minor_determinant_content)
open RationalMatrixClearingBounds (inputMatrix entryCap)
open RationalGaussianEmbedding (embed scalarZero embed_zero)
open RationalPolynomialGaussianEmbedding (embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def columnMask (P d j : PTm n) : PTm n :=
  select (eqb j (free P d)) (erase d (extendedColumn P d) j) (bestColumn P d)

def minorValue (P d j : PTm n) : PTm n := determinant (normalized P d (bestRow P d) (columnMask P d j)) (rank P d)

def bound (P d H : PTm n) : PTm n := factorial d * pw (entryCap P d H) d

ipra_subst columnMask

theorem free_mask (P d j : PTm n) (h : Γ ⊢[PRAAx] j ≐ free P d) : Γ ⊢[PRAAx] columnMask P d j ≐ bestColumn P d :=
  select_one _ _ _ (eqb_of_eq h)

theorem other_mask (P d j : PTm n) (h : Γ ⊢[PRAAx] neg (j ≐ free P d)) :
    Γ ⊢[PRAAx] columnMask P d j ≐ erase d (extendedColumn P d) j :=
  select_zero _ _ _ (eqb_of_ne h)

theorem column_count_congr (d : PTm n) {a b : PTm n} (e : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] count d a ≐ count d b :=
  congrAp2 (sumF (Foundations.BoundedReflection.sgB RationalSubtupleSpan.bitBody)) (.eqRefl d) e

theorem cofactor_size (P d j : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) : Γ ⊢[PRAAx] count d (columnMask P d j) ≐ rank P d := by
  refine .orE (eq_or_ne j (free P d)) ?_ ?_
  · exact (column_count_congr d (free_mask P d j Prf.hyp0)).eqTrans (best_valid P d).andE₁.eqSymm
  · have e : neg (j ≐ free P d) :: Γ ⊢[PRAAx] succ (count d (erase d (extendedColumn P d) j)) ≐ succ (rank P d) :=
      (erase_count d (extendedColumn P d) j hj.wk hs.wk).eqTrans (extended_column_size P d h.wk)
    exact (column_count_congr d (other_mask P d j Prf.hyp0)).eqTrans (succ_inj e)

theorem free_minor_value (P d : PTm n) : Γ ⊢[PRAAx] minorValue P d (free P d) ≐
    determinant (normalized P d (bestRow P d) (bestColumn P d)) (rank P d) := by
  ipra_congr (determinant (normalized (var 0) (var 1) (var 2) (var 3)) (var 4) : PTm 5) with
    [.eqRefl P, .eqRefl d, .eqRefl (bestRow P d), free_mask _ _ _ (.eqRefl _), .eqRefl (rank P d)] using [minorValue]

theorem free_minor_nonzero (P d : PTm n) : Γ ⊢[PRAAx] neg (minorValue P d (free P d) ≐ scalarZero) := by
  refine .impI (.impE (best_cleared_nonzero P d).wk ?_)
  exact (embed_congr (free_minor_value P d).eqSymm).eqTrans ((embed_congr Prf.hyp0).eqTrans embed_zero)

theorem factorial_step_mono (i : PTm n) : Γ ⊢[PRAAx] le (factorial i) (factorial (succ i)) := by
  have positive : Γ ⊢[PRAAx] le one (succ i) := (succ_monus_succ zero i).eqTrans (zero_le i)
  exact le_congr (by ipra_ring) (factorial_succ i).eqSymm (le_mul_mono (le_refl (factorial i)) positive)

theorem factorial_mono (a b : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (factorial a) (factorial b) := by
  have powers : Γ ⊢[PRAAx] .all (le (factorial (Syn.shift a)) (factorial (Syn.shift a+var 0))) := by
    ipra_qfind (le_QF _ _) [subst_le, subst_factorial]
    · exact le_congr (.eqRefl _) (congrAp2 factF (add_zero a).eqSymm (.eqRefl zero)) (le_refl _)
    · have e : Γ.map Fm.shift ⊢[PRAAx] succ (Syn.shift a+var 0) ≐ Syn.shift a+succ (var 0) := by ipra_ring
      exact le_trans Prf.hyp0 (le_congr (.eqRefl _) (congrAp2 factF e.wk (.eqRefl zero)) (factorial_step_mono _))
  have shifted : Γ ⊢[PRAAx] le (factorial a) (factorial (a+monus b a)) := by
    simpa only [subst_le,subst_factorial,PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using powers.allE (monus b a)
  exact le_congr (.eqRefl _) (congrAp2 factF (eq_add_of_le h).eqSymm (.eqRefl zero)) shifted

theorem cofactor_minor_bound (P d j H : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hj : Γ ⊢[PRAAx] lt j d)
    (hs : Γ ⊢[PRAAx] bit (extendedColumn P d) j ≐ one) (hH : Γ ⊢[PRAAx] le one H)
    (hP : Γ ⊢[PRAAx] inputMatrix P d H) : Γ ⊢[PRAAx] content (minorValue P d j) (bound P d H) := by
  have sized := cofactor_size P d j h hj hs
  have exactBound := cleared_minor_determinant_content P d (bestRow P d) (columnMask P d j) (rank P d) H hP (.eqRefl _) sized.eqSymm
  have cap : Γ ⊢[PRAAx] entryCap P d H ≐ succ (pred (entryCap P d H)) :=
    pos_of_eq_succ (DiophantineNumberTheory.IntegerRootBound.pw_pos_of hH (succ (length P*d)))
  have r := le_of_lt h
  exact .andI exactBound.andE₁ (le_trans exactBound.andE₂ (le_mul_mono (factorial_mono _ _ r) (pw_le_exp cap r)))

theorem actual_cofactor_minor_size_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (var 1) ⟶ bit (extendedColumn (var 0) (var 1)) (var 2) ≐ one ⟶
      count (var 1) (columnMask (var 0) (var 1) (var 2)) ≐ rank (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (.impI (cofactor_size _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

theorem actual_free_cofactor_minor_nonzero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (neg (minorValue (var 0) (var 1) (free (var 0) (var 1)) ≐ scalarZero)) :=
  closeUniv 2 (free_minor_nonzero _ _)

theorem actual_cofactor_minor_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (var 1) ⟶
      bit (extendedColumn (var 0) (var 1)) (var 2) ≐ one ⟶ le one (var 3) ⟶ inputMatrix (var 0) (var 1) (var 3) ⟶
      content (minorValue (var 0) (var 1) (var 2)) (bound (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (cofactor_minor_bound _ _ _ _
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.RationalCofactorMinorBounds

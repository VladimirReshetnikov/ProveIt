import IPRADerivations.Analysis.Polynomials.Elimination.Vandermonde.GaussianRationalFiberVandermonde
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalReconstruction
import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerAlgebra

/-!
# Actual uniform row quotients and repeated-root polynomials

The first t rows are divided by X-x using the actual synthetic quotient.
One leading zero retains the original width, including width zero. Later
rows retain their original raw coefficient lists. Original cell roots
derive the pointwise row factor equation; no quotient or evaluator law is
an input. A numerical list of t copies of x separately constructs the
actual monic polynomial (X-x)^t by genuine guarded QF induction.

All table dimensions, widths, counts, original codes and query points are
numerical. Determinant factorization and fiber multiplicity are separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qmul_congr qadd_congr qsub_congr quotient quotient_length canonicalCoefficients)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (table firstRowsZero)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell tableShape cell_length)
open LeanProofs.IPRA.Analysis.GaussianRationalReconstruction (reconstruct factors)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power power_zero power_succ)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence subst_entry sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quotientCell (A B t x r j : PTm n) : PTm n := sel (Signum.sg (monus t r))
  (leftPad (quotient (cell A r j) x B) one) (cell A r j)
def data (A B t x : PTm n) : PTm n := pairT A (pairT B (pairT t x))
def fields (p : PTm n) : Fin 4 → PTm n :=
  ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),sndT (sndT (sndT p))]
def quotientBody : PTm 3 := quotientCell (fields (var 2) 0) (fields (var 2) 1)
  (fields (var 2) 2) (fields (var 2) 3) (var 0) (var 1)
def Qhat (A m B t x : PTm n) : PTm n := table quotientBody m m (data A B t x)
def repeated (x t : PTm n) : PTm n := sequence (var 1 : PTm 2) t x
def H (x t : PTm n) : PTm n := reconstruct (repeated x t) t t

ipra_subst quotientCell [sel]
ipra_subst data
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 4) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
ipra_subst Qhat
ipra_subst repeated
ipra_subst H

theorem quotient_cell_congr {A A' B B' t t' x x' r r' j j' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (ht : Γ ⊢[PRAAx] t ≐ t')
    (hx : Γ ⊢[PRAAx] x ≐ x') (hr : Γ ⊢[PRAAx] r ≐ r') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    quotientCell A B t x r j ≐ quotientCell A' B' t' x' r' j' := by
  ipra_congr (quotientCell (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6) with [hA, hB, ht, hx, hr, hj]
theorem fields_at (A B t x : PTm n) (i : Fin 4) : Γ ⊢[PRAAx] fields (data A B t x) i ≐ ![A,B,t,x] i :=
  pairVectorField_eq 3 ![A,B,t,x] (.eqRefl _) i
theorem quotient_lookup (A m B t x r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (Qhat A m B t x) r j ≐ quotientCell A B t x r j := by
  have e : Γ ⊢[PRAAx] cell (Qhat A m B t x) r j ≐ quotientCell
      (fields (data A B t x) 0) (fields (data A B t x) 1) (fields (data A B t x) 2) (fields (data A B t x) 3) r j := by
    simpa [Qhat,quotientBody] using GaussianRationalFiberVandermonde.table_lookup quotientBody m m (data A B t x) r j hr hj
  exact e.eqTrans (quotient_cell_congr (fields_at _ _ _ _ 0) (fields_at _ _ _ _ 1)
    (fields_at _ _ _ _ 2) (fields_at _ _ _ _ 3) (.eqRefl _) (.eqRefl _))
theorem upper_cell (A B t x r j : PTm n) (hr : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx]
    quotientCell A B t x r j ≐ leftPad (quotient (cell A r j) x B) one :=
  sel_one (AnalyticNumberTheory.Totatives.sg_lt hr)
theorem lower_cell (A B t x r j : PTm n) (hr : Γ ⊢[PRAAx] le t r) : Γ ⊢[PRAAx]
    quotientCell A B t x r j ≐ cell A r j := sel_zero (Foundations.BoundedFormulas.sg_of_zero hr)
theorem Qhat_length (A m B t x : PTm n) : Γ ⊢[PRAAx] length (Qhat A m B t x) ≐ m :=
  GaussianRationalFiberVandermonde.table_length _ _ _ _
theorem Qhat_row_length (A m B t x r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (Qhat A m B t x) r) ≐ m := GaussianRationalFiberVandermonde.table_row_length _ _ _ _ _ hr
theorem Qhat_cell_length (A m B t x r j : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (cell (Qhat A m B t x) r j) ≐ succ B := by
  refine (congrFst (quotient_lookup _ _ _ _ _ _ _ hr hj)).eqTrans ?_
  refine .orE (lt_or_le r t) ?_ ?_
  · exact (congrFst (upper_cell _ _ _ _ _ _ Prf.hyp0)).eqTrans
      ((pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (quotient_length _ _ _)).eqTrans (by ipra_ring)))
  · exact (congrFst (lower_cell _ _ _ _ _ _ Prf.hyp0)).eqTrans (cell_length _ _ _ _ _ hA.wk hr.wk hj.wk)
theorem Qhat_shape (A m B t x : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B) : Γ ⊢[PRAAx]
    tableShape (Qhat A m B t x) m B := by
  refine .andI (Qhat_length _ _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI (.allI (.impI ?_)))))
  · simpa only [Syn.shift,subst_Qhat] using Qhat_row_length (Syn.shift A) (Syn.shift m) (Syn.shift B) (Syn.shift t) (Syn.shift x) (var 0) Prf.hyp0
  · let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    have hs : Δ ⊢[PRAAx] tableShape (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift B)) := by
      simpa only [Δ,List.map_cons,Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hA.shift.shift.wk.wk
    have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
    have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
    simpa only [Δ,Syn.shift,subst_Qhat,Syn.subst_var,Fin.succ_zero_eq_one] using Qhat_cell_length (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x)) (var 1) (var 0) hs rr Prf.hyp0

theorem root_at (A m t x r j : PTm n) (h : Γ ⊢[PRAAx] firstRowsZero A m t x)
    (hr : Γ ⊢[PRAAx] lt r t) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] evaluate (cell A r j) x ≐ qzero := by
  have rowRule : Γ ⊢[PRAAx] lt r t ⟶ .all (lt (var 0) (Syn.shift m) ⟶
      evaluate (cell (Syn.shift A) (Syn.shift r) (var 0)) (Syn.shift x) ≐ qzero) := by
    simpa [firstRowsZero,Foundations.BoundedFormulas.subst_up_shift'] using h.allE r
  have rule : Γ ⊢[PRAAx] lt j m ⟶ evaluate (cell A r j) x ≐ qzero := by simpa using (Prf.impE rowRule hr).allE j
  exact .impE rule hj
theorem upper_evaluation (A m B t x z r j : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B)
    (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x) (hr : Γ ⊢[PRAAx] lt r m)
    (hj : Γ ⊢[PRAAx] lt j m) (ht : Γ ⊢[PRAAx] lt r t) : Γ ⊢[PRAAx]
    evaluate (cell A r j) z ≐ qmul (qsub z x) (evaluate (cell (Qhat A m B t x) r j) z) := by
  have cellEq := (quotient_lookup A m B t x r j hr hj).eqTrans (upper_cell A B t x r j ht)
  have padded := (evaluate_congr cellEq (.eqRefl z)).eqTrans (pad_evaluation _ _ _)
  exact (GaussianRationalSyntheticDivision.division_evaluation _ _ _ _ (cell_length _ _ _ _ _ hA hr hj)).eqTrans
    ((qadd_congr (.eqRefl _) (root_at _ _ _ _ _ _ hRoot ht hj)).eqTrans
      ((GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
        (qmul_congr (.eqRefl _) padded.eqSymm)))
theorem lower_evaluation (A m B t x z r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hj : Γ ⊢[PRAAx] lt j m) (ht : Γ ⊢[PRAAx] le t r) : Γ ⊢[PRAAx]
    evaluate (cell (Qhat A m B t x) r j) z ≐ evaluate (cell A r j) z :=
  evaluate_congr ((quotient_lookup _ _ _ _ _ _ _ hr hj).eqTrans (lower_cell _ _ _ _ _ _ ht)) (.eqRefl _)

theorem repeated_length (x t : PTm n) : Γ ⊢[PRAAx] length (repeated x t) ≐ t := sequence_length _ _ _
theorem repeated_lookup (x t i : PTm n) (hi : Γ ⊢[PRAAx] lt i t) : Γ ⊢[PRAAx] entry (repeated x t) i ≐ x := by
  simpa [repeated,inst2] using sequence_decode (var 1 : PTm 2) (x := x) hi
theorem H_length (x t : PTm n) : Γ ⊢[PRAAx] length (H x t) ≐ succ t := GaussianRationalReconstruction.reconstruct_length _ _ _
theorem H_canonical (x t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (H x t) := GaussianRationalReconstruction.reconstruct_canonical _ _ _
theorem H_monic (x t : PTm n) : Γ ⊢[PRAAx] entry (H x t) zero ≐ qone := GaussianRationalReconstruction.reconstruct_monic _ _ _
alias reverse_bound := Common.monus_succ_lt

theorem repeated_factors (x t z k : PTm n) (hk : Γ ⊢[PRAAx] le k t) : Γ ⊢[PRAAx]
    factors (repeated x t) t z k ≐ power (qsub z x) k := by
  have all : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift t) ⟶
      factors (repeated (Syn.shift x) (Syn.shift t)) (Syn.shift t) (Syn.shift z) (var 0) ≐
        power (qsub (Syn.shift z) (Syn.shift x)) (var 0)) := by
    ipra_qfind (⟨le_QF _ _,trivial⟩) [subst_le, GaussianRationalReconstruction.subst_factors, subst_repeated,
        GaussianRationalReciprocal.subst_power, GaussianRationalMetric.subst_qsub]
    · exact .impI ((GaussianRationalReconstruction.factors_zero _ _ _).eqTrans (power_zero _).eqSymm)
    · refine .impI ?_
      exact (GaussianRationalReconstruction.factors_succ _ _ _ _).eqTrans
        ((qmul_congr (qsub_congr (.eqRefl _) (repeated_lookup _ _ _ (reverse_bound _ _ Prf.hyp0)))
          (.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0))).eqTrans
          ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (power_succ _ _).eqSymm))
  have rule : Γ ⊢[PRAAx] le k t ⟶ factors (repeated x t) t z k ≐ power (qsub z x) k := by
    simpa only [Fm.subst_imp,Fm.subst_eq,subst_le,GaussianRationalReconstruction.subst_factors,
      subst_repeated,GaussianRationalReciprocal.subst_power,GaussianRationalMetric.subst_qsub,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE k
  exact .impE rule hk
theorem H_evaluation (x t z : PTm n) : Γ ⊢[PRAAx] evaluate (H x t) z ≐ power (qsub z x) t :=
  (GaussianRationalReconstruction.reconstruction_evaluation _ _ _ _).eqTrans (repeated_factors _ _ _ _ (le_refl _))

/-! The actual PR5 constructor returns the quotient table and the very
same repeated-root polynomial/list used by the proofs. -/
def output (A m B t x : PTm n) : PTm n := pairT (Qhat A m B t x) (pairT (H x t) (repeated x t))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A m B t x : PTm n) : PTm n := app outputF ![A,m,B,t,x]
ipra_subst output
ipra_subst run
theorem program_at (A m B t x : PTm n) : Γ ⊢[PRAAx] run A m B t x ≐ output A m B t x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,m,B,t,x]
theorem returned_Qhat (A m B t x : PTm n) : Γ ⊢[PRAAx] fstT (run A m B t x) ≐ Qhat A m B t x :=
  (program_at _ _ _ _ _).fstE
theorem returned_H (A m B t x : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A m B t x)) ≐ H x t :=
  (program_at _ _ _ _ _).sndE.fstE
theorem returned_repeated (A m B t x : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A m B t x)) ≐ repeated x t :=
  (program_at _ _ _ _ _).sndE.sndE
theorem returned_H_evaluation (A m B t x z : PTm n) : Γ ⊢[PRAAx]
    evaluate (fstT (sndT (run A m B t x))) z ≐ power (qsub z x) t :=
  (evaluate_congr (returned_H _ _ _ _ _) (.eqRefl _)).eqTrans (H_evaluation _ _ _)
theorem returned_Qhat_shape (A m B t x : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B) : Γ ⊢[PRAAx]
    tableShape (fstT (run A m B t x)) m B :=
  GaussianRationalFiberVandermonde.table_shape_congr (returned_Qhat _ _ _ _ _).eqSymm (Qhat_shape _ _ _ _ _ hA)

/-! Original source shapes and roots, every table/polynomial/query index,
and all program inputs are bound by ordinary PRA proofs. -/
theorem actual_quotient_table_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ tableShape (Qhat (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 2)) :=
  closeUniv 5 (.impI (Qhat_shape _ _ _ _ _ Prf.hyp0))
theorem actual_upper_row_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (tableShape (var 0) (var 1) (var 2) ⟶ firstRowsZero (var 0) (var 1) (var 3) (var 4) ⟶
      lt (var 6) (var 1) ⟶ lt (var 7) (var 1) ⟶ lt (var 6) (var 3) ⟶
        evaluate (cell (var 0) (var 6) (var 7)) (var 5) ≐ qmul (qsub (var 5) (var 4))
          (evaluate (cell (Qhat (var 0) (var 1) (var 2) (var 3) (var 4)) (var 6) (var 7)) (var 5))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (.impI
    (upper_evaluation _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))
theorem actual_unchanged_lower_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (lt (var 6) (var 1) ⟶ lt (var 7) (var 1) ⟶ le (var 3) (var 6) ⟶
      evaluate (cell (Qhat (var 0) (var 1) (var 2) (var 3) (var 4)) (var 6) (var 7)) (var 5) ≐
        evaluate (cell (var 0) (var 6) (var 7)) (var 5)) :=
  closeUniv 8 (.impI (.impI (.impI (lower_evaluation _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_repeated_root_list_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((length (repeated (var 0) (var 1)) ≐ var 1) ⋏
      (lt (var 2) (var 1) ⟶ entry (repeated (var 0) (var 1)) (var 2) ≐ var 0)) :=
  closeUniv 3 (.andI (repeated_length _ _) (.impI (repeated_lookup _ _ _ Prf.hyp0)))
theorem actual_repeated_root_polynomial_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((length (H (var 0) (var 1)) ≐ succ (var 1)) ⋏
      (canonicalCoefficients (H (var 0) (var 1)) ⋏ entry (H (var 0) (var 1)) zero ≐ qone)) :=
  closeUniv 2 (.andI (H_length _ _) (.andI (H_canonical _ _) (H_monic _ _)))
theorem actual_repeated_factor_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le (var 3) (var 1) ⟶ factors (repeated (var 0) (var 1)) (var 1) (var 2) (var 3) ≐
      power (qsub (var 2) (var 0)) (var 3)) := closeUniv 4 (.impI (repeated_factors _ _ _ _ Prf.hyp0))
theorem actual_repeated_root_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (evaluate (H (var 0) (var 1)) (var 2) ≐ power (qsub (var 2) (var 0)) (var 1)) :=
  closeUniv 3 (H_evaluation _ _ _)
theorem actual_constructor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ Qhat (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        ((fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ H (var 4) (var 3)) ⋏
          (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))) ≐ repeated (var 4) (var 3))))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (returned_Qhat _ _ _ _ _)
    (.andI (returned_H _ _ _ _ _) (returned_repeated _ _ _ _ _))))
theorem actual_returned_repeated_root_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (evaluate (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) (var 5) ≐
      power (qsub (var 5) (var 4)) (var 3)) := closeUniv 6 (returned_H_evaluation _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient

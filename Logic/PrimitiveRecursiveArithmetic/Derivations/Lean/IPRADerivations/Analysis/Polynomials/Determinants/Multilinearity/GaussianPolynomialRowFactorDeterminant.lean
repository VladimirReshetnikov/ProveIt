import IPRADerivations.Analysis.Polynomials.Division.GaussianPolynomialRowQuotient
import IPRADerivations.Analysis.LinearAlgebra.Determinants.SpecialMatrices.GaussianScalarDiagonalDeterminant
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminantMultiplication
import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianRationalGridCoefficientEquality

/-!
# Actual determinant row factors with bounded coefficient witnesses

Original roots of the first t polynomial rows derive a real diagonal
matrix action at every queried point. The proved scalar determinant
product and diagonal determinant laws then factor the SAME numerical
polynomial determinant. The actual monic repeated-root polynomial and
the actual polynomial product have equal evaluations on the constructed
finite grid; its computed root bound gives literal bounded coefficient
equality after the original determinant is padded to the common width.

All dimensions, widths, lists, counts and query indices are numerical.
The guards concern original cell shapes/roots and t<=m. No determinant,
evaluator, grid-root, coefficient or exact-degree law is an input.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialRowFactorDeterminant

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qone qmul_congr canonicalCoefficients canonical_coefficient_at)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub)
open LeanProofs.IPRA.Analysis.GaussianRationalPolynomialBuffers (leftPad pad_length pad_evaluation)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (evaluate_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (firstRowsZero)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell tableShape)
open LeanProofs.IPRA.Analysis.GaussianPolynomialRowQuotient (Qhat H)
open LeanProofs.IPRA.Analysis.GaussianScalarDeterminant (evaluatedTable scalarDet)
open LeanProofs.IPRA.Analysis.GaussianScalarDiagonalDeterminant (weight diagonal)
open LeanProofs.IPRA.Analysis.GaussianRationalMatrixFiniteSums (matrixProduct)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal (power)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def original (A m B : PTm n) : PTm n := GaussianPolynomialDeterminant.determinant A m B
def quotientDeterminant (A m B t x : PTm n) : PTm n := GaussianPolynomialDeterminant.determinant (Qhat A m B t x) m B
def width (m B t : PTm n) : PTm n := t+m*B
def paddedOriginal (A m B t : PTm n) : PTm n := leftPad (original A m B) t
def factorProduct (A m B t x : PTm n) : PTm n :=
  GaussianRationalPolynomialProduct.product (H x t) (quotientDeterminant A m B t x) t (m*B)

ipra_subst original
ipra_subst quotientDeterminant
ipra_subst width
ipra_subst paddedOriginal
ipra_subst factorProduct

theorem weighted_cell_evaluation (A m B t x z r j : PTm n)
    (hA : Γ ⊢[PRAAx] tableShape A m B) (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell A r j) z ≐ qmul (weight (qsub z x) t r) (evaluate (cell (Qhat A m B t x) r j) z) := by
  refine .orE (lt_or_le r t) ?_ ?_
  · exact (GaussianPolynomialRowQuotient.upper_evaluation _ _ _ _ _ _ _ _ hA.wk hRoot.wk hr.wk hj.wk Prf.hyp0).eqTrans
      (qmul_congr (GaussianScalarDiagonalDeterminant.weight_upper _ _ _ Prf.hyp0).eqSymm (.eqRefl _))
  · exact (GaussianPolynomialRowQuotient.lower_evaluation _ _ _ _ _ _ _ _ hr.wk hj.wk Prf.hyp0).eqSymm.eqTrans
      (((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (GaussianRationalHorner.horner_canonical _ _ _))).eqSymm.eqTrans
          (qmul_congr (GaussianScalarDiagonalDeterminant.weight_lower _ _ _ Prf.hyp0).eqSymm (.eqRefl _)))

theorem evaluated_product_cell (A m B t x z r j : PTm n)
    (hA : Γ ⊢[PRAAx] tableShape A m B) (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (evaluatedTable A m z) r j ≐
      cell (matrixProduct (diagonal (qsub z x) t m) (evaluatedTable (Qhat A m B t x) m z) m) r j :=
  (GaussianScalarDeterminant.evaluated_lookup _ _ _ _ _ hr hj).eqTrans
    ((weighted_cell_evaluation _ _ _ _ _ _ _ _ hA hRoot hr hj).eqTrans
      ((qmul_congr (.eqRefl _) (GaussianScalarDeterminant.evaluated_lookup _ _ _ _ _ hr hj).eqSymm).eqTrans
        (GaussianScalarDiagonalDeterminant.diagonal_left_action _ _ _ _ _ _ hr hj).eqSymm))

theorem evaluated_product_values (A m B t x z : PTm n)
    (hA : Γ ⊢[PRAAx] tableShape A m B) (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarCellsEqual (evaluatedTable A m z)
      (matrixProduct (diagonal (qsub z x) t m) (evaluatedTable (Qhat A m B t x) m z) m) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have hs : Δ ⊢[PRAAx] tableShape (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift B)) := by
    simpa only [Δ,List.map_cons,Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hA.shift.shift.wk.wk
  have roots : Δ ⊢[PRAAx] firstRowsZero (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m))
      (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x)) := by
    simpa only [Δ,List.map_cons,Fm.shift,GaussianRationalFiberVandermonde.subst_firstRowsZero,Syn.shift] using hRoot.shift.shift.wk.wk
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have e := evaluated_product_cell (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m))
    (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z)) (var 1) (var 0) hs roots rr Prf.hyp0
  simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,GaussianScalarDeterminant.subst_evaluatedTable,
    GaussianRationalMatrixFiniteSums.subst_matrixProduct,GaussianScalarDiagonalDeterminant.subst_diagonal,
    GaussianRationalMetric.subst_qsub,GaussianPolynomialRowQuotient.subst_Qhat] using
      GaussianRationalValueEquality.value_equal_of_code e

theorem determinant_evaluation (A m B t x z : PTm n)
    (hA : Γ ⊢[PRAAx] tableShape A m B) (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x)
    (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    evaluate (original A m B) z ≐ qmul (power (qsub z x) t) (evaluate (quotientDeterminant A m B t x) z) :=
  (GaussianScalarDeterminant.determinant_evaluation_specialization _ _ _ _ hA).eqTrans
    ((GaussianScalarDeterminant.scalar_det_congr _ _ _ (evaluated_product_values _ _ _ _ _ _ hA hRoot)).eqTrans
      ((GaussianScalarDeterminantMultiplication.scalar_det_multiply _ _ _).eqTrans
        (qmul_congr (GaussianScalarDiagonalDeterminant.diagonal_det _ _ _ ht)
          (GaussianScalarDeterminant.determinant_evaluation_specialization _ _ _ _
            (GaussianPolynomialRowQuotient.Qhat_shape _ _ _ _ _ hA)).eqSymm)))

theorem original_length (A m B : PTm n) : Γ ⊢[PRAAx] length (original A m B) ≐ succ (m*B) :=
  GaussianPolynomialDeterminant.determinant_length _ _ _
theorem quotient_length (A m B t x : PTm n) : Γ ⊢[PRAAx] length (quotientDeterminant A m B t x) ≐ succ (m*B) :=
  GaussianPolynomialDeterminant.determinant_length _ _ _
theorem padded_length (A m B t : PTm n) : Γ ⊢[PRAAx] length (paddedOriginal A m B t) ≐ succ (width m B t) := by
  change Γ ⊢[PRAAx] length (leftPad (original A m B) t) ≐ succ (t+m*B)
  exact (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (original_length _ _ _)).eqTrans (by ipra_ring))
theorem product_length (A m B t x : PTm n) : Γ ⊢[PRAAx] length (factorProduct A m B t x) ≐ succ (width m B t) :=
  GaussianRationalPolynomialProduct.product_length _ _ _ _
theorem product_canonical (A m B t x : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (factorProduct A m B t x) :=
  GaussianRationalPolynomialProduct.product_canonical _ _ _ _

theorem padded_canonical (A m B t : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (paddedOriginal A m B t) :=
  GaussianPolynomialMonicCompanion.pad_canonical _ _ (GaussianPolynomialDeterminant.determinant_canonical _ _ _)

theorem buffer_evaluation (A m B t x z : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B)
    (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    evaluate (paddedOriginal A m B t) z ≐ evaluate (factorProduct A m B t x) z :=
  (pad_evaluation _ _ _).eqTrans ((determinant_evaluation _ _ _ _ _ _ hA hRoot ht).eqTrans
    (((GaussianRationalPolynomialProduct.product_evaluation _ _ _ _ _
      (GaussianPolynomialRowQuotient.H_length _ _) (quotient_length _ _ _ _ _)).eqTrans
        (qmul_congr (GaussianPolynomialRowQuotient.H_evaluation _ _ _) (.eqRefl _))).eqSymm))

theorem buffer_grid_equal (A m B t x : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B)
    (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    GaussianRationalGridCoefficientEquality.gridEqual (paddedOriginal A m B t) (factorProduct A m B t x) (width m B t) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift A) (Syn.shift m) (Syn.shift B) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hA.shift
  have roots : Γ.map Fm.shift ⊢[PRAAx] firstRowsZero (Syn.shift A) (Syn.shift m) (Syn.shift t) (Syn.shift x) := by
    simpa only [Fm.shift,GaussianRationalFiberVandermonde.subst_firstRowsZero,Syn.shift] using hRoot.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift t) (Syn.shift m) := by simpa only [Fm.shift,subst_le,Syn.shift] using ht.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_paddedOriginal,subst_factorProduct,subst_width] using
    buffer_evaluation (Syn.shift A) (Syn.shift m) (Syn.shift B) (Syn.shift t) (Syn.shift x)
      (GaussianRationalFiniteGridIdentity.gridPoint (var 0)) hs.wk roots.wk ts.wk
theorem coefficient_factor (A m B t x i : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B)
    (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x) (ht : Γ ⊢[PRAAx] le t m)
    (hi : Γ ⊢[PRAAx] le i (width m B t)) : Γ ⊢[PRAAx]
    entry (paddedOriginal A m B t) i ≐ entry (factorProduct A m B t x) i :=
  GaussianRationalGridCoefficientEquality.coefficient_equal _ _ _ _ (padded_length _ _ _ _) (product_length _ _ _ _ _)
    (padded_canonical _ _ _ _) (product_canonical _ _ _ _ _) (buffer_grid_equal _ _ _ _ _ hA hRoot ht) hi
theorem coefficients_factor (A m B t x : PTm n) (hA : Γ ⊢[PRAAx] tableShape A m B)
    (hRoot : Γ ⊢[PRAAx] firstRowsZero A m t x) (ht : Γ ⊢[PRAAx] le t m) : Γ ⊢[PRAAx]
    GaussianRationalGridCoefficientEquality.coefficientsEqual (paddedOriginal A m B t) (factorProduct A m B t x) (width m B t) :=
  GaussianRationalGridCoefficientEquality.coefficients_equal _ _ _ (padded_length _ _ _ _) (product_length _ _ _ _ _)
    (padded_canonical _ _ _ _) (product_canonical _ _ _ _ _) (buffer_grid_equal _ _ _ _ _ hA hRoot ht)

def input (A m B t x : PTm n) : Fm PTm n := tableShape A m B ⋏ (firstRowsZero A m t x ⋏ le t m)
def certificate (A m B t x : PTm n) : Fm PTm n :=
  (length (paddedOriginal A m B t) ≐ succ (width m B t)) ⋏
    ((length (factorProduct A m B t x) ≐ succ (width m B t)) ⋏
      GaussianRationalGridCoefficientEquality.coefficientsEqual (paddedOriginal A m B t) (factorProduct A m B t x) (width m B t))
ipra_subst input
ipra_subst certificate
theorem factorization (A m B t x : PTm n) (h : Γ ⊢[PRAAx] input A m B t x) : Γ ⊢[PRAAx] certificate A m B t x :=
  .andI (padded_length _ _ _ _) (.andI (product_length _ _ _ _ _)
    (coefficients_factor _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h))))

/-! Actual PR5 metadata retain both determinant programs, the quotient
table/root polynomial, and the exact two common-width factor buffers. -/
def output (A m B t x : PTm n) : PTm n := pairT (Qhat A m B t x) (pairT (H x t)
  (pairT (original A m B) (pairT (quotientDeterminant A m B t x)
    (pairT (paddedOriginal A m B t) (factorProduct A m B t x)))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A m B t x : PTm n) : PTm n := app outputF ![A,m,B,t,x]
def tableField (p : PTm n) : PTm n := fstT p
def rootPolynomialField (p : PTm n) : PTm n := fstT (sndT p)
def originalField (p : PTm n) : PTm n := fstT (sndT (sndT p))
def quotientField (p : PTm n) : PTm n := fstT (sndT (sndT (sndT p)))
def paddedField (p : PTm n) : PTm n := fstT (sndT (sndT (sndT (sndT p))))
def productField (p : PTm n) : PTm n := sndT (sndT (sndT (sndT (sndT p))))
ipra_subst output
ipra_subst run
ipra_subst tableField
ipra_subst rootPolynomialField
ipra_subst originalField
ipra_subst quotientField
ipra_subst paddedField
ipra_subst productField
theorem program_at (A m B t x : PTm n) : Γ ⊢[PRAAx] run A m B t x ≐ output A m B t x := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,m,B,t,x]
theorem returned_table (A m B t x : PTm n) : Γ ⊢[PRAAx] tableField (run A m B t x) ≐ Qhat A m B t x :=
  (program_at _ _ _ _ _).fstE
theorem returned_root_polynomial (A m B t x : PTm n) : Γ ⊢[PRAAx] rootPolynomialField (run A m B t x) ≐ H x t :=
  (program_at _ _ _ _ _).sndE.fstE
theorem returned_original (A m B t x : PTm n) : Γ ⊢[PRAAx] originalField (run A m B t x) ≐ original A m B :=
  (program_at _ _ _ _ _).sndE.sndE.fstE
theorem returned_quotient (A m B t x : PTm n) : Γ ⊢[PRAAx] quotientField (run A m B t x) ≐ quotientDeterminant A m B t x := by
  have tail := (program_at (Γ := Γ) A m B t x).sndE.sndE.sndE
  exact tail.fstE
theorem returned_padded (A m B t x : PTm n) : Γ ⊢[PRAAx] paddedField (run A m B t x) ≐ paddedOriginal A m B t := by
  have tail := (program_at (Γ := Γ) A m B t x).sndE.sndE.sndE.sndE
  exact tail.fstE
theorem returned_product (A m B t x : PTm n) : Γ ⊢[PRAAx] productField (run A m B t x) ≐ factorProduct A m B t x := by
  have tail := (program_at (Γ := Γ) A m B t x).sndE.sndE.sndE.sndE
  exact tail.sndE
theorem returned_padded_length (A m B t x : PTm n) : Γ ⊢[PRAAx] length (paddedField (run A m B t x)) ≐ succ (width m B t) :=
  (congrFst (returned_padded _ _ _ _ _)).eqTrans (padded_length _ _ _ _)
theorem returned_product_length (A m B t x : PTm n) : Γ ⊢[PRAAx] length (productField (run A m B t x)) ≐ succ (width m B t) :=
  (congrFst (returned_product _ _ _ _ _)).eqTrans (product_length _ _ _ _ _)
theorem returned_coefficient_factor (A m B t x i : PTm n) (h : Γ ⊢[PRAAx] input A m B t x)
    (hi : Γ ⊢[PRAAx] le i (width m B t)) : Γ ⊢[PRAAx]
    entry (paddedField (run A m B t x)) i ≐ entry (productField (run A m B t x)) i :=
  (entry_congr (returned_padded _ _ _ _ _) (.eqRefl _)).eqTrans
    ((coefficient_factor _ _ _ _ _ _ (.andE₁ h) (.andE₁ (.andE₂ h)) (.andE₂ (.andE₂ h)) hi).eqTrans
      (entry_congr (returned_product _ _ _ _ _) (.eqRefl _)).eqSymm)

/-! Original roots and shapes are the only factorization guards. All
dimensions/widths/counts/query indices and every original code are bound. -/
theorem actual_evaluated_row_action_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (tableShape (var 0) (var 1) (var 2) ⟶ firstRowsZero (var 0) (var 1) (var 3) (var 4) ⟶
      lt (var 6) (var 1) ⟶ lt (var 7) (var 1) ⟶
        cell (evaluatedTable (var 0) (var 1) (var 5)) (var 6) (var 7) ≐
          cell (matrixProduct (diagonal (qsub (var 5) (var 4)) (var 3) (var 1))
            (evaluatedTable (Qhat (var 0) (var 1) (var 2) (var 3) (var 4)) (var 1) (var 5)) (var 1)) (var 6) (var 7)) :=
  closeUniv 8 (.impI (.impI (.impI (.impI
    (evaluated_product_cell _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))
theorem actual_determinant_row_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ evaluate (original (var 0) (var 1) (var 2)) (var 5) ≐
      qmul (power (qsub (var 5) (var 4)) (var 3))
        (evaluate (quotientDeterminant (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5))) :=
  closeUniv 6 (.impI (determinant_evaluation _ _ _ _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))
theorem actual_common_factor_buffers_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((length (paddedOriginal (var 0) (var 1) (var 2) (var 3)) ≐ succ (width (var 1) (var 2) (var 3))) ⋏
      ((length (factorProduct (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ succ (width (var 1) (var 2) (var 3))) ⋏
        (canonicalCoefficients (paddedOriginal (var 0) (var 1) (var 2) (var 3)) ⋏
          canonicalCoefficients (factorProduct (var 0) (var 1) (var 2) (var 3) (var 4))))) :=
  closeUniv 5 (.andI (padded_length _ _ _ _) (.andI (product_length _ _ _ _ _)
    (.andI (padded_canonical _ _ _ _) (product_canonical _ _ _ _ _))))
theorem actual_grid_factor_witness_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      GaussianRationalGridCoefficientEquality.gridEqual (paddedOriginal (var 0) (var 1) (var 2) (var 3))
        (factorProduct (var 0) (var 1) (var 2) (var 3) (var 4)) (width (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (buffer_grid_equal _ _ _ _ _ (.andE₁ Prf.hyp0)
    (.andE₁ (.andE₂ Prf.hyp0)) (.andE₂ (.andE₂ Prf.hyp0))))
theorem actual_coefficient_row_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 5) (width (var 1) (var 2) (var 3)) ⟶
      entry (paddedOriginal (var 0) (var 1) (var 2) (var 3)) (var 5) ≐
        entry (factorProduct (var 0) (var 1) (var 2) (var 3) (var 4)) (var 5)) :=
  closeUniv 6 (.impI (.impI (coefficient_factor _ _ _ _ _ _ (.andE₁ Prf.hyp1)
    (.andE₁ (.andE₂ Prf.hyp1)) (.andE₂ (.andE₂ Prf.hyp1)) Prf.hyp0)))
theorem actual_factorization_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ certificate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (factorization _ _ _ _ _ Prf.hyp0))
theorem actual_row_factor_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      ((tableField (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ Qhat (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
        ((rootPolynomialField (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ H (var 4) (var 3)) ⋏
          ((originalField (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ original (var 0) (var 1) (var 2)) ⋏
            ((quotientField (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ quotientDeterminant (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
              ((paddedField (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ paddedOriginal (var 0) (var 1) (var 2) (var 3)) ⋏
                (productField (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐ factorProduct (var 0) (var 1) (var 2) (var 3) (var 4)))))))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (returned_table _ _ _ _ _) (.andI (returned_root_polynomial _ _ _ _ _)
    (.andI (returned_original _ _ _ _ _) (.andI (returned_quotient _ _ _ _ _)
      (.andI (returned_padded _ _ _ _ _) (returned_product _ _ _ _ _)))))))
theorem actual_returned_coefficient_row_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le (var 5) (width (var 1) (var 2) (var 3)) ⟶
      entry (paddedField (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5) ≐
        entry (productField (run (var 0) (var 1) (var 2) (var 3) (var 4))) (var 5)) :=
  closeUniv 6 (.impI (.impI (returned_coefficient_factor _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialRowFactorDeterminant

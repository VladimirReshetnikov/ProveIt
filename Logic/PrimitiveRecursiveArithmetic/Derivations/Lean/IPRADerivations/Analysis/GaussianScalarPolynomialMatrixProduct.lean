import IPRADerivations.Analysis.GaussianScalarDeterminant
import IPRADerivations.Analysis.GaussianRationalMatrixFiniteSums

/-!
# Actual scalar-left polynomial matrix products at a numerical query

The original stored scalar-left polynomial product is evaluated cell by
cell and bound to the actual scalar matrix-product table of the original
left table and the actual evaluated right table. Bounded cell equations
then identify the SAME original polynomial determinant observation with
the scalar determinant of that scalar product. Only the original right
polynomial-table shape is required. No outer table-code equality or
determinant multiplication law is supplied or asserted here.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarPolynomialMatrixProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (evaluate canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell tableShape)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The original left table and the independently evaluated original right table. -/
def scalarProduct (S M m z : PTm n) : PTm n :=
  GaussianRationalMatrixFiniteSums.matrixProduct S
    (GaussianScalarDeterminant.evaluatedTable M m z) m

@[simp] theorem subst_scalarProduct {l : ℕ} (σ : Fin n → PTm l) (S M m z : PTm n) :
    Syn.subst σ (scalarProduct S M m z) = scalarProduct (Syn.subst σ S)
      (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ z) := by simp [scalarProduct]

/-- Both original finite folds use the same numerical middle index. -/
theorem value_sum_as_dot (S M m r j z : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianRationalFiberVandermonde.valueSum S M r j m z ≐
      GaussianRationalMatrixFiniteSums.scalarDot S
        (GaussianScalarDeterminant.evaluatedTable M m z) m r j := by
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hj.shift
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have e := (GaussianRationalFiberVandermonde.value_body_at (Γ := Δ)
      (Syn.shift S) (Syn.shift M) (Syn.shift r) (Syn.shift j) (var 0) (Syn.shift z)).eqTrans
    ((qmul_congr (.eqRefl _) (GaussianScalarDeterminant.evaluated_lookup
        (Syn.shift M) (Syn.shift m) (Syn.shift z) (var 0) (Syn.shift j) Prf.hyp0 js.wk).eqSymm).eqTrans
      (GaussianRationalMatrixFiniteSums.scalar_body_at (Syn.shift S)
        (GaussianScalarDeterminant.evaluatedTable (Syn.shift M) (Syn.shift m) (Syn.shift z))
        (Syn.shift r) (Syn.shift j) (var 0)).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalFiberVandermonde.subst_productData,
    GaussianRationalMatrixFiniteSums.subst_scalarData,GaussianScalarDeterminant.subst_evaluatedTable] using e

/-- Actual evaluation of the SAME stored scalar-left polynomial product cell. -/
theorem product_cell_evaluation (S M m L r j z : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m L) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (GaussianRationalFiberVandermonde.product S M m L) r j) z ≐
      GaussianRationalMatrixFiniteSums.scalarDot S
        (GaussianScalarDeterminant.evaluatedTable M m z) m r j :=
  (GaussianRationalFiberVandermonde.product_evaluation _ _ _ _ _ _ _ hM hr hj).eqTrans
    (value_sum_as_dot _ _ _ _ _ _ hj)

theorem evaluated_product_cell (S M m L r j z : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m L) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (GaussianScalarDeterminant.evaluatedTable (GaussianRationalFiberVandermonde.product S M m L) m z) r j ≐
      cell (scalarProduct S M m z) r j :=
  (GaussianScalarDeterminant.evaluated_lookup _ _ _ _ _ hr hj).eqTrans
    ((product_cell_evaluation _ _ _ _ _ _ _ hM hr hj).eqTrans
      (GaussianRationalMatrixFiniteSums.product_lookup _ _ _ _ _ hr hj).eqSymm)

theorem evaluated_product_values (S M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    GaussianScalarDeterminant.scalarCellsEqual
      (GaussianScalarDeterminant.evaluatedTable (GaussianRationalFiberVandermonde.product S M m L) m z)
      (scalarProduct S M m z) m := by
  refine .allI (.impI (.allI (.impI ?_)))
  let Δ := lt (var 0) (Syn.shift (Syn.shift m)) ::
    List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
  have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
  have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
  have ms : Δ ⊢[PRAAx] tableShape (Syn.shift (Syn.shift M))
      (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift L)) := by
    simpa only [Δ,List.map_cons,Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using hM.shift.shift.wk.wk
  have e := GaussianRationalValueEquality.value_equal_of_code
    (evaluated_product_cell (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift M))
      (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift L)) (var 1) (var 0)
      (Syn.shift (Syn.shift z)) ms rr Prf.hyp0)
  simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_scalarProduct,
    GaussianScalarDeterminant.subst_evaluatedTable,GaussianRationalFiberVandermonde.subst_product] using e

/-- This is evaluation specialization, with determinant multiplication still separate. -/
theorem determinant_evaluation_bridge (S M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant (GaussianRationalFiberVandermonde.product S M m L) m L) z ≐
      GaussianScalarDeterminant.scalarDet (scalarProduct S M m z) m :=
  (GaussianScalarDeterminant.determinant_evaluation_specialization _ _ _ _
    (GaussianRationalFiberVandermonde.product_shape _ _ _ _)).eqTrans
      (GaussianScalarDeterminant.scalar_det_congr _ _ _ (evaluated_product_values _ _ _ _ _ hM))

/-- The source Vandermonde factor stays the SAME original numerical W table. -/
theorem WM_determinant_evaluation (R M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant (GaussianRationalFiberVandermonde.WM R M m L) m L) z ≐
      GaussianScalarDeterminant.scalarDet (scalarProduct (GaussianRationalFiberVandermonde.W R m) M m z) m :=
  determinant_evaluation_bridge _ _ _ _ _ hM

/-- Five actual fields: stored polynomial product, evaluated original right
table, scalar product, original determinant polynomial, scalar determinant. -/
def output (S M m L z : PTm n) : PTm n :=
  pairT (GaussianRationalFiberVandermonde.product S M m L)
    (pairT (GaussianScalarDeterminant.evaluatedTable M m z)
      (pairT (scalarProduct S M m z)
        (pairT (GaussianPolynomialDeterminant.determinant
          (GaussianRationalFiberVandermonde.product S M m L) m L)
          (GaussianScalarDeterminant.scalarDet (scalarProduct S M m z) m))))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (S M m L z : PTm n) : PTm n := app outputF ![S,M,m,L,z]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (S M m L z : PTm n) :
    Syn.subst σ (output S M m L z) = output (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ z) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (S M m L z : PTm n) :
    Syn.subst σ (run S M m L z) = run (Syn.subst σ S) (Syn.subst σ M)
      (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ z) := by
  simp [run]
  funext i
  fin_cases i <;> rfl

theorem program_at (S M m L z : PTm n) : Γ ⊢[PRAAx] run S M m L z ≐ output S M m L z := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![S,M,m,L,z]
theorem returned_product (S M m L z : PTm n) : Γ ⊢[PRAAx]
    fstT (run S M m L z) ≐ GaussianRationalFiberVandermonde.product S M m L :=
  (congrFst (program_at _ _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_evaluated_right (S M m L z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run S M m L z)) ≐ GaussianScalarDeterminant.evaluatedTable M m z :=
  (congrFst ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_scalar_product (S M m L z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run S M m L z))) ≐ scalarProduct S M m z :=
  (congrFst ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_polynomial (S M m L z : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (run S M m L z)))) ≐
      GaussianPolynomialDeterminant.determinant (GaussianRationalFiberVandermonde.product S M m L) m L :=
  (congrFst ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_value (S M m L z : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (run S M m L z)))) ≐
      GaussianScalarDeterminant.scalarDet (scalarProduct S M m z) m :=
  (congrSnd ((congrSnd ((congrSnd ((congrSnd (program_at _ _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans
    (snd_pair _ _))).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_value_canonical (S M m L z : PTm n) : Γ ⊢[PRAAx]
    canonical (sndT (sndT (sndT (sndT (run S M m L z))))) :=
  GaussianRationalHorner.canonical_congr (returned_value _ _ _ _ _)
    (GaussianScalarDeterminant.scalar_det_canonical _ _)
theorem returned_evaluation (S M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (fstT (sndT (sndT (sndT (run S M m L z))))) z ≐
      sndT (sndT (sndT (sndT (run S M m L z)))) :=
  (GaussianRationalMonicReduction.evaluate_congr (returned_polynomial _ _ _ _ _) (.eqRefl _)).eqTrans
    ((determinant_evaluation_bridge _ _ _ _ _ hM).eqTrans (returned_value _ _ _ _ _).eqSymm)

theorem actual_value_sum_as_dot_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (var 4) (var 2) ⟶
      GaussianRationalFiberVandermonde.valueSum (var 0) (var 1) (var 3) (var 4) (var 2) (var 5) ≐
        GaussianRationalMatrixFiniteSums.scalarDot (var 0)
          (GaussianScalarDeterminant.evaluatedTable (var 1) (var 2) (var 5)) (var 2) (var 3) (var 4)) :=
  closeUniv 6 (.impI (value_sum_as_dot _ _ _ _ _ _ Prf.hyp0))
theorem actual_polynomial_product_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (tableShape (var 1) (var 2) (var 3) ⟶ lt (var 4) (var 2) ⟶ lt (var 5) (var 2) ⟶
      evaluate (cell (GaussianRationalFiberVandermonde.product (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5)) (var 6) ≐
        cell (scalarProduct (var 0) (var 1) (var 2) (var 6)) (var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI
    ((product_cell_evaluation _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0).eqTrans
      (GaussianRationalMatrixFiniteSums.product_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0).eqSymm))))
theorem actual_evaluated_product_values_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 1) (var 2) (var 3) ⟶ GaussianScalarDeterminant.scalarCellsEqual
      (GaussianScalarDeterminant.evaluatedTable (GaussianRationalFiberVandermonde.product
        (var 0) (var 1) (var 2) (var 3)) (var 2) (var 4))
      (scalarProduct (var 0) (var 1) (var 2) (var 4)) (var 2)) :=
  closeUniv 5 (.impI (evaluated_product_values _ _ _ _ _ Prf.hyp0))
theorem actual_determinant_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 1) (var 2) (var 3) ⟶
      evaluate (GaussianPolynomialDeterminant.determinant (GaussianRationalFiberVandermonde.product
        (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) (var 4) ≐
        GaussianScalarDeterminant.scalarDet (scalarProduct (var 0) (var 1) (var 2) (var 4)) (var 2)) :=
  closeUniv 5 (.impI (determinant_evaluation_bridge _ _ _ _ _ Prf.hyp0))
theorem actual_WM_determinant_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 1) (var 2) (var 3) ⟶
      evaluate (GaussianPolynomialDeterminant.determinant (GaussianRationalFiberVandermonde.WM
        (var 0) (var 1) (var 2) (var 3)) (var 2) (var 3)) (var 4) ≐
        GaussianScalarDeterminant.scalarDet (scalarProduct (GaussianRationalFiberVandermonde.W (var 0) (var 2))
          (var 1) (var 2) (var 4)) (var 2)) :=
  closeUniv 5 (.impI (WM_determinant_evaluation _ _ _ _ _ Prf.hyp0))
theorem actual_product_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)) ≐
        GaussianRationalFiberVandermonde.product (var 0) (var 1) (var 2) (var 3)) ⋏
      (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ≐
        scalarProduct (var 0) (var 1) (var 2) (var 4))) :=
  closeUniv 5 (.andI (program_at _ _ _ _ _) (.andI (returned_product _ _ _ _ _) (returned_scalar_product _ _ _ _ _)))
theorem actual_returned_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 1) (var 2) (var 3) ⟶
      (evaluate (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) (var 4) ≐
        sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) ⋏
      canonical (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4))))))) :=
  closeUniv 5 (.impI (.andI (returned_evaluation _ _ _ _ _ Prf.hyp0) (returned_value_canonical _ _ _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianScalarPolynomialMatrixProduct

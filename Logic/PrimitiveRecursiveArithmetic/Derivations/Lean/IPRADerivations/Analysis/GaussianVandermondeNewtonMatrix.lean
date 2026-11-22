import IPRADerivations.Analysis.GaussianVandermondeNewtonPolynomials
import IPRADerivations.Analysis.GaussianScalarTriangularDeterminant
import IPRADerivations.Analysis.GaussianScalarDeterminantMultiplication

/-!
# The actual Newton matrix and square Vandermonde product

The original power table is multiplied by the actual descending Newton
coefficient table, read in ascending powers. Its derived entries are the
original Newton polynomial evaluations. Thus the change table is upper
unitriangular and the product is lower triangular. The SAME numerical
scalar determinant and its actual matrix-product law give the literal
nested pair-difference product. Empty lists and arbitrary raw roots are
included; no evaluator, determinant or coefficient law is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianVandermondeNewtonMatrix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalHorner (qzero qmul canonical canonical_congr evaluate)
open GaussianRationalSyntheticDivision (qone qone_canonical qzero_canonical qmul_congr)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianRationalFiberVandermonde (table table_length table_row_length table_lookup U U_lookup)
open GaussianRationalMatrixFiniteSums (matrixProduct scalarDot scalarBody scalarData product_lookup scalar_body_at)
open GaussianScalarDeterminant (scalarDet scalar_det_canonical)
open GaussianScalarTriangularDeterminant (belowZeros aboveZeros diagonalOnes diagonalProduct)
open GaussianVandermondeNewtonPolynomials (polynomial coefficient differenceProduct pairProduct)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)
open ConciseIPRA.PTm (zero succ app)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficientBody : PTm 3 := coefficient (var 2) (var 1) (var 0)
def change (R m : PTm n) : PTm n := table coefficientBody m m R
def transformed (R m : PTm n) : PTm n := matrixProduct (U R m) (change R m) m
@[simp] theorem subst_change {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (change R m) = change (Syn.subst σ R) (Syn.subst σ m) := by simp [change]
@[simp] theorem subst_transformed {l : ℕ} (σ : Fin n → PTm l) (R m : PTm n) :
    Syn.subst σ (transformed R m) = transformed (Syn.subst σ R) (Syn.subst σ m) := by simp [transformed]

theorem change_length (R m : PTm n) : Γ ⊢[PRAAx] length (change R m) ≐ m := table_length _ _ _ _
theorem change_row_length (R m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    length (entry (change R m) r) ≐ m := table_row_length _ _ _ _ _ hr
theorem change_lookup (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (change R m) r j ≐ coefficient R j r := by
  simpa only [coefficientBody,GaussianVandermondeNewtonPolynomials.subst_coefficient,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,change] using
    table_lookup coefficientBody m m R r j hr hj
theorem change_canonical (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (change R m) r j) := canonical_congr (change_lookup _ _ _ _ hr hj)
      (GaussianVandermondeNewtonPolynomials.coefficient_canonical _ _ _)

theorem change_upper (R m : PTm n) : Γ ⊢[PRAAx] belowZeros (change R m) m := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let Δ := lt (var 0) (var 1) :: lt (var 0) (Syn.shift (Syn.shift m)) ::
    (lt (var 0) (Syn.shift m)).shift :: (Γ.map Fm.shift).map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
    simpa [Δ,Fm.shift,Syn.shift] using
      (Prf.hyp0.wk.wk : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift)
  have hj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp1
  have actual := (recode_congr (change_lookup (Γ := Δ) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift m))
      (var 1) (var 0) hr hj)).eqTrans
    ((recode_congr (GaussianVandermondeNewtonPolynomials.coefficient_above _ _ _ Prf.hyp0)).eqTrans
      (recode_eq qzero qzero_canonical))
  simpa [Δ,belowZeros,GaussianScalarTriangularDeterminant.belowRow,Syn.shift,Fm.shift] using actual

theorem change_diagonal_ones (R m : PTm n) : Γ ⊢[PRAAx] diagonalOnes (change R m) m := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have actual := (recode_congr (change_lookup (Γ := Δ) (Syn.shift R) (Syn.shift m) (var 0) (var 0) Prf.hyp0 Prf.hyp0)).eqTrans
    ((recode_congr (GaussianVandermondeNewtonPolynomials.coefficient_diagonal _ _)).eqTrans (recode_eq qone qone_canonical))
  simpa only [Δ,diagonalOnes,Syn.shift,subst_change] using actual

theorem change_det (R m : PTm n) : Γ ⊢[PRAAx] scalarDet (change R m) m ≐ qone :=
  GaussianScalarTriangularDeterminant.unit_triangular_det _ _ (.orI₁ (change_upper _ _)) (change_diagonal_ones _ _)

theorem dot_power_sum (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    scalarDot (U R m) (change R m) m r j ≐
      GaussianVandermondeNewtonPolynomials.powerSum R j (entry R r) m := by
  refine GaussianRationalFiniteSum.sum_congr_bounded scalarBody GaussianVandermondeNewtonPolynomials.powerBody m
    (scalarData (U R m) (change R m) r j) (GaussianVandermondeNewtonPolynomials.powerData R j (entry R r)) (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
  have rs : Δ ⊢[PRAAx] lt (Syn.shift r) (length (Syn.shift R)) := by
    simpa [Δ,Fm.shift,Syn.shift] using
      (hr.shift.wk : Δ ⊢[PRAAx] (lt r (length R)).shift)
  have js : Δ ⊢[PRAAx] lt (Syn.shift j) (Syn.shift m) := by
    simpa [Δ,Fm.shift,Syn.shift] using (hj.shift.wk : Δ ⊢[PRAAx] (lt j m).shift)
  have actual := (scalar_body_at (Γ := Δ) (U (Syn.shift R) (Syn.shift m)) (change (Syn.shift R) (Syn.shift m))
      (Syn.shift r) (Syn.shift j) (var 0)).eqTrans
    ((qmul_congr (U_lookup _ _ _ _ rs Prf.hyp0) (change_lookup _ _ _ _ Prf.hyp0 js)).eqTrans
      (GaussianVandermondeNewtonPolynomials.power_body_at _ _ _ _).eqSymm)
  simpa only [Δ,Syn.shift,GaussianRationalFiberVandermonde.subst_U,subst_change,
    GaussianRationalMatrixFiniteSums.subst_scalarData,GaussianVandermondeNewtonPolynomials.subst_powerData,
    Foundations.MasterCertificate.subst_entry] using actual

theorem product_evaluation (R m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hR : Γ ⊢[PRAAx] lt r (length R)) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (transformed R m) r j ≐ evaluate (polynomial R j) (entry R r) :=
  (product_lookup _ _ _ _ _ hr hj).eqTrans
    ((dot_power_sum _ _ _ _ hR hj).eqTrans (GaussianVandermondeNewtonPolynomials.power_sum_evaluation _ _ _ _ hj))

theorem square_lower (R : PTm n) : Γ ⊢[PRAAx] aboveZeros (transformed R (length R)) (length R) := by
  refine .allI (.impI (.allI (.impI (.impI ?_))))
  let Δ := lt (var 1) (var 0) :: lt (var 0) (Syn.shift (Syn.shift (length R))) ::
    (lt (var 0) (Syn.shift (length R))).shift :: (Γ.map Fm.shift).map Fm.shift
  have hr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift (length R))) := by
    simpa [Δ,Fm.shift,Syn.shift] using
      (Prf.hyp0.wk.wk : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift (length R))).shift)
  have actual := (recode_congr (product_evaluation (Γ := Δ) (Syn.shift (Syn.shift R))
      (length (Syn.shift (Syn.shift R))) (var 1) (var 0) (by simpa [Syn.shift] using hr) (by simpa [Syn.shift] using hr) (by simpa [Δ,Syn.shift] using (Prf.hyp1 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift (length R))))))).eqTrans
    ((recode_congr (GaussianVandermondeNewtonPolynomials.prior_root_zero _ _ _ Prf.hyp0)).eqTrans (recode_eq qzero qzero_canonical))
  simpa [Δ,aboveZeros,GaussianScalarTriangularDeterminant.aboveRow,Syn.shift,Fm.shift] using actual

theorem square_diagonal (R j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length R)) : Γ ⊢[PRAAx]
    cell (transformed R (length R)) j j ≐ differenceProduct R (entry R j) j :=
  (product_evaluation _ _ _ _ hj hj hj).eqTrans (GaussianVandermondeNewtonPolynomials.diagonal_evaluation _ _)

theorem square_diagonal_product (R : PTm n) : Γ ⊢[PRAAx]
    diagonalProduct (transformed R (length R)) (length R) ≐ pairProduct R (length R) := by
  refine GaussianRationalFiniteProduct.product_congr_bounded GaussianScalarTriangularDeterminant.diagonalBody
    GaussianVandermondeNewtonPolynomials.pairBody (length R) (transformed R (length R)) R (.allI (.impI ?_))
  let Δ := lt (var 0) (Syn.shift (length R)) :: Γ.map Fm.shift
  have actual := square_diagonal (Γ := Δ) (Syn.shift R) (var 0) (by simpa [Δ,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (length R))))
  simpa only [Δ,Syn.shift,GaussianScalarTriangularDeterminant.diagonal_body_at,
    GaussianVandermondeNewtonPolynomials.pair_body_at,subst_transformed,Foundations.SequenceComposition.subst_length] using actual

theorem square_det (R : PTm n) : Γ ⊢[PRAAx]
    scalarDet (U R (length R)) (length R) ≐ pairProduct R (length R) := by
  have product := (GaussianScalarDeterminantMultiplication.scalar_det_multiply (Γ := Γ) (U R (length R))
      (change R (length R)) (length R)).eqTrans
    ((qmul_congr (.eqRefl _) (change_det R (length R))).eqTrans
      (GaussianReciprocalHorner.qmul_one_right _ (scalar_det_canonical _ _)))
  exact product.eqSymm.eqTrans ((GaussianScalarTriangularDeterminant.lower_triangular_det _ _ (square_lower R)).eqTrans
    (square_diagonal_product R))

theorem change_shape (R m : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (change R m) m := by
  refine .andI (change_length R m) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_change] using change_row_length (Syn.shift R) (Syn.shift m) (var 0) Prf.hyp0
theorem transformed_shape (R m : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (transformed R m) m :=
  GaussianRationalMatrixFiniteSums.product_shape _ _ _

def changeF : PR 2 := PTm.toPR (change (var 0) (var 1))
def output (R : PTm n) : PTm n := pairT (U R (length R)) (pairT (change R (length R))
  (pairT (transformed R (length R)) (pairT (scalarDet (U R (length R)) (length R)) (pairProduct R (length R)))))
def outputF : PR 1 := PTm.toPR (output (var 0))
def run (R : PTm n) : PTm n := app outputF ![R]
def fields (p : PTm n) : Fin 5 → PTm n := ![fstT p,fstT (sndT p),fstT (sndT (sndT p)),
  fstT (sndT (sndT (sndT p))),sndT (sndT (sndT (sndT p)))]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (output R) = output (Syn.subst σ R) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (run R) = run (Syn.subst σ R) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i
  rfl
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (p : PTm n) (i : Fin 5) :
    Syn.subst σ (fields p i) = fields (Syn.subst σ p) i := by fin_cases i <;> simp [fields]
theorem change_program_at (R m : PTm n) : Γ ⊢[PRAAx] app changeF ![R,m] ≐ change R m := by
  simpa [changeF] using toPR_eq (Γ := Γ) (change (var 0) (var 1) : PTm 2) ![R,m]
theorem program_at (R : PTm n) : Γ ⊢[PRAAx] run R ≐ output R := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) : PTm 1) ![R]
theorem returned_fields (R : PTm n) (i : Fin 5) : Γ ⊢[PRAAx] fields (run R) i ≐
    ![U R (length R),change R (length R),transformed R (length R),
      scalarDet (U R (length R)) (length R),pairProduct R (length R)] i := by
  have e0 := program_at (Γ := Γ) R
  have e1 := (congrSnd e0).eqTrans (snd_pair _ _)
  have e2 := (congrSnd e1).eqTrans (snd_pair _ _)
  have e3 := (congrSnd e2).eqTrans (snd_pair _ _)
  fin_cases i
  · exact (congrFst e0).eqTrans (fst_pair _ _)
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrSnd e3).eqTrans (snd_pair _ _)
theorem returned_equality (R : PTm n) : Γ ⊢[PRAAx] fields (run R) 3 ≐ fields (run R) 4 :=
  (returned_fields R 3).eqTrans ((square_det R).eqTrans (returned_fields R 4).eqSymm)
theorem returned_change_det (R : PTm n) : Γ ⊢[PRAAx] scalarDet (fields (run R) 1) (length R) ≐ qone := by
  have eq : Γ ⊢[PRAAx] scalarDet (fields (run R) 1) (length R) ≐ scalarDet (change R (length R)) (length R) := by
    simpa only [GaussianScalarDeterminant.subst_scalarDet,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (scalarDet (var 0) (var 1) : PTm 2)
        (σ := ![fields (run R) 1,length R]) (σ' := ![change R (length R),length R])
        (fun i => by fin_cases i; exact returned_fields R 1; exact .eqRefl _)
  exact eq.eqTrans (change_det R (length R))

theorem actual_change_lookup_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 3) (var 1) ⟶
      cell (change (var 0) (var 1)) (var 2) (var 3) ≐ coefficient (var 0) (var 3) (var 2)) :=
  closeUniv 4 (.impI (.impI (change_lookup _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_change_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalMatrixFiniteSums.squareShape (change (var 0) (var 1)) (var 1)) := closeUniv 2 (change_shape _ _)
theorem actual_change_upper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (belowZeros (change (var 0) (var 1)) (var 1)) := closeUniv 2 (change_upper _ _)
theorem actual_change_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (change (var 0) (var 1)) (var 1) ≐ qone) := closeUniv 2 (change_det _ _)
theorem actual_product_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ lt (var 3) (var 1) ⟶
      cell (transformed (var 0) (var 1)) (var 2) (var 3) ≐ evaluate (polynomial (var 0) (var 3)) (entry (var 0) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (product_evaluation _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_transformed_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (GaussianRationalMatrixFiniteSums.squareShape (transformed (var 0) (var 1)) (var 1)) := closeUniv 2 (transformed_shape _ _)
theorem actual_square_lower_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (aboveZeros (transformed (var 0) (length (var 0))) (length (var 0))) := closeUniv 1 (square_lower _)
theorem actual_square_diagonal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (length (var 0)) ⟶ cell (transformed (var 0) (length (var 0))) (var 1) (var 1) ≐
      differenceProduct (var 0) (entry (var 0) (var 1)) (var 1)) := closeUniv 2 (.impI (square_diagonal _ _ Prf.hyp0))
theorem actual_diagonal_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (diagonalProduct (transformed (var 0) (length (var 0))) (length (var 0)) ≐ pairProduct (var 0) (length (var 0))) :=
  closeUniv 1 (square_diagonal_product _)
theorem actual_square_vandermonde_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (scalarDet (U (var 0) (length (var 0))) (length (var 0)) ≐ pairProduct (var 0) (length (var 0))) := closeUniv 1 (square_det _)
theorem actual_change_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (app changeF ![var 0,var 1] ≐ change (var 0) (var 1)) := closeUniv 2 (change_program_at _ _)
theorem actual_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (run (var 0) ≐ output (var 0)) := closeUniv 1 (program_at _)
theorem actual_returned_equality_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (fields (run (var 0)) 3 ≐ fields (run (var 0)) 4) := closeUniv 1 (returned_equality _)
theorem actual_returned_change_det_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (scalarDet (fields (run (var 0)) 1) (length (var 0)) ≐ qone) := closeUniv 1 (returned_change_det _)

end LeanProofs.IPRA.Analysis.GaussianVandermondeNewtonMatrix

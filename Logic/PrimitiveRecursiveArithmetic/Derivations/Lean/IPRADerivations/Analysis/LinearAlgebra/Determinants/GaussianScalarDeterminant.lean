import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalAdjacentProduct
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminant
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality

/-!
# Scalar observations of the SAME actual runtime polynomial determinant

A scalar table is lifted by actual singleton cells and passed to the
existing polynomial determinant. Its scalar value is that actual output
evaluated at zero. Actual evaluated tables and bounded individual cell
value congruence bind arbitrary polynomial observations to the same
producer, preserving numerical dimensions and original raw cell codes.
No abstract determinant interpretation or outer table-code extensionality
is assumed. Multiplication and the identity determinant are separate.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminant

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open LeanProofs.IPRA.Analysis.GaussianRationalMonicReduction (singleton singleton_length singleton_evaluation evaluate_congr)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell tableShape rowCells signPoint scalarProduct)
open LeanProofs.IPRA.Analysis.GaussianRationalFiberVandermonde (table table_length table_row_length table_lookup)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalFiniteProduct (qprod)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def constantBody : PTm 3 := singleton (cell (var 2) (var 0) (var 1))
def constantTable (A m : PTm n) : PTm n := table constantBody m m A
def evaluationBody : PTm 3 := evaluate (cell (fstT (var 2)) (var 0) (var 1)) (sndT (var 2))
def evaluatedTable (M m z : PTm n) : PTm n := table evaluationBody m m (pairT M z)
def scalarDet (A m : PTm n) : PTm n := evaluate (GaussianPolynomialDeterminant.determinant (constantTable A m) m zero) qzero

ipra_subst constantTable
ipra_subst evaluatedTable
ipra_subst scalarDet

theorem constant_lookup (A m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (constantTable A m) r j ≐ singleton (cell A r j) := by
  simpa [constantTable,constantBody] using table_lookup constantBody m m A r j hr hj
theorem constant_cell_length (A m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    length (cell (constantTable A m) r j) ≐ one :=
  (congrFst (constant_lookup _ _ _ _ hr hj)).eqTrans (singleton_length _)
theorem constant_row_cells (A m r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    rowCells (constantTable A m) m zero r := by
  refine .allI (.impI ?_)
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  simpa only [Syn.shift,subst_constantTable,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using
    constant_cell_length (Syn.shift A) (Syn.shift m) (Syn.shift r) (var 0) rs.wk Prf.hyp0
theorem constant_shape (A m : PTm n) : Γ ⊢[PRAAx] tableShape (constantTable A m) m zero := by
  refine .andI (table_length _ _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa only [Syn.shift,subst_constantTable,constantTable,GaussianRationalFiberVandermonde.subst_table] using
      table_row_length constantBody (Syn.shift m) (Syn.shift m) (Syn.shift A) (var 0) Prf.hyp0
  · simpa only [Syn.shift,subst_constantTable,ConciseIPRA.PTm.subst_zero] using
      constant_row_cells (Syn.shift A) (Syn.shift m) (var 0) Prf.hyp0

theorem constant_cell_evaluation (A m r j z : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell (constantTable A m) r j) z ≐ recode (cell A r j) :=
  (evaluate_congr (constant_lookup _ _ _ _ hr hj) (.eqRefl _)).eqTrans (singleton_evaluation _ _)
theorem evaluated_lookup (M m z r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    cell (evaluatedTable M m z) r j ≐ evaluate (cell M r j) z := by
  have e : Γ ⊢[PRAAx] cell (evaluatedTable M m z) r j ≐ evaluate (cell (fstT (pairT M z)) r j) (sndT (pairT M z)) := by
    simpa [evaluatedTable,evaluationBody] using table_lookup evaluationBody m m (pairT M z) r j hr hj
  exact e.eqTrans (evaluate_congr (entry_congr (entry_congr (fst_pair _ _) (.eqRefl _)) (.eqRefl _)) (snd_pair _ _))
theorem evaluated_canonical (M m z r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    canonical (cell (evaluatedTable M m z) r j) :=
  GaussianRationalHorner.canonical_congr (evaluated_lookup _ _ _ _ _ hr hj) (GaussianRationalHorner.horner_canonical _ _ _)
theorem scalar_det_canonical (A m : PTm n) : Γ ⊢[PRAAx] canonical (scalarDet A m) := GaussianRationalHorner.horner_canonical _ _ _

/-- The raw scalar factors are read in exactly the original column-position order. -/
def factorData (A m w : PTm n) : PTm n := pairT A (pairT m w)
def factorBody : PTm 2 := cell (fstT (var 1))
  (Foundations.RuntimePermutationWords.digit (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)) (var 0)
def rawProduct (A m w : PTm n) : PTm n := qprod factorBody m (factorData A m w)
ipra_subst factorData
ipra_subst rawProduct

theorem factor_body_at (A m w i : PTm n) : Γ ⊢[PRAAx]
    inst2 factorBody i (factorData A m w) ≐ cell A (Foundations.RuntimePermutationWords.digit m w i) i := by
  simp only [factorBody,inst2,GaussianPolynomialDeterminantTerms.subst_cell,Foundations.RuntimePermutationWords.subst_digit,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact entry_congr (entry_congr (fst_pair _ _)
    (Foundations.RuntimeAdjacentPermutationSwap.digit_congr (snd_pair _ _).fstE
      (snd_pair _ _).sndE (.eqRefl _))) (.eqRefl _)

theorem constant_scalar_product (A m w z : PTm n) : Γ ⊢[PRAAx]
    scalarProduct (constantTable A m) m zero w z m ≐ rawProduct A m w := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianRationalAdjacentProduct.evaluatedFactorBody
      (GaussianRationalFiniteProduct.recodeBody factorBody) m
      (GaussianRationalAdjacentProduct.factorData (constantTable A m) m zero w z) (factorData A m w) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 GaussianRationalAdjacentProduct.evaluatedFactorBody (var 0)
        (GaussianRationalAdjacentProduct.factorData (constantTable (Syn.shift A) (Syn.shift m)) (Syn.shift m) zero (Syn.shift w) (Syn.shift z)) ≐
        recode (inst2 factorBody (var 0) (factorData (Syn.shift A) (Syn.shift m) (Syn.shift w))) :=
      (GaussianRationalAdjacentProduct.evaluated_factor_at _ _ _ _ _ _).eqTrans
        ((constant_cell_evaluation _ _ _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ Prf.hyp0) Prf.hyp0).eqTrans
          (recode_congr (factor_body_at _ _ _ _)).eqSymm)
    simpa only [Δ,Syn.shift,GaussianRationalFiniteProduct.recode_body_at,GaussianRationalAdjacentProduct.subst_factorData,
      subst_constantTable,subst_factorData,ConciseIPRA.PTm.subst_zero] using e
  exact (GaussianRationalAdjacentProduct.scalar_product_as_qprod _ _ _ _ _ _).eqTrans
    ((GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ terms).eqTrans
      (GaussianRationalFiniteProduct.product_recode factorBody m (factorData A m w)))

def signedTerm (A m t : PTm n) : PTm n := qmul (signPoint m (GaussianPolynomialDeterminant.wordCode m t))
  (rawProduct A m (GaussianPolynomialDeterminant.wordCode m t))
def signedBody : PTm 2 := signedTerm (fstT (var 1)) (sndT (var 1)) (var 0)
def scalarSum (A m : PTm n) : PTm n := GaussianRationalFiniteSum.sum signedBody
  (Foundations.RuntimePermutationWords.count m) (pairT A m)
ipra_subst signedTerm
ipra_subst scalarSum

theorem signed_body_at (A m t : PTm n) : Γ ⊢[PRAAx] inst2 signedBody t (pairT A m) ≐ signedTerm A m t := by
  simp only [signedBody,inst2,subst_signedTerm,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  ipra_congr (signedTerm (var 0) (var 1) (var 2) : PTm 3) with [fst_pair _ _, snd_pair _ _, .eqRefl t]

theorem scalar_leibniz (A m : PTm n) : Γ ⊢[PRAAx] scalarDet A m ≐ scalarSum A m := by
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianPolynomialDeterminant.valueBody signedBody
      (Foundations.RuntimePermutationWords.count m)
      (GaussianPolynomialDeterminantTerms.data (constantTable A m) m zero qzero) (pairT A m) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 GaussianPolynomialDeterminant.valueBody (var 0)
        (GaussianPolynomialDeterminantTerms.data (constantTable (Syn.shift A) (Syn.shift m)) (Syn.shift m) zero qzero) ≐
        inst2 signedBody (var 0) (pairT (Syn.shift A) (Syn.shift m)) :=
      (GaussianPolynomialDeterminant.value_body_at _ _ _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) (constant_scalar_product _ _ _ _)).eqTrans (signed_body_at _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianPolynomialDeterminantTerms.subst_data,subst_constantTable,subst_pairT,
      ConciseIPRA.PTm.subst_zero,GaussianRationalHorner.subst_qzero] using e
  exact (GaussianPolynomialDeterminant.evaluation_leibniz _ _ _ _ (constant_shape A m)).eqTrans
    (GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms)

/-- Only bounded original cell VALUE equations, with independent query codes. -/
def rowValuesEqual (M N m r z y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ evaluate (cell (Syn.shift M) (Syn.shift r) (var 0)) (Syn.shift z) ≐
    evaluate (cell (Syn.shift N) (Syn.shift r) (var 0)) (Syn.shift y))
def cellValuesEqual (M N m z y : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ rowValuesEqual (Syn.shift M) (Syn.shift N) (Syn.shift m) (var 0) (Syn.shift z) (Syn.shift y))
ipra_subst rowValuesEqual [Syn.subst_shift, Syn.shift_subst]
ipra_subst cellValuesEqual [Syn.subst_shift, Syn.shift_subst]

theorem cell_value_at (M N m z y r j : PTm n) (h : Γ ⊢[PRAAx] cellValuesEqual M N m z y)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    evaluate (cell M r j) z ≐ evaluate (cell N r j) y := by
  have outer : Γ ⊢[PRAAx] lt r m ⟶ rowValuesEqual M N m r z y := by simpa [cellValuesEqual] using h.allE r
  have inner : Γ ⊢[PRAAx] lt j m ⟶ evaluate (cell M r j) z ≐ evaluate (cell N r j) y := by
    simpa [rowValuesEqual] using (Prf.impE outer hr).allE j
  exact .impE inner hj

/-- The SAME original scalarProduct program observes only the bounded cells.
No table shape is required until evaluation of the polynomial determinant. -/
theorem scalar_products_congr_values (M N m L K w z y : PTm n)
    (h : Γ ⊢[PRAAx] cellValuesEqual M N m z y) : Γ ⊢[PRAAx]
    scalarProduct M m L w z m ≐ scalarProduct N m K w y m := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cellValuesEqual (Syn.shift M) (Syn.shift N) (Syn.shift m) (Syn.shift z) (Syn.shift y) := by
    simpa only [Fm.shift,subst_cellValuesEqual,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianRationalAdjacentProduct.evaluatedFactorBody
      GaussianRationalAdjacentProduct.evaluatedFactorBody m
      (GaussianRationalAdjacentProduct.factorData M m L w z) (GaussianRationalAdjacentProduct.factorData N m K w y) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 GaussianRationalAdjacentProduct.evaluatedFactorBody (var 0)
        (GaussianRationalAdjacentProduct.factorData (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift w) (Syn.shift z)) ≐
        inst2 GaussianRationalAdjacentProduct.evaluatedFactorBody (var 0)
          (GaussianRationalAdjacentProduct.factorData (Syn.shift N) (Syn.shift m) (Syn.shift K) (Syn.shift w) (Syn.shift y)) :=
      (GaussianRationalAdjacentProduct.evaluated_factor_at _ _ _ _ _ _).eqTrans
        ((cell_value_at _ _ _ _ _ _ _ hs.wk (Foundations.RuntimePermutationWords.digit_bound _ _ _ Prf.hyp0) Prf.hyp0).eqTrans
          (GaussianRationalAdjacentProduct.evaluated_factor_at _ _ _ _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianRationalAdjacentProduct.subst_factorData] using e
  exact (GaussianRationalAdjacentProduct.scalar_product_as_qprod _ _ _ _ _ _).eqTrans
    ((GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ terms).eqTrans
      (GaussianRationalAdjacentProduct.scalar_product_as_qprod _ _ _ _ _ _).eqSymm)

/-- Different numerical polynomial widths and queries are allowed; no outer table equality. -/
theorem determinant_evaluation_congr (M N m L K z y : PTm n)
    (hM : Γ ⊢[PRAAx] tableShape M m L) (hN : Γ ⊢[PRAAx] tableShape N m K)
    (h : Γ ⊢[PRAAx] cellValuesEqual M N m z y) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant M m L) z ≐
      evaluate (GaussianPolynomialDeterminant.determinant N m K) y := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] cellValuesEqual (Syn.shift M) (Syn.shift N) (Syn.shift m) (Syn.shift z) (Syn.shift y) := by
    simpa only [Fm.shift,subst_cellValuesEqual,Syn.shift] using h.shift
  have terms : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual GaussianPolynomialDeterminant.valueBody GaussianPolynomialDeterminant.valueBody
      (Foundations.RuntimePermutationWords.count m) (GaussianPolynomialDeterminantTerms.data M m L z) (GaussianPolynomialDeterminantTerms.data N m K y) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] inst2 GaussianPolynomialDeterminant.valueBody (var 0)
        (GaussianPolynomialDeterminantTerms.data (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift z)) ≐
        inst2 GaussianPolynomialDeterminant.valueBody (var 0)
          (GaussianPolynomialDeterminantTerms.data (Syn.shift N) (Syn.shift m) (Syn.shift K) (Syn.shift y)) :=
      (GaussianPolynomialDeterminant.value_body_at _ _ _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) (scalar_products_congr_values _ _ _ _ _ _ _ _ hs.wk)).eqTrans
          (GaussianPolynomialDeterminant.value_body_at _ _ _ _ _).eqSymm)
    simpa only [Δ,Syn.shift,GaussianPolynomialDeterminantTerms.subst_data] using e
  exact (GaussianPolynomialDeterminant.evaluation_leibniz _ _ _ _ hM).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans
      (GaussianPolynomialDeterminant.evaluation_leibniz _ _ _ _ hN).eqSymm)

/-- A real evaluated-table constructor binds the scalar observer to arbitrary polynomial inputs. -/
theorem determinant_evaluation_specialization (M m L z : PTm n) (hM : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant M m L) z ≐ scalarDet (evaluatedTable M m z) m := by
  have terms : Γ ⊢[PRAAx] cellValuesEqual M (constantTable (evaluatedTable M m z) m) m z qzero := by
    refine .allI (.impI (.allI (.impI ?_)))
    let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
    have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
    have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
    have e := (constant_cell_evaluation (Γ := Δ) (evaluatedTable (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift m)) (Syn.shift (Syn.shift z)))
      (Syn.shift (Syn.shift m)) (var 1) (var 0) qzero rr jj).eqTrans
        ((recode_eq _ (evaluated_canonical _ _ _ _ _ rr jj)).eqTrans (evaluated_lookup _ _ _ _ _ rr jj))
    simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_evaluatedTable,subst_constantTable,GaussianRationalHorner.subst_qzero] using e.eqSymm
  exact determinant_evaluation_congr _ _ _ _ _ _ _ hM (constant_shape _ _) terms

/-- Native decoded FIELD equality of original scalar cells, not raw code equality. -/
def scalarRowEqual (A B m r : PTm n) : Fm PTm n := .all (lt (var 0) (Syn.shift m) ⟶
  GaussianRationalValueEquality.valueEqual (cell (Syn.shift A) (Syn.shift r) (var 0)) (cell (Syn.shift B) (Syn.shift r) (var 0)))
def scalarCellsEqual (A B m : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift m) ⟶ scalarRowEqual (Syn.shift A) (Syn.shift B) (Syn.shift m) (var 0))
ipra_subst scalarRowEqual [Syn.subst_shift, Syn.shift_subst]
ipra_subst scalarCellsEqual [Syn.subst_shift, Syn.shift_subst]

theorem scalar_cell_at (A B m r j : PTm n) (h : Γ ⊢[PRAAx] scalarCellsEqual A B m)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    GaussianRationalValueEquality.valueEqual (cell A r j) (cell B r j) := by
  have outer : Γ ⊢[PRAAx] lt r m ⟶ scalarRowEqual A B m r := by simpa [scalarCellsEqual] using h.allE r
  have inner : Γ ⊢[PRAAx] lt j m ⟶ GaussianRationalValueEquality.valueEqual (cell A r j) (cell B r j) := by
    simpa [scalarRowEqual] using (Prf.impE outer hr).allE j
  exact .impE inner hj

theorem scalar_det_congr (A B m : PTm n) (h : Γ ⊢[PRAAx] scalarCellsEqual A B m) : Γ ⊢[PRAAx] scalarDet A m ≐ scalarDet B m := by
  have values : Γ ⊢[PRAAx] cellValuesEqual (constantTable A m) (constantTable B m) m qzero qzero := by
    refine .allI (.impI (.allI (.impI ?_)))
    let Δ := lt (var 0) (Syn.shift (Syn.shift m)) :: List.map Fm.shift (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift)
    have rr0 : Δ ⊢[PRAAx] (lt (var 0) (Syn.shift m)).shift := Prf.hyp1
    have rr : Δ ⊢[PRAAx] lt (var 1) (Syn.shift (Syn.shift m)) := by
      simpa only [Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one] using rr0
    have jj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift (Syn.shift m)) := Prf.hyp0
    have hs : Δ ⊢[PRAAx] scalarCellsEqual (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift m)) := by
      simpa only [Δ,List.map_cons,Fm.shift,subst_scalarCellsEqual,Syn.shift] using h.shift.shift.wk.wk
    have native := scalar_cell_at _ _ _ _ _ hs rr jj
    have e := (constant_cell_evaluation (Γ := Δ) (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift m)) (var 1) (var 0) qzero rr jj).eqTrans
      (((GaussianRationalValueEquality.recode_equal_iff _ _).iffMpr native).eqTrans
        (constant_cell_evaluation (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift m)) (var 1) (var 0) qzero rr jj).eqSymm)
    simpa only [Δ,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_constantTable,GaussianRationalHorner.subst_qzero] using e
  exact determinant_evaluation_congr _ _ _ _ _ _ _ (constant_shape _ _) (constant_shape _ _) values

/-- Actual scalar payload retains the lifted table and SAME old determinant run. -/
def output (A m : PTm n) : PTm n := pairT (constantTable A m)
  (pairT (GaussianPolynomialDeterminant.run (constantTable A m) m zero) (scalarDet A m))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
def run (A m : PTm n) : PTm n := ap2 outputF A m
def evaluatedF : PR 3 := PTm.toPR (evaluatedTable (var 0) (var 1) (var 2))
ipra_subst output
ipra_subst run

theorem program_at (A m : PTm n) : Γ ⊢[PRAAx] run A m ≐ output A m := by
  simpa [run,outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![A,m]
theorem evaluated_program_at (M m z : PTm n) : Γ ⊢[PRAAx] ap3 evaluatedF M m z ≐ evaluatedTable M m z := by
  simpa [evaluatedF,ap3] using toPR_eq (Γ := Γ) (evaluatedTable (var 0) (var 1) (var 2) : PTm 3) ![M,m,z]
theorem returned_table (A m : PTm n) : Γ ⊢[PRAAx] fstT (run A m) ≐ constantTable A m :=
  (program_at _ _).fstE
theorem returned_old_run (A m : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run A m)) ≐ GaussianPolynomialDeterminant.run (constantTable A m) m zero :=
  (program_at _ _).sndE.fstE
theorem returned_polynomial (A m : PTm n) : Γ ⊢[PRAAx]
    fstT (fstT (sndT (run A m))) ≐ GaussianPolynomialDeterminant.determinant (constantTable A m) m zero :=
  (congrFst (returned_old_run _ _)).eqTrans (GaussianPolynomialDeterminant.returned_polynomial _ _ _)
theorem returned_scalar (A m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A m)) ≐ scalarDet A m :=
  (program_at _ _).sndE.sndE
theorem returned_evaluation (A m : PTm n) : Γ ⊢[PRAAx]
    evaluate (fstT (fstT (sndT (run A m)))) qzero ≐ sndT (sndT (run A m)) :=
  (evaluate_congr (returned_polynomial _ _) (.eqRefl _)).eqTrans (returned_scalar _ _).eqSymm
theorem returned_scalar_canonical (A m : PTm n) : Γ ⊢[PRAAx] canonical (sndT (sndT (run A m))) :=
  GaussianRationalHorner.canonical_congr (returned_scalar _ _) (scalar_det_canonical _ _)

theorem actual_scalar_leibniz_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (var 0) (var 1) ≐ scalarSum (var 0) (var 1)) := closeUniv 2 (scalar_leibniz _ _)
theorem actual_determinant_value_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (tableShape (var 0) (var 2) (var 3) ⟶ tableShape (var 1) (var 2) (var 4) ⟶
      cellValuesEqual (var 0) (var 1) (var 2) (var 5) (var 6) ⟶
        evaluate (GaussianPolynomialDeterminant.determinant (var 0) (var 2) (var 3)) (var 5) ≐
          evaluate (GaussianPolynomialDeterminant.determinant (var 1) (var 2) (var 4)) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (determinant_evaluation_congr _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_scalar_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) (var 1) (var 2) ⟶ evaluate (GaussianPolynomialDeterminant.determinant (var 0) (var 1) (var 2)) (var 3) ≐
      scalarDet (evaluatedTable (var 0) (var 1) (var 3)) (var 1)) :=
  closeUniv 4 (.impI (determinant_evaluation_specialization _ _ _ _ Prf.hyp0))
theorem actual_scalar_native_congruence_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scalarCellsEqual (var 0) (var 1) (var 2) ⟶ scalarDet (var 0) (var 2) ≐ scalarDet (var 1) (var 2)) :=
  closeUniv 3 (.impI (scalar_det_congr _ _ _ Prf.hyp0))
theorem actual_evaluated_table_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap3 evaluatedF (var 0) (var 1) (var 2) ≐ evaluatedTable (var 0) (var 1) (var 2)) := closeUniv 3 (evaluated_program_at _ _ _)
theorem actual_evaluated_table_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ lt (var 4) (var 1) ⟶ cell (evaluatedTable (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
      evaluate (cell (var 0) (var 3) (var 4)) (var 2)) :=
  closeUniv 5 (.impI (.impI (evaluated_lookup _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_scalar_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((run (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏
      (fstT (fstT (sndT (run (var 0) (var 1)))) ≐ GaussianPolynomialDeterminant.determinant (constantTable (var 0) (var 1)) (var 1) zero)) :=
  closeUniv 2 (.andI (program_at _ _) (returned_polynomial _ _))
theorem actual_returned_scalar_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((evaluate (fstT (fstT (sndT (run (var 0) (var 1))))) qzero ≐ sndT (sndT (run (var 0) (var 1)))) ⋏
      canonical (sndT (sndT (run (var 0) (var 1))))) :=
  closeUniv 2 (.andI (returned_evaluation _ _) (returned_scalar_canonical _ _))

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminant

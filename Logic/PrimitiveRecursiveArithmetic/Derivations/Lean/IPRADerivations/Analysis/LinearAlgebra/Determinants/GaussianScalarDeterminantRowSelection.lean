import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminantMultiplication
import IPRADerivations.Foundations.RuntimePermutationDeletion

/-!
# Exact numerical row selection preserves a vanishing determinant

Multiply the input by the actual table of row selectors. Each resulting
entry is the canonical read of the chosen original row. No bijection is
required to transport a vanishing determinant. A zero last row itself
gives a zero factor in every retained Leibniz term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantRowSelection

open_ipra
open GaussianRationalFiberVandermonde (table table_lookup delta)
open GaussianPolynomialDeterminantTerms (cell signPoint)
open GaussianScalarDeterminant (scalarDet signedBody signedTerm factorBody factorData rawProduct)
open GaussianRationalMatrixFiniteSums (matrixProduct product_lookup scalarDot scalarBody scalarData scalar_body_at deltaBody deltaSum delta_body_at)
open GaussianRationalHorner (qzero)
open GaussianTranslatedNonconstant (recode)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianRationalFiniteSum (termsEqual)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.RuntimePermutationWords (count words digit retained_bound retained_valid checker_reflection)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (maximumPosition maximum_correct)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def selectorBody (f : PTm 2) : PTm 3 := delta (inst2 f (var 0) (var 2)) (var 1)
def selectorTable (f : PTm 2) (m x : PTm n) : PTm n := table (selectorBody f) m m x
def selected (f : PTm 2) (A m x : PTm n) : PTm n := matrixProduct (selectorTable f m x) A m
def originalColumn : PTm 2 := cell (fstT (var 1)) (var 0) (sndT (var 1))
def zeroLastRow (A m : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift m)) ⟶ cell (Syn.shift A) (Syn.shift m) (var 0) ≐ qzero)

ipra_subst selectorTable
ipra_subst selected
ipra_subst zeroLastRow [Syn.subst_shift, Syn.shift_subst]

theorem selector_lookup (f : PTm 2) (m x r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] cell (selectorTable f m x) r j ≐ delta (inst2 f r x) j := by
  simpa only [selectorTable,selectorBody,GaussianRationalFiberVandermonde.subst_delta,subst_inst2,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using
    table_lookup (selectorBody f) m m x r j hr hj

theorem column_at (A j k : PTm n) : Γ ⊢[PRAAx] inst2 originalColumn k (pairT A j) ≐ cell A k j := by
  simpa [originalColumn,inst2] using
    GaussianScalarColumnSelection.cell_congr (fst_pair (Γ := Γ) A j) (.eqRefl k) (snd_pair A j)

theorem selector_dot (f : PTm 2) (A m x r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    scalarDot (selectorTable f m x) A m r j ≐ deltaSum originalColumn m (inst2 f r x) (pairT A j) := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  let a := Syn.shift A
  let b := Syn.shift m
  let s := Syn.shift x
  let p := Syn.shift r
  let q := Syn.shift j
  let Δ := lt (var 0) b :: Γ.map Fm.shift
  have hp : Δ ⊢[PRAAx] lt p b := by simpa only [Δ,p,b,Fm.shift,Syn.shift,subst_lt] using hr.shift.wk
  have hi : Δ ⊢[PRAAx] lt (var 0) b := Prf.hyp0
  have actual := scalar_body_at (Γ := Δ) (selectorTable f b s) a p q (var 0)
  have e := qmul_congr (selector_lookup f b s p (var 0) hp hi) (column_at a q (var 0)).eqSymm
  simpa only [Δ,a,b,s,p,q,Syn.shift,subst_pairT,subst_inst2,subst_selectorTable,GaussianRationalMatrixFiniteSums.subst_scalarData] using
    actual.eqTrans (e.eqTrans (delta_body_at originalColumn (inst2 f p s) (var 0) (pairT a q)).eqSymm)

theorem selected_lookup (f : PTm 2) (A m x r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j m)
    (hIndex : Γ ⊢[PRAAx] lt (inst2 f r x) m) : Γ ⊢[PRAAx] cell (selected f A m x) r j ≐ recode (cell A (inst2 f r x) j) :=
  (product_lookup (selectorTable f m x) A m r j hr hj).eqTrans ((selector_dot f A m x r j hr).eqTrans
    ((GaussianRationalMatrixFiniteSums.sum_delta originalColumn m (inst2 f r x) (pairT A j) hIndex).eqTrans
      (GaussianTranslatedNonconstant.recode_congr (column_at A j (inst2 f r x)))))

theorem selected_determinant_zero (f : PTm 2) (A m x : PTm n) (h : Γ ⊢[PRAAx] scalarDet A m ≐ qzero) :
    Γ ⊢[PRAAx] scalarDet (selected f A m x) m ≐ qzero :=
  (GaussianScalarDeterminantMultiplication.scalar_det_multiply (selectorTable f m x) A m).eqTrans
    ((qmul_congr (.eqRefl _) h).eqTrans (qmul_zero_right _))

theorem zero_last_at (A m j : PTm n) (h : Γ ⊢[PRAAx] zeroLastRow A m) (hj : Γ ⊢[PRAAx] lt j (succ m)) :
    Γ ⊢[PRAAx] cell A m j ≐ qzero := by
  have rule : Γ ⊢[PRAAx] lt j (succ m) ⟶ cell A m j ≐ qzero := by simpa [zeroLastRow] using h.allE j
  exact .impE rule hj

theorem zero_last_term (A m r : PTm n) (hr : Γ ⊢[PRAAx] lt r (count (succ m))) (h : Γ ⊢[PRAAx] zeroLastRow A m) :
    Γ ⊢[PRAAx] signedTerm A (succ m) r ≐ qzero := by
  let w := entry (words (succ m)) r
  let j := maximumPosition m w
  have max := maximum_correct m w (retained_bound (succ m) r hr)
    ((checker_reflection _ _).iffMpr (retained_valid (succ m) r hr))
  have z := (GaussianScalarDeterminant.factor_body_at A (succ m) w j).eqTrans
    ((GaussianScalarColumnSelection.cell_congr (.eqRefl A) max.andE₂ (.eqRefl j)).eqTrans (zero_last_at A m j h max.andE₁))
  have prod := GaussianRationalProductAlgebra.product_zero_at factorBody (succ m) j (factorData A (succ m) w) max.andE₁ z
  exact (qmul_congr (.eqRefl _) prod).eqTrans (qmul_zero_right _)

theorem zero_last_determinant (A m : PTm n) (h : Γ ⊢[PRAAx] zeroLastRow A m) : Γ ⊢[PRAAx] scalarDet A (succ m) ≐ qzero := by
  have terms : Γ ⊢[PRAAx] termsEqual signedBody (qzero : PTm 2) (count (succ m)) (pairT A (succ m)) (pairT A (succ m)) := by
    refine .allI (.impI ?_)
    let a := Syn.shift A
    let b := Syn.shift m
    let Δ := lt (var 0) (count (succ b)) :: Γ.map Fm.shift
    have hr : Δ ⊢[PRAAx] lt (var 0) (count (succ b)) := Prf.hyp0
    have hz : Δ ⊢[PRAAx] zeroLastRow a b := by simpa only [Δ,a,b,Fm.shift,Syn.shift,subst_zeroLastRow] using h.shift.wk
    simpa [Δ,a,b,Syn.shift,inst2] using
      (GaussianScalarDeterminant.signed_body_at (Γ := Δ) a (succ b) (var 0)).eqTrans (zero_last_term a b (var 0) hr hz)
  exact (GaussianScalarDeterminant.scalar_leibniz A (succ m)).eqTrans
    ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ terms).eqTrans (GaussianRationalFubini.zero_body_sum _ _))

theorem actual_selected_rows_determinant_zero_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scalarDet (var 0) (var 1) ≐ qzero ⟶ scalarDet (selected f (var 0) (var 1) (var 2)) (var 1) ≐ qzero) :=
  closeUniv 3 (.impI (selected_determinant_zero f _ _ _ Prf.hyp0))

theorem actual_zero_last_row_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zeroLastRow (var 0) (var 1) ⟶ scalarDet (var 0) (succ (var 1)) ≐ qzero) :=
  closeUniv 2 (.impI (zero_last_determinant _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantRowSelection

import IPRADerivations.Foundations.RuntimeAdjacentPermutationSwap
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianDeterminantSignTransport
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalAdjacentProduct
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalPermutationSum
import IPRADerivations.Analysis.LinearAlgebra.Matrices.GaussianRationalMatrixFiniteSums
import IPRADerivations.Analysis.Polynomials.Determinants.GaussianPolynomialDeterminant
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual numerical column swaps and evaluated determinant alternation

The column table reuses the actual numerical tuple swap on each original
row. Invalid adjacent positions preserve that row. The determinant keeps
its original factor orientation M(digit_i,i): a column swap therefore
composes the permutation word at its positions, not at its row values.
All dimensions, polynomial codes, positions and queries are numerical.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialColumnAlternation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode subst_entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length entry_congr)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_zero sel_one)
open LeanProofs.IPRA.Analysis.GaussianPolynomialDeterminantTerms (cell tableShape rowCells)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qzero qadd qmul canonical evaluate)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnegative)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ app)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def active (m j : PTm n) : PTm n := Signum.sg (monus m (succ j))
def selectedRow (R m j : PTm n) : PTm n := sel (active m j)
  (Foundations.RuntimeAdjacentPermutationSwap.swapTuple R m j) R
def rowData (M m j : PTm n) : PTm n := pairT M (pairT m j)
def rowBody : PTm 2 := selectedRow (entry (fstT (var 1)) (var 0))
  (fstT (sndT (var 1))) (sndT (sndT (var 1)))
def CS (M m j : PTm n) : PTm n := sequence rowBody m (rowData M m j)

@[simp] theorem subst_active {l : ℕ} (σ : Fin n → PTm l) (m j : PTm n) :
    Syn.subst σ (active m j) = active (Syn.subst σ m) (Syn.subst σ j) := by simp [active]
@[simp] theorem subst_selectedRow {l : ℕ} (σ : Fin n → PTm l) (R m j : PTm n) :
    Syn.subst σ (selectedRow R m j) = selectedRow (Syn.subst σ R) (Syn.subst σ m) (Syn.subst σ j) := by simp [selectedRow,sel]
@[simp] theorem subst_rowData {l : ℕ} (σ : Fin n → PTm l) (M m j : PTm n) :
    Syn.subst σ (rowData M m j) = rowData (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ j) := by simp [rowData]
@[simp] theorem subst_CS {l : ℕ} (σ : Fin n → PTm l) (M m j : PTm n) :
    Syn.subst σ (CS M m j) = CS (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ j) := by simp [CS]

theorem selected_row_congr {R R' m m' j j' : PTm n}
    (hR : Γ ⊢[PRAAx] R ≐ R') (hm : Γ ⊢[PRAAx] m ≐ m') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    selectedRow R m j ≐ selectedRow R' m' j' := by
  ipra_congr (selectedRow (var 0) (var 1) (var 2) : PTm 3) with [hR, hm, hj]
theorem selected_row_active (R m j : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    selectedRow R m j ≐ Foundations.RuntimeAdjacentPermutationSwap.swapTuple R m j :=
  sel_one (AnalyticNumberTheory.Totatives.sg_lt hj)
theorem selected_row_inactive (R m j : PTm n) (hj : Γ ⊢[PRAAx] le m (succ j)) : Γ ⊢[PRAAx]
    selectedRow R m j ≐ R := sel_zero (AnalyticNumberTheory.Totatives.sg_le hj)
theorem selected_row_length (R m j : PTm n) (hR : Γ ⊢[PRAAx] length R ≐ m) : Γ ⊢[PRAAx]
    length (selectedRow R m j) ≐ m := by
  refine .orE (lt_or_le (succ j) m) ?_ ?_
  · exact (congrFst (selected_row_active _ _ _ Prf.hyp0)).eqTrans
      (Foundations.RuntimeAdjacentPermutationSwap.tuple_length _ _ _)
  · exact (congrFst (selected_row_inactive _ _ _ Prf.hyp0)).eqTrans hR.wk
theorem row_body_at (M m j r : PTm n) : Γ ⊢[PRAAx]
    inst2 rowBody r (rowData M m j) ≐ selectedRow (entry M r) m j := by
  simp only [rowBody,inst2,subst_selectedRow,subst_entry,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  have tail := snd_pair (Γ := Γ) M (pairT m j)
  exact selected_row_congr (entry_congr (fst_pair _ _) (.eqRefl _))
    ((congrFst tail).eqTrans (fst_pair _ _)) ((congrSnd tail).eqTrans (snd_pair _ _))
theorem CS_length (M m j : PTm n) : Γ ⊢[PRAAx] length (CS M m j) ≐ m := sequence_length _ _ _
theorem row_at (M m j r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx]
    entry (CS M m j) r ≐ selectedRow (entry M r) m j :=
  (sequence_decode rowBody hr).eqTrans (row_body_at _ _ _ _)
theorem cell_active (M m j r i : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hi : Γ ⊢[PRAAx] lt i m) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    cell (CS M m j) r i ≐ cell M r (Foundations.RuntimeAdjacentPermutationSwap.tau j i) :=
  (entry_congr ((row_at _ _ _ _ hr).eqTrans (selected_row_active _ _ _ hj)) (.eqRefl _)).eqTrans
    (Foundations.RuntimeAdjacentPermutationSwap.tuple_lookup _ _ _ _ hi)
theorem cell_inactive (M m j r i : PTm n) (hr : Γ ⊢[PRAAx] lt r m)
    (hj : Γ ⊢[PRAAx] le m (succ j)) : Γ ⊢[PRAAx] cell (CS M m j) r i ≐ cell M r i :=
  entry_congr ((row_at _ _ _ _ hr).eqTrans (selected_row_inactive _ _ _ hj)) (.eqRefl _)

theorem original_row_length (M m L r : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] length (entry M r) ≐ m := by
  have rule : Γ ⊢[PRAAx] lt r m ⟶ length (entry M r) ≐ m := by
    simpa using (Prf.andE₁ (Prf.andE₂ h)).allE r
  exact .impE rule hr
theorem CS_row_length (M m L j r : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] length (entry (CS M m j) r) ≐ m :=
  (congrFst (row_at _ _ _ _ hr)).eqTrans (selected_row_length _ _ _ (original_row_length _ _ _ _ h hr))
theorem CS_cell_length (M m L j r i : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    length (cell (CS M m j) r i) ≐ succ L := by
  refine .orE (lt_or_le (succ j) m) ?_ ?_
  · exact (congrFst (cell_active _ _ _ _ _ hr.wk hi.wk Prf.hyp0)).eqTrans
      (GaussianPolynomialDeterminantTerms.cell_length _ _ _ _ _ h.wk hr.wk
        (Foundations.RuntimeAdjacentPermutationSwap.tau_range _ _ _ Prf.hyp0 hi.wk))
  · exact (congrFst (cell_inactive _ _ _ _ _ hr.wk Prf.hyp0)).eqTrans
      (GaussianPolynomialDeterminantTerms.cell_length _ _ _ _ _ h.wk hr.wk hi.wk)
theorem CS_row_cells (M m L j r : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] rowCells (CS M m j) m L r := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using h.shift
  have rs : Γ.map Fm.shift ⊢[PRAAx] lt (Syn.shift r) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,Syn.shift] using hr.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_CS,GaussianPolynomialDeterminantTerms.subst_cell] using
    CS_cell_length (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift r) (var 0) hs.wk rs.wk Prf.hyp0
theorem CS_shape (M m L j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    tableShape (CS M m j) m L := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] tableShape (Syn.shift M) (Syn.shift m) (Syn.shift L) := by
    simpa only [Fm.shift,GaussianPolynomialDeterminantTerms.subst_tableShape,Syn.shift] using h.shift
  refine .andI (CS_length _ _ _) (.andI (.allI (.impI ?_)) (.allI (.impI ?_)))
  · simpa only [Syn.shift,subst_CS] using CS_row_length (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (var 0) hs.wk Prf.hyp0
  · simpa only [Syn.shift,subst_CS] using CS_row_cells (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (var 0) hs.wk Prf.hyp0

theorem CS_congr {M M' m m' j j' : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m') (hj : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx]
    CS M m j ≐ CS M' m' j' := by
  ipra_congr (CS (var 0) (var 1) (var 2) : PTm 3) with [hM, hm, hj]

/-- Columns compose a permutation word at its positions. This is not a
row-label swap, which would compose its digit values instead. -/
theorem factor_swap (M m j w i : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (hi : Γ ⊢[PRAAx] lt i m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.factor (CS M m j) m
      (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) i ≐
        GaussianPolynomialDeterminantTerms.factor M m w (Foundations.RuntimeAdjacentPermutationSwap.tau j i) :=
  (cell_active _ _ _ _ _ (Foundations.RuntimePermutationWords.digit_bound _ _ _ hi) hi hj).eqTrans
    (entry_congr (entry_congr (.eqRefl _)
      (Foundations.RuntimeAdjacentPermutationSwap.swapped_digit _ _ _ _ hj hi)) (.eqRefl _))

theorem scalar_swap (M m L j w z : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.scalarProduct (CS M m j) m L
      (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) z m ≐
        GaussianPolynomialDeterminantTerms.scalarProduct M m L w z m := by
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  have entries : Γ ⊢[PRAAx] GaussianRationalFiniteSum.termsEqual
      GaussianRationalAdjacentProduct.evaluatedFactorBody
      (GaussianRationalAdjacentProduct.swapBody GaussianRationalAdjacentProduct.evaluatedFactorBody) m
      (GaussianRationalAdjacentProduct.factorData (CS M m j) m L (Foundations.RuntimeAdjacentPermutationSwap.swapWord m w j) z)
      (pairT j (GaussianRationalAdjacentProduct.factorData M m L w z)) := by
    refine .allI (.impI ?_)
    have e := (GaussianRationalAdjacentProduct.evaluated_factor_at
        (CS (Syn.shift M) (Syn.shift m) (Syn.shift j)) (Syn.shift m) (Syn.shift L)
        (Foundations.RuntimeAdjacentPermutationSwap.swapWord (Syn.shift m) (Syn.shift w) (Syn.shift j)) (Syn.shift z) (var 0)).eqTrans
      ((GaussianRationalMonicReduction.evaluate_congr
          (factor_swap (Syn.shift M) (Syn.shift m) (Syn.shift j) (Syn.shift w) (var 0) js.wk Prf.hyp0) (.eqRefl _)).eqTrans
        ((GaussianRationalAdjacentProduct.evaluated_factor_at (Syn.shift M) (Syn.shift m) (Syn.shift L)
          (Syn.shift w) (Syn.shift z) (Foundations.RuntimeAdjacentPermutationSwap.tau (Syn.shift j) (var 0))).eqSymm.eqTrans
          (GaussianRationalAdjacentProduct.swap_body_at GaussianRationalAdjacentProduct.evaluatedFactorBody
            (Syn.shift j) (var 0) (GaussianRationalAdjacentProduct.factorData (Syn.shift M) (Syn.shift m)
              (Syn.shift L) (Syn.shift w) (Syn.shift z))).eqSymm))
    simpa only [Syn.shift,subst_CS,Foundations.RuntimeAdjacentPermutationSwap.subst_swapWord,
      GaussianRationalAdjacentProduct.subst_factorData,subst_pairT] using e
  exact (GaussianRationalAdjacentProduct.scalar_product_as_qprod _ _ _ _ _ _).eqTrans
    ((GaussianRationalFiniteProduct.product_congr_bounded _ _ _ _ _ entries).eqTrans
      ((GaussianRationalAdjacentProduct.adjacent_product _ _ _ _ hj).eqTrans
        (GaussianRationalAdjacentProduct.scalar_product_as_qprod _ _ _ _ _ _).eqSymm))

theorem scalar_word_congr (M m L z k : PTm n) {w w' : PTm n} (hw : Γ ⊢[PRAAx] w ≐ w') : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminantTerms.scalarProduct M m L w z k ≐
      GaussianPolynomialDeterminantTerms.scalarProduct M m L w' z k :=
  congrAp2 GaussianPolynomialDeterminantTerms.scalarF (.eqRefl _)
    (congrPairT (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) hw))) (.eqRefl _))

theorem value_term_congr {M M' m m' L L' t t' z z' : PTm n}
    (hM : Γ ⊢[PRAAx] M ≐ M') (hm : Γ ⊢[PRAAx] m ≐ m') (hL : Γ ⊢[PRAAx] L ≐ L')
    (ht : Γ ⊢[PRAAx] t ≐ t') (hz : Γ ⊢[PRAAx] z ≐ z') : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminant.valueTerm M m L t z ≐ GaussianPolynomialDeterminant.valueTerm M' m' L' t' z' := by
  ipra_congr (GaussianPolynomialDeterminant.valueTerm (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [hM, hm, hL, ht, hz]
theorem value_reindexed (M m L j z t : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminant.valueTerm (CS M m j) m L (Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t) z ≐
      qnegative (GaussianPolynomialDeterminant.valueTerm M m L t z) := by
  have word := Prf.andE₂ (Foundations.RuntimeAdjacentPermutationSwap.retained_transport m j t ht hj)
  exact (qmul_congr (GaussianDeterminantSignTransport.sign_congr (.eqRefl _) word)
    ((scalar_word_congr _ _ _ _ _ word).eqTrans (scalar_swap _ _ _ _ _ _ hj))).eqTrans
      (GaussianDeterminantSignTransport.signed_scalar_flip _ _ _ _
        (Foundations.RuntimePermutationWords.retained_valid _ _ ht) hj)

/-! One persistent numerical packet supplies every fixed two-variable
body. No numerical matrix or swap position is captured as external syntax. -/
def pack (M m L j z : PTm n) : PTm n := pairT M (pairT m (pairT L (pairT j z)))
def fields (x : PTm n) : Fin 5 → PTm n := ![fstT x,fstT (sndT x),fstT (sndT (sndT x)),
  fstT (sndT (sndT (sndT x))),sndT (sndT (sndT (sndT x)))]
def rankBody : PTm 2 := Foundations.RuntimeAdjacentPermutationSwap.rankSwap (fields (var 1) 1) (fields (var 1) 3) (var 0)
def oldBody : PTm 2 := GaussianPolynomialDeterminant.valueTerm (fields (var 1) 0)
  (fields (var 1) 1) (fields (var 1) 2) (var 0) (fields (var 1) 4)
def newBody : PTm 2 := GaussianPolynomialDeterminant.valueTerm
  (CS (fields (var 1) 0) (fields (var 1) 1) (fields (var 1) 3))
  (fields (var 1) 1) (fields (var 1) 2) (var 0) (fields (var 1) 4)
@[simp] theorem subst_pack {l : ℕ} (σ : Fin n → PTm l) (M m L j z : PTm n) :
    Syn.subst σ (pack M m L j z) = pack (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ j) (Syn.subst σ z) := by simp [pack]
@[simp] theorem subst_fields {l : ℕ} (σ : Fin n → PTm l) (x : PTm n) (i : Fin 5) :
    Syn.subst σ (fields x i) = fields (Syn.subst σ x) i := by fin_cases i <;> simp [fields]
theorem field_at (M m L j z : PTm n) (i : Fin 5) : Γ ⊢[PRAAx] fields (pack M m L j z) i ≐ ![M,m,L,j,z] i := by
  have e1 := snd_pair (Γ := Γ) M (pairT m (pairT L (pairT j z)))
  have e2 := (congrSnd e1).eqTrans (snd_pair m (pairT L (pairT j z)))
  have e3 := (congrSnd e2).eqTrans (snd_pair L (pairT j z))
  fin_cases i
  · exact fst_pair _ _
  · exact (congrFst e1).eqTrans (fst_pair _ _)
  · exact (congrFst e2).eqTrans (fst_pair _ _)
  · exact (congrFst e3).eqTrans (fst_pair _ _)
  · exact (congrSnd e3).eqTrans (snd_pair _ _)
theorem rank_congr {m m' j j' t t' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ m')
    (hj : Γ ⊢[PRAAx] j ≐ j') (ht : Γ ⊢[PRAAx] t ≐ t') : Γ ⊢[PRAAx]
    Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t ≐ Foundations.RuntimeAdjacentPermutationSwap.rankSwap m' j' t' := by
  ipra_congr (Foundations.RuntimeAdjacentPermutationSwap.rankSwap (var 0) (var 1) (var 2) : PTm 3) with [hm, hj, ht]
theorem rank_body_at (M m L j z t : PTm n) : Γ ⊢[PRAAx]
    inst2 rankBody t (pack M m L j z) ≐ Foundations.RuntimeAdjacentPermutationSwap.rankSwap m j t := by
  simp only [rankBody,inst2,Foundations.RuntimeAdjacentPermutationSwap.subst_rankSwap,subst_fields,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact rank_congr (field_at _ _ _ _ _ 1) (field_at _ _ _ _ _ 3) (.eqRefl _)
theorem old_body_at (M m L j z t : PTm n) : Γ ⊢[PRAAx]
    inst2 oldBody t (pack M m L j z) ≐ GaussianPolynomialDeterminant.valueTerm M m L t z := by
  simp only [oldBody,inst2,GaussianPolynomialDeterminant.subst_valueTerm,subst_fields,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact value_term_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 1) (field_at _ _ _ _ _ 2) (.eqRefl _) (field_at _ _ _ _ _ 4)
theorem new_body_at (M m L j z t : PTm n) : Γ ⊢[PRAAx]
    inst2 newBody t (pack M m L j z) ≐ GaussianPolynomialDeterminant.valueTerm (CS M m j) m L t z := by
  simp only [newBody,inst2,GaussianPolynomialDeterminant.subst_valueTerm,subst_CS,subst_fields,
    Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact value_term_congr (CS_congr (field_at _ _ _ _ _ 0) (field_at _ _ _ _ _ 1) (field_at _ _ _ _ _ 3))
    (field_at _ _ _ _ _ 1) (field_at _ _ _ _ _ 2) (.eqRefl _) (field_at _ _ _ _ _ 4)

theorem rank_range (M m L j z : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianRationalPermutationSum.boundedRange rankBody (Foundations.RuntimePermutationWords.count m) (pack M m L j z) := by
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  have ht : lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (Foundations.RuntimePermutationWords.count (Syn.shift m)) := by
    simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_count] using
      (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m))))
  have e := lt_congr (rank_body_at (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z) (var 0)).eqSymm
    (.eqRefl _) (.andE₁ (Foundations.RuntimeAdjacentPermutationSwap.retained_transport _ _ _ ht js.wk))
  simpa only [Syn.shift,subst_pack,Foundations.RuntimePermutationWords.subst_count] using e
theorem rank_inverse (M m L j z : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianRationalPermutationSum.inverseLaw rankBody rankBody (Foundations.RuntimePermutationWords.count m) (pack M m L j z) := by
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  have ht : lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (Foundations.RuntimePermutationWords.count (Syn.shift m)) := by
    simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_count] using
      (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m))))
  have inner := rank_body_at (Γ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift)
    (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z) (var 0)
  have e := (rank_body_at (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z)
      (inst2 rankBody (var 0) (pack (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z)))).eqTrans
    ((rank_congr (.eqRefl _) (.eqRefl _) inner).eqTrans
      (Foundations.RuntimeAdjacentPermutationSwap.rank_involution _ _ _ ht js.wk))
  simpa only [Syn.shift,subst_pack,Foundations.RuntimePermutationWords.subst_count] using e

theorem mapped_value_negative (M m L j z t : PTm n)
    (ht : Γ ⊢[PRAAx] lt t (Foundations.RuntimePermutationWords.count m))
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    inst2 (GaussianRationalPermutationSum.mappedBody newBody rankBody) t (pack M m L j z) ≐
      inst2 (GaussianRationalMatrixFiniteSums.negativeBody oldBody) t (pack M m L j z) := by
  rw [GaussianRationalPermutationSum.inst2_mappedBody,GaussianRationalMatrixFiniteSums.negative_body_at]
  exact (new_body_at _ _ _ _ _ _).eqTrans
    ((value_term_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (rank_body_at _ _ _ _ _ _) (.eqRefl _)).eqTrans
      ((value_reindexed _ _ _ _ _ _ ht hj).eqTrans
        (GaussianInverseBinomialRows.negative_congr (old_body_at _ _ _ _ _ _)).eqSymm))
theorem mapped_terms_negative (M m L j z : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.termsEqual (GaussianRationalPermutationSum.mappedBody newBody rankBody)
      (GaussianRationalMatrixFiniteSums.negativeBody oldBody) (Foundations.RuntimePermutationWords.count m)
      (pack M m L j z) (pack M m L j z) := by
  have js : Γ.map Fm.shift ⊢[PRAAx] lt (succ (Syn.shift j)) (Syn.shift m) := by
    simpa only [Fm.shift,subst_lt,ConciseIPRA.PTm.subst_succ,Syn.shift] using hj.shift
  refine .allI (.impI ?_)
  have ht : lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m)) :: Γ.map Fm.shift ⊢[PRAAx]
      lt (var 0) (Foundations.RuntimePermutationWords.count (Syn.shift m)) := by
    simpa only [Syn.shift,Foundations.RuntimePermutationWords.subst_count] using
      (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (Syn.shift (Foundations.RuntimePermutationWords.count m))))
  simpa only [Syn.shift,subst_pack,Foundations.RuntimePermutationWords.subst_count] using
    mapped_value_negative (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z) (var 0) ht js.wk
theorem old_sum (M m L j z k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum oldBody k (pack M m L j z) ≐ GaussianPolynomialDeterminant.valueSum M m L k z := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have e := (old_body_at (Γ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift)
      (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z) (var 0)).eqTrans
    (GaussianPolynomialDeterminant.value_body_at (Syn.shift M) (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift z)).eqSymm
  simpa only [Syn.shift,subst_pack,GaussianPolynomialDeterminantTerms.subst_data] using e
theorem new_sum (M m L j z k : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalFiniteSum.sum newBody k (pack M m L j z) ≐ GaussianPolynomialDeterminant.valueSum (CS M m j) m L k z := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have e := (new_body_at (Γ := lt (var 0) (Syn.shift k) :: Γ.map Fm.shift)
      (Syn.shift M) (Syn.shift m) (Syn.shift L) (Syn.shift j) (Syn.shift z) (var 0)).eqTrans
    (GaussianPolynomialDeterminant.value_body_at (CS (Syn.shift M) (Syn.shift m) (Syn.shift j))
      (Syn.shift m) (Syn.shift L) (var 0) (Syn.shift z)).eqSymm
  simpa only [Syn.shift,subst_pack,subst_CS,GaussianPolynomialDeterminantTerms.subst_data] using e

/-- The exact retained-rank involution reindexes the SAME finite field
sum. Its local range and inverse contracts are derived above. -/
theorem value_sum_negative (M m L j z : PTm n) (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    GaussianPolynomialDeterminant.valueSum (CS M m j) m L (Foundations.RuntimePermutationWords.count m) z ≐
      qnegative (GaussianPolynomialDeterminant.valueSum M m L (Foundations.RuntimePermutationWords.count m) z) :=
  (new_sum _ _ _ _ _ _).eqSymm.eqTrans
    ((GaussianRationalPermutationSum.involution_sum newBody rankBody _ _ (rank_range _ _ _ _ _ hj)
      (rank_inverse _ _ _ _ _ hj)).eqSymm.eqTrans
        ((GaussianRationalFiniteSum.sum_congr_bounded _ _ _ _ _ (mapped_terms_negative _ _ _ _ _ hj)).eqTrans
          ((GaussianRationalMatrixFiniteSums.sum_negative oldBody _ _).eqTrans
            (GaussianInverseBinomialRows.negative_congr (old_sum _ _ _ _ _ _)))))

theorem column_evaluation_neg (M m L j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant (CS M m j) m L) z ≐
      qnegative (evaluate (GaussianPolynomialDeterminant.determinant M m L) z) :=
  (GaussianPolynomialDeterminant.evaluation_leibniz _ _ _ _ (CS_shape _ _ _ _ h)).eqTrans
    ((value_sum_negative _ _ _ _ _ hj).eqTrans
      (GaussianInverseBinomialRows.negative_congr (GaussianPolynomialDeterminant.evaluation_leibniz _ _ _ _ h)).eqSymm)
theorem column_evaluation_cancel (M m L j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    qadd (evaluate (GaussianPolynomialDeterminant.determinant (CS M m j) m L) z)
      (evaluate (GaussianPolynomialDeterminant.determinant M m L) z) ≐ qzero :=
  (qadd_congr (column_evaluation_neg _ _ _ _ _ h hj) (.eqRefl _)).eqTrans
    ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self _))

theorem empty_evaluation (M L j z : PTm n) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant (CS M zero j) zero L) z ≐ GaussianRationalSyntheticDivision.qone :=
  GaussianPolynomialDeterminant.empty_evaluation _ _ _
theorem singleton_evaluation (M L j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M one L) : Γ ⊢[PRAAx]
    evaluate (GaussianPolynomialDeterminant.determinant (CS M one j) one L) z ≐ evaluate (cell M zero zero) z :=
  (GaussianPolynomialDeterminant.singleton_evaluation _ _ _ (CS_shape _ _ _ _ h)).eqTrans
    (GaussianRationalMonicReduction.evaluate_congr (cell_inactive _ _ _ _ _ (le_refl one)
      (le_of_eq_add (d := j) (by ipra_ring))) (.eqRefl _))

/-- The two determinant payloads are the SAME original determinant PR3,
with their actual stored polynomials, word lists and counts preserved. -/
def output (M m L j : PTm n) : PTm n := pairT (CS M m j)
  (pairT (GaussianPolynomialDeterminant.run M m L) (GaussianPolynomialDeterminant.run (CS M m j) m L))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (M m L j : PTm n) : PTm n := app outputF ![M,m,L,j]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (M m L j : PTm n) :
    Syn.subst σ (output M m L j) = output (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ j) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (M m L j : PTm n) :
    Syn.subst σ (run M m L j) = run (Syn.subst σ M) (Syn.subst σ m) (Syn.subst σ L) (Syn.subst σ j) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl
theorem program_at (M m L j : PTm n) : Γ ⊢[PRAAx] run M m L j ≐ output M m L j := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3)) ![M,m,L,j]
theorem returned_table (M m L j : PTm n) : Γ ⊢[PRAAx] fstT (run M m L j) ≐ CS M m j :=
  (congrFst (program_at _ _ _ _)).eqTrans (fst_pair _ _)
theorem returned_original (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run M m L j)) ≐ GaussianPolynomialDeterminant.run M m L :=
  (congrFst ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_swapped (M m L j : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (run M m L j)) ≐ GaussianPolynomialDeterminant.run (CS M m j) m L :=
  (congrSnd ((congrSnd (program_at _ _ _ _)).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)
theorem returned_original_polynomial (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (fstT (sndT (run M m L j))) ≐ GaussianPolynomialDeterminant.determinant M m L :=
  (congrFst (returned_original _ _ _ _)).eqTrans (GaussianPolynomialDeterminant.returned_polynomial _ _ _)
theorem returned_swapped_polynomial (M m L j : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run M m L j))) ≐ GaussianPolynomialDeterminant.determinant (CS M m j) m L :=
  (congrFst (returned_swapped _ _ _ _)).eqTrans (GaussianPolynomialDeterminant.returned_polynomial _ _ _)
theorem returned_shape (M m L j : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L) : Γ ⊢[PRAAx]
    tableShape (fstT (run M m L j)) m L :=
  GaussianRationalFiberVandermonde.table_shape_congr (returned_table _ _ _ _).eqSymm (CS_shape _ _ _ _ h)
theorem returned_evaluation_neg (M m L j z : PTm n) (h : Γ ⊢[PRAAx] tableShape M m L)
    (hj : Γ ⊢[PRAAx] lt (succ j) m) : Γ ⊢[PRAAx]
    evaluate (fstT (sndT (sndT (run M m L j)))) z ≐ qnegative (evaluate (fstT (fstT (sndT (run M m L j)))) z) :=
  (GaussianRationalMonicReduction.evaluate_congr (returned_swapped_polynomial _ _ _ _) (.eqRefl _)).eqTrans
    ((column_evaluation_neg _ _ _ _ _ h hj).eqTrans
      (GaussianInverseBinomialRows.negative_congr
        (GaussianRationalMonicReduction.evaluate_congr (returned_original_polynomial _ _ _ _) (.eqRefl _))).eqSymm)

/-! Dimensions, original codes, swap position and query remain bound
inside the ordinary PRA statements. No externally fixed size is used. -/
theorem actual_column_table_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) (var 1) (var 2) ⟶ tableShape (CS (var 0) (var 1) (var 3)) (var 1) (var 2)) :=
  closeUniv 4 (.impI (CS_shape _ _ _ _ Prf.hyp0))
theorem actual_column_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (var 1) ⟶ lt (var 4) (var 1) ⟶ lt (succ (var 2)) (var 1) ⟶
      cell (CS (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
        cell (var 0) (var 3) (Foundations.RuntimeAdjacentPermutationSwap.tau (var 2) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (cell_active _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_scalar_product_swap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (succ (var 3)) (var 1) ⟶
      GaussianPolynomialDeterminantTerms.scalarProduct (CS (var 0) (var 1) (var 3)) (var 1) (var 2)
        (Foundations.RuntimeAdjacentPermutationSwap.swapWord (var 1) (var 4) (var 3)) (var 5) (var 1) ≐
      GaussianPolynomialDeterminantTerms.scalarProduct (var 0) (var 1) (var 2) (var 4) (var 5) (var 1)) :=
  closeUniv 6 (.impI (scalar_swap _ _ _ _ _ _ Prf.hyp0))
theorem actual_rank_reindex_contract_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (succ (var 3)) (var 1) ⟶
      (GaussianRationalPermutationSum.boundedRange rankBody (Foundations.RuntimePermutationWords.count (var 1))
        (pack (var 0) (var 1) (var 2) (var 3) (var 4)) ⋏
      GaussianRationalPermutationSum.inverseLaw rankBody rankBody (Foundations.RuntimePermutationWords.count (var 1))
        (pack (var 0) (var 1) (var 2) (var 3) (var 4)))) :=
  closeUniv 5 (.impI (.andI (rank_range _ _ _ _ _ Prf.hyp0) (rank_inverse _ _ _ _ _ Prf.hyp0)))
theorem actual_column_evaluation_neg_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶
      evaluate (GaussianPolynomialDeterminant.determinant (CS (var 0) (var 1) (var 3)) (var 1) (var 2)) (var 4) ≐
        qnegative (evaluate (GaussianPolynomialDeterminant.determinant (var 0) (var 1) (var 2)) (var 4))) :=
  closeUniv 5 (.impI (.impI (column_evaluation_neg _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_column_evaluation_cancel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶
      qadd (evaluate (GaussianPolynomialDeterminant.determinant (CS (var 0) (var 1) (var 3)) (var 1) (var 2)) (var 4))
        (evaluate (GaussianPolynomialDeterminant.determinant (var 0) (var 1) (var 2)) (var 4)) ≐ qzero) :=
  closeUniv 5 (.impI (.impI (column_evaluation_cancel _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem empty_column_table_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (evaluate (GaussianPolynomialDeterminant.determinant (CS (var 0) zero (var 2)) zero (var 1)) (var 3) ≐ GaussianRationalSyntheticDivision.qone) :=
  closeUniv 4 (empty_evaluation _ _ _ _)
theorem singleton_column_table_evaluation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (tableShape (var 0) one (var 1) ⟶
      evaluate (GaussianPolynomialDeterminant.determinant (CS (var 0) one (var 2)) one (var 1)) (var 3) ≐ evaluate (cell (var 0) zero zero) (var 3)) :=
  closeUniv 4 (.impI (singleton_evaluation _ _ _ _ Prf.hyp0))
theorem actual_column_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem returned_column_alternation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (tableShape (var 0) (var 1) (var 2) ⟶ lt (succ (var 3)) (var 1) ⟶
      evaluate (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3))))) (var 4) ≐
        qnegative (evaluate (fstT (fstT (sndT (run (var 0) (var 1) (var 2) (var 3))))) (var 4))) :=
  closeUniv 5 (.impI (.impI (returned_evaluation_neg _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialColumnAlternation

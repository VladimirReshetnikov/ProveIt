import IPRADerivations.Analysis.RationalCofactorBorderedRows
import IPRADerivations.Analysis.RationalCofactorColumnOrder
import IPRADerivations.Analysis.RationalCofactorSupport

/-!
# The actual bordered Laplace minors are the original cofactor minors

Deleting a supported numerical column from the bordered table retains the
original selected rows and the exact ordered cofactor columns. Bounded cell
comparisons derive determinant equality with the embedded original rational
minor. The final-row entry reads the SAME cleared original coordinate.
No determinant, cofactor-sum or annihilation identity is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorBorderedMinors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ app)
open RationalMaximalMinors (bestRow rank)
open RationalSelectedMinors (count normalized normalized_lookup)
open RationalMinorAugmentation (extendedColumn extended_column_size)
open RationalCofactorMinorBounds (columnMask minorValue cofactor_size)
open RationalCofactorColumnOrder (cofactor_cell)
open RationalCofactorSupport (supportedColumn supported_label)
open RationalCofactorBorderedRows (bordered bordered_old bordered_last clearedCell)
open RationalRowSpanGaussianEmbedding (matrix matrix_lookup)
open RationalScalarDeterminantGaussianEmbedding (determinant_embedding)
open RationalGaussianEmbedding (embed)
open RationalPolynomialGaussianEmbedding (embed_congr)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianScalarDeterminantLastRowProduct (minorTable minor_lookup)
open GaussianScalarDeterminant (scalarDet scalarCellsEqual scalar_det_congr)
open GaussianScalarColumnSelection (cell_congr)
open GaussianRationalValueEquality (value_equal_of_code)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (slot slot_bound)
open LeanProofs.IPRA.Foundations.RuntimePermutationInsertion (slot_congr)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open RationalSupMetric (coordinate normalizedList)
open RationalIntegerNormalization (normalize)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def laplaceMinor (P d i r : PTm n) : PTm n := minorTable (bordered P d i) (rank P d) r
def rationalMinor (P d r : PTm n) : PTm n := normalized P d (bestRow P d) (columnMask P d (supportedColumn P d r))
def embeddedMinor (P d r : PTm n) : PTm n := matrix (rationalMinor P d r) (rank P d) (rank P d)

@[simp] theorem subst_laplaceMinor {k : ℕ} (σ : Fin n → PTm k) (P d i r : PTm n) :
    Syn.subst σ (laplaceMinor P d i r) = laplaceMinor (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ r) := by simp [laplaceMinor]
@[simp] theorem subst_rationalMinor {k : ℕ} (σ : Fin n → PTm k) (P d r : PTm n) :
    Syn.subst σ (rationalMinor P d r) = rationalMinor (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ r) := by simp [rationalMinor]
@[simp] theorem subst_embeddedMinor {k : ℕ} (σ : Fin n → PTm k) (P d r : PTm n) :
    Syn.subst σ (embeddedMinor P d r) = embeddedMinor (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ r) := by simp [embeddedMinor]

theorem supported_spec (P d r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) : Γ ⊢[PRAAx]
    lt (supportedColumn P d r) d ⋏ (RationalSubtupleSpan.bit (extendedColumn P d) (supportedColumn P d r) ≐ one ⋏
      count (supportedColumn P d r) (extendedColumn P d) ≐ r) :=
  supported_label P d r (lt_congr (.eqRefl _) (extended_column_size P d h).eqSymm hr)

/-- Literal equality of the actual scalar cells, stronger than field equality.
The appended original row i disappears from both minors. -/
theorem minor_cell (P d i r a b : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d)))
    (ha : Γ ⊢[PRAAx] lt a (rank P d)) (hb : Γ ⊢[PRAAx] lt b (rank P d)) : Γ ⊢[PRAAx]
    cell (laplaceMinor P d i r) a b ≐ cell (embeddedMinor P d r) a b := by
  let j := supportedColumn P d r
  have label := supported_spec P d r h hr
  have size := cofactor_size P d j h label.andE₁ label.andE₂.andE₁
  have smallColumn : Γ ⊢[PRAAx] lt b (count d (columnMask P d j)) := lt_congr (.eqRefl _) size.eqSymm hb
  have slotSmall := slot_bound (rank P d) r b hb
  have slotInColumns := lt_congr (.eqRefl _) (extended_column_size P d h).eqSymm slotSmall
  have positions := slot_congr label.andE₂.andE₂ (.eqRefl b)
  have cofactor := (cofactor_cell P d j a b h label.andE₁ label.andE₂.andE₁ ha smallColumn).eqTrans
    ((cell_congr (.eqRefl _) (.eqRefl a) positions).eqTrans
      (normalized_lookup P d (bestRow P d) (extendedColumn P d) a (slot r b) ha slotInColumns))
  have right := (matrix_lookup (rationalMinor P d r) (rank P d) (rank P d) a b ha hb).eqTrans (embed_congr cofactor)
  have left := (minor_lookup (bordered P d i) (rank P d) r a b ha hb).eqTrans (bordered_old P d i a (slot r b) ha slotSmall)
  exact left.eqTrans right.eqSymm

theorem minor_cells (P d i r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) :
    Γ ⊢[PRAAx] scalarCellsEqual (laplaceMinor P d i r) (embeddedMinor P d r) (rank P d) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let a := Syn.shift (Syn.shift P)
  let b := Syn.shift (Syn.shift d)
  let c := Syn.shift (Syn.shift i)
  let s := Syn.shift (Syn.shift r)
  let Δ := lt (var 0) (rank a b) :: lt (var 1) (rank a b) :: (Γ.map Fm.shift).map Fm.shift
  have hh : Δ ⊢[PRAAx] lt (rank a b) b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  have rh : Δ ⊢[PRAAx] lt s (succ (rank a b)) := by simpa [Δ,a,b,s,Fm.shift,Syn.shift] using hr.shift.shift.wk.wk
  have values := value_equal_of_code (minor_cell a b c s (var 1) (var 0) hh rh Prf.hyp1 Prf.hyp0)
  simpa [Δ,a,b,c,s,GaussianScalarDeterminant.scalarRowEqual,scalarCellsEqual,Fm.shift,Syn.shift] using values

/-- The exact scalar Laplace minor is the actual embedded original rational
cofactor determinant, at the selected source column. -/
theorem minor_determinant (P d i r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) : Γ ⊢[PRAAx]
    scalarDet (minorTable (bordered P d i) (rank P d) r) (rank P d) ≐ embed (minorValue P d (supportedColumn P d r)) :=
  (scalar_det_congr _ _ _ (minor_cells P d i r h hr)).eqTrans (determinant_embedding (rationalMinor P d r) (rank P d)).eqSymm

/-- Original cleared last-row entry at the SAME supported source column.
No bound on i is needed for this literal producer identity. -/
theorem last_supported_cell (P d i r : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (bordered P d i) (rank P d) r ≐
      embed (normalize (coordinate (entry (normalizedList P d) i) (supportedColumn P d r)) one) :=
  bordered_last P d i r hr

theorem minor_length (P d i r : PTm n) : Γ ⊢[PRAAx] Foundations.SequenceComposition.length (laplaceMinor P d i r) ≐ rank P d :=
  GaussianRationalFiberVandermonde.table_length _ _ _ _
theorem minor_row_length (P d i r a : PTm n) (ha : Γ ⊢[PRAAx] lt a (rank P d)) : Γ ⊢[PRAAx]
    Foundations.SequenceComposition.length (entry (laplaceMinor P d i r) a) ≐ rank P d :=
  GaussianRationalFiberVandermonde.table_row_length _ _ _ _ _ ha
theorem minor_shape (P d i r : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (laplaceMinor P d i r) (rank P d) := by
  refine .andI (minor_length _ _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_laplaceMinor,RationalMaximalMinors.subst_rank] using
    minor_row_length (Syn.shift P) (Syn.shift d) (Syn.shift i) (Syn.shift r) (var 0) Prf.hyp0

def cofactorValue (P d r : PTm n) : PTm n := embed (minorValue P d (supportedColumn P d r))
def lastValue (P d i r : PTm n) : PTm n := clearedCell P d i (supportedColumn P d r)
def output (P d i r : PTm n) : PTm n := pairT (laplaceMinor P d i r)
  (pairT (scalarDet (laplaceMinor P d i r) (rank P d)) (pairT (cofactorValue P d r) (lastValue P d i r)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (P d i r : PTm n) : PTm n := app outputF ![P,d,i,r]
@[simp] theorem subst_cofactorValue {k : ℕ} (σ : Fin n → PTm k) (P d r : PTm n) :
    Syn.subst σ (cofactorValue P d r) = cofactorValue (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ r) := by simp [cofactorValue,minorValue]
@[simp] theorem subst_lastValue {k : ℕ} (σ : Fin n → PTm k) (P d i r : PTm n) :
    Syn.subst σ (lastValue P d i r) = lastValue (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ r) := by simp [lastValue]
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (P d i r : PTm n) :
    Syn.subst σ (output P d i r) = output (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ r) := by simp [output]
theorem program_at (P d i r : PTm n) : Γ ⊢[PRAAx] run P d i r ≐ output P d i r := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![P,d,i,r]
theorem returned_table (P d i r : PTm n) : Γ ⊢[PRAAx] fstT (run P d i r) ≐ laplaceMinor P d i r :=
  (congrFst (program_at P d i r)).eqTrans (fst_pair _ _)
theorem returned_tail (P d i r : PTm n) : Γ ⊢[PRAAx] sndT (run P d i r) ≐
    pairT (scalarDet (laplaceMinor P d i r) (rank P d)) (pairT (cofactorValue P d r) (lastValue P d i r)) :=
  (congrSnd (program_at P d i r)).eqTrans (snd_pair _ _)
theorem returned_determinant (P d i r : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run P d i r)) ≐ scalarDet (laplaceMinor P d i r) (rank P d) :=
  (congrFst (returned_tail P d i r)).eqTrans (fst_pair _ _)
theorem returned_source (P d i r : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run P d i r)) ≐ pairT (cofactorValue P d r) (lastValue P d i r) :=
  (congrSnd (returned_tail P d i r)).eqTrans (snd_pair _ _)
theorem returned_cofactor (P d i r : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run P d i r))) ≐ cofactorValue P d r :=
  (congrFst (returned_source P d i r)).eqTrans (fst_pair _ _)
theorem returned_last (P d i r : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run P d i r))) ≐ lastValue P d i r :=
  (congrSnd (returned_source P d i r)).eqTrans (snd_pair _ _)
theorem returned_minor_value (P d i r : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) : Γ ⊢[PRAAx]
    fstT (sndT (run P d i r)) ≐ embed (minorValue P d (supportedColumn P d r)) :=
  (returned_determinant P d i r).eqTrans (minor_determinant P d i r h hr)

theorem actual_bordered_minor_cells_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 3) (succ (rank (var 0) (var 1))) ⟶
      lt (var 4) (rank (var 0) (var 1)) ⟶ lt (var 5) (rank (var 0) (var 1)) ⟶
        cell (laplaceMinor (var 0) (var 1) (var 2) (var 3)) (var 4) (var 5) ≐
          cell (embeddedMinor (var 0) (var 1) (var 3)) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (minor_cell _ _ _ _ _ _ (.hyp (by simp)) (.hyp (by simp)) Prf.hyp1 Prf.hyp0)))))
theorem actual_bordered_minor_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 3) (succ (rank (var 0) (var 1))) ⟶
      scalarDet (minorTable (bordered (var 0) (var 1) (var 2)) (rank (var 0) (var 1)) (var 3)) (rank (var 0) (var 1)) ≐
        embed (minorValue (var 0) (var 1) (supportedColumn (var 0) (var 1) (var 3)))) :=
  closeUniv 4 (.impI (.impI (minor_determinant _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_bordered_supported_last_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (succ (rank (var 0) (var 1))) ⟶ cell (bordered (var 0) (var 1) (var 2)) (rank (var 0) (var 1)) (var 3) ≐
      embed (normalize (coordinate (entry (normalizedList (var 0) (var 1)) (var 2)) (supportedColumn (var 0) (var 1) (var 3))) one)) :=
  closeUniv 4 (.impI (last_supported_cell _ _ _ _ Prf.hyp0))
theorem actual_bordered_minor_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalMatrixFiniteSums.squareShape (laplaceMinor (var 0) (var 1) (var 2) (var 3)) (rank (var 0) (var 1))) :=
  closeUniv 4 (minor_shape _ _ _ _)
theorem actual_bordered_minors_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_bordered_minor_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 3) (succ (rank (var 0) (var 1))) ⟶
      fstT (sndT (run (var 0) (var 1) (var 2) (var 3))) ≐ embed (minorValue (var 0) (var 1) (supportedColumn (var 0) (var 1) (var 3)))) :=
  closeUniv 4 (.impI (.impI (returned_minor_value _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCofactorBorderedMinors

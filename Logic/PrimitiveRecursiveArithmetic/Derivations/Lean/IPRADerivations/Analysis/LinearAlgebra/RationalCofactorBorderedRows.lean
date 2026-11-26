import IPRADerivations.Analysis.RationalArithmetic.RationalMinorOrderTransport
import IPRADerivations.Analysis.LinearAlgebra.GaussianScalarDeterminantLastRowTransport
import IPRADerivations.Core.CongruenceTactic

/-!
# Actual bordered rows at the selected maximum minor

The table retains the chosen rows on the enlarged column mask, then appends
one original globally cleared row. An unselected row gives the actual moved
augmented minor. A selected row repeats its actual retained position. Both
cases derive zero determinant; no cofactor sum or annihilation law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCofactorBorderedRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (succ)
open RationalMaximalMinors (bestRow bestColumn rank rowSize columnSize clearedValue)
open RationalSelectedMinors (count index normalized fromInteger from_integer_congr normalized_lookup selected_listed)
open RationalMinorAugmentation (extendedRow extendedColumn extended_row_size extended_column_size extended_row_position extended_minor_zero)
open RationalMinorOrderTransport (original_row_slot)
open RationalSubtupleSpan (bit)
open RationalSupMetric (normalizedList)
open RationalGaussianEmbedding (embed embed_canonical)
open RationalPolynomialGaussianEmbedding (embed_congr)
open RationalRowSpanGaussianEmbedding (matrix matrix_lookup)
open RationalScalarDeterminantGaussianEmbedding (determinant determinantF determinant_at determinant_embedding)
open GaussianScalarDeterminant (scalarDet scalarCellsEqual scalar_det_congr)
open GaussianScalarDeterminantLastRowTransport
  (moveToLast moved_last_lookup moved_other_lookup moved_determinant_zero repeatedLastRow repeated_last_determinant)
open GaussianRationalFiberVandermonde (table table_lookup table_length table_row_length)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianScalarColumnSelection (cell_congr)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq)
open GaussianRationalHorner (qzero)
open GaussianRationalValueEquality (valueEqual value_equal_of_code)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- SAME denominator-cleared original coordinate, embedded as a field value. -/
def clearedCell (P d r j : PTm n) : PTm n := embed (fromInteger (cell (normalizedList P d) r j))
def rowLabel (P d i r : PTm n) : PTm n := sel (eqb r (rank P d)) i (index (length P) (bestRow P d) r)
def value (P d i r j : PTm n) : PTm n := clearedCell P d (rowLabel P d i r) (index d (extendedColumn P d) j)
def data (P d i : PTm n) : PTm n := pairT P (pairT d i)
def body : PTm 3 := value (fstT (var 2)) (fstT (sndT (var 2))) (sndT (sndT (var 2))) (var 0) (var 1)
def bordered (P d i : PTm n) : PTm n := table body (succ (rank P d)) (succ (rank P d)) (data P d i)
def augmented (P d i : PTm n) : PTm n := matrix (normalized P d (extendedRow P d i) (extendedColumn P d)) (succ (rank P d)) (succ (rank P d))
def insertionPosition (P d i : PTm n) : PTm n := count i (bestRow P d)

@[simp] theorem subst_clearedCell {k : ℕ} (σ : Fin n → PTm k) (P d r j : PTm n) :
    Syn.subst σ (clearedCell P d r j) = clearedCell (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ r) (Syn.subst σ j) := by simp [clearedCell]
@[simp] theorem subst_rowLabel {k : ℕ} (σ : Fin n → PTm k) (P d i r : PTm n) :
    Syn.subst σ (rowLabel P d i r) = rowLabel (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ r) := by simp [rowLabel,sel]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (P d i r j : PTm n) :
    Syn.subst σ (value P d i r j) = value (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) (Syn.subst σ r) (Syn.subst σ j) := by simp [value]
@[simp] theorem subst_data {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (data P d i) = data (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by simp [data]
@[simp] theorem subst_bordered {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (bordered P d i) = bordered (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by simp [bordered]
@[simp] theorem subst_augmented {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (augmented P d i) = augmented (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by simp [augmented]
@[simp] theorem subst_insertionPosition {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (insertionPosition P d i) = insertionPosition (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by simp [insertionPosition]

theorem cleared_cell_congr (P d : PTm n) {r s j k : PTm n} (hr : Γ ⊢[PRAAx] r ≐ s) (hj : Γ ⊢[PRAAx] j ≐ k) :
    Γ ⊢[PRAAx] clearedCell P d r j ≐ clearedCell P d s k := embed_congr (from_integer_congr (cell_congr (.eqRefl _) hr hj))
theorem cleared_cell_canonical (P d r j : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (clearedCell P d r j) := embed_canonical _
theorem value_congr {P Q d e i k r s j l : PTm n} (hP : Γ ⊢[PRAAx] P ≐ Q) (hd : Γ ⊢[PRAAx] d ≐ e)
    (hi : Γ ⊢[PRAAx] i ≐ k) (hr : Γ ⊢[PRAAx] r ≐ s) (hj : Γ ⊢[PRAAx] j ≐ l) : Γ ⊢[PRAAx] value P d i r j ≐ value Q e k s l := by
  ipra_congr (value (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with [hP, hd, hi, hr, hj]
theorem body_at (P d i r j : PTm n) : Γ ⊢[PRAAx] Syn.subst ![r,j,data P d i] body ≐ value P d i r j := by
  simp only [body,subst_value,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  exact value_congr (fst_pair _ _) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _))
    ((congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)) (.eqRefl _) (.eqRefl _)
theorem bordered_lookup (P d i r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) :
    Γ ⊢[PRAAx] cell (bordered P d i) r j ≐ value P d i r j :=
  (table_lookup body _ _ _ r j hr hj).eqTrans (body_at P d i r j)
theorem row_label_last (P d i : PTm n) : Γ ⊢[PRAAx] rowLabel P d i (rank P d) ≐ i := sel_one (eqb_of_eq (.eqRefl _))
theorem row_label_old (P d i r : PTm n) (hr : Γ ⊢[PRAAx] lt r (rank P d)) : Γ ⊢[PRAAx]
    rowLabel P d i r ≐ index (length P) (bestRow P d) r := sel_zero (eqb_of_ne (Foundations.RuntimeAdjacentPermutationSwap.different_of_lt hr))
theorem bordered_last (P d i j : PTm n) (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (bordered P d i) (rank P d) j ≐ clearedCell P d i (index d (extendedColumn P d) j) :=
  (bordered_lookup P d i (rank P d) j (le_refl _) hj).eqTrans (cleared_cell_congr P d (row_label_last P d i) (.eqRefl _))
theorem bordered_old (P d i r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (rank P d)) (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (bordered P d i) r j ≐ clearedCell P d (index (length P) (bestRow P d) r) (index d (extendedColumn P d) j) :=
  (bordered_lookup P d i r j (lt_of_lt_of_le hr (le_succ_self _)) hj).eqTrans (cleared_cell_congr P d (row_label_old P d i r hr) (.eqRefl _))

theorem augmented_lookup (P d i r j : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d)))
    (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (augmented P d i) r j ≐ clearedCell P d (index (length P) (extendedRow P d i) r) (index d (extendedColumn P d) j) :=
  (matrix_lookup _ _ _ _ _ hr hj).eqTrans (embed_congr (normalized_lookup P d (extendedRow P d i) (extendedColumn P d) r j
    (lt_congr (.eqRefl _) (extended_row_size P d i hi hb).eqSymm hr) (lt_congr (.eqRefl _) (extended_column_size P d h).eqSymm hj)))

theorem augmented_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) : Γ ⊢[PRAAx] scalarDet (augmented P d i) (succ (rank P d)) ≐ qzero := by
  let A := normalized P d (extendedRow P d i) (extendedColumn P d)
  have sizes := extended_row_size P d i hi hb
  have dimension : Γ ⊢[PRAAx] determinant A (succ (rank P d)) ≐ determinant A (rowSize P (extendedRow P d i)) :=
    (determinant_at A _).eqSymm.eqTrans ((congrAp2 determinantF (.eqRefl _) sizes.eqSymm).eqTrans (determinant_at A _))
  exact (determinant_embedding A (succ (rank P d))).eqSymm.eqTrans
    ((embed_congr dimension).eqTrans (extended_minor_zero P d i h hi hb))

def moved (P d i : PTm n) : PTm n := moveToLast (augmented P d i) (rank P d) (insertionPosition P d i)
@[simp] theorem subst_moved {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (moved P d i) = moved (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by simp [moved]

theorem insertion_position_bound (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) : Γ ⊢[PRAAx] lt (insertionPosition P d i) (succ (rank P d)) :=
  lt_congr (.eqRefl _) (extended_row_size P d i hi hb) (extended_row_position P d i hi).andE₁

theorem moved_last_read (P d i j : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (moved P d i) (rank P d) j ≐ clearedCell P d i (index d (extendedColumn P d) j) := by
  have pos := insertion_position_bound P d i hi hb
  have read := (augmented_lookup P d i (insertionPosition P d i) j h hi hb pos hj).eqTrans
    (cleared_cell_congr P d (extended_row_position P d i hi).andE₂ (.eqRefl _))
  exact (moved_last_lookup (augmented P d i) (rank P d) (insertionPosition P d i) j pos hj).eqTrans
    ((recode_congr read).eqTrans (recode_eq _ (cleared_cell_canonical _ _ _ _)))

theorem moved_old_read (P d i r j : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) (hr : Γ ⊢[PRAAx] lt r (rank P d))
    (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (moved P d i) r j ≐ clearedCell P d (index (length P) (bestRow P d) r) (index d (extendedColumn P d) j) := by
  have pos := insertion_position_bound P d i hi hb
  have kept := original_row_slot P d i r hr hb
  have slotBound := lt_congr (.eqRefl _) (extended_row_size P d i hi hb) kept.andE₁
  have read := (augmented_lookup P d i (Foundations.RuntimePermutationDeletion.slot (insertionPosition P d i) r) j h hi hb slotBound hj).eqTrans
    (cleared_cell_congr P d kept.andE₂ (.eqRefl _))
  exact (moved_other_lookup (augmented P d i) (rank P d) (insertionPosition P d i) r j pos hr hj).eqTrans
    ((recode_congr read).eqTrans (recode_eq _ (cleared_cell_canonical _ _ _ _)))

theorem outside_cell_equal (P d i r j : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d)))
    (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx] cell (bordered P d i) r j ≐ cell (moved P d i) r j := by
  have rm : Γ ⊢[PRAAx] le r (rank P d) := (succ_monus_succ r (rank P d)).eqSymm.eqTrans hr
  refine .orE (lt_or_eq_of_le rm) ?_ ?_
  · exact (bordered_old P d i r j Prf.hyp0 hj.wk).eqTrans (moved_old_read P d i r j h.wk hi.wk hb.wk Prf.hyp0 hj.wk).eqSymm
  · exact (cell_congr (.eqRefl _) Prf.hyp0 (.eqRefl _)).eqTrans
      ((bordered_last P d i j hj.wk).eqTrans ((moved_last_read P d i j h.wk hi.wk hb.wk hj.wk).eqSymm.eqTrans
        (cell_congr (.eqRefl _) Prf.hyp0.eqSymm (.eqRefl _))))

theorem outside_cells (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) : Γ ⊢[PRAAx]
    scalarCellsEqual (bordered P d i) (moved P d i) (succ (rank P d)) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let a := Syn.shift (Syn.shift P)
  let b := Syn.shift (Syn.shift d)
  let c := Syn.shift (Syn.shift i)
  let Δ := lt (var 0) (succ (rank a b)) :: lt (var 1) (succ (rank a b)) :: (Γ.map Fm.shift).map Fm.shift
  have hh : Δ ⊢[PRAAx] lt (rank a b) b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using h.shift.shift.wk.wk
  have ih : Δ ⊢[PRAAx] lt c (length a) := by simpa [Δ,a,c,Fm.shift,Syn.shift] using hi.shift.shift.wk.wk
  have bh : Δ ⊢[PRAAx] bit (bestRow a b) c ≐ ConciseIPRA.PTm.zero := by simpa [Δ,a,b,c,Fm.shift,Syn.shift] using hb.shift.shift.wk.wk
  have values := value_equal_of_code (outside_cell_equal a b c (var 1) (var 0) hh ih bh Prf.hyp1 Prf.hyp0)
  simpa [Δ,a,b,c,GaussianScalarDeterminant.scalarRowEqual,scalarCellsEqual,Fm.shift,Syn.shift] using values

theorem outside_determinant_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero) : Γ ⊢[PRAAx]
    scalarDet (bordered P d i) (succ (rank P d)) ≐ qzero :=
  (scalar_det_congr _ _ _ (outside_cells P d i h hi hb)).eqTrans
    (moved_determinant_zero _ _ _ (augmented_zero P d i h hi hb))

theorem retained_position (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] neg (bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero)) : Γ ⊢[PRAAx]
    lt (insertionPosition P d i) (rank P d) ⋏ index (length P) (bestRow P d) (insertionPosition P d i) ≐ i :=
  selected_listed _ _ _ hi hb

theorem retained_repeated_cell (P d i j : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] neg (bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero)) (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) : Γ ⊢[PRAAx]
    cell (bordered P d i) (rank P d) j ≐ cell (bordered P d i) (insertionPosition P d i) j := by
  have retained := retained_position P d i hi hb
  have old := (bordered_old P d i (insertionPosition P d i) j retained.andE₁ hj).eqTrans
    (cleared_cell_congr P d retained.andE₂ (.eqRefl _))
  exact (bordered_last P d i j hj).eqTrans old.eqSymm

theorem retained_repeated (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] neg (bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero)) : Γ ⊢[PRAAx]
    repeatedLastRow (bordered P d i) (rank P d) (insertionPosition P d i) := by
  refine .allI (.impI ?_)
  let a := Syn.shift P
  let b := Syn.shift d
  let c := Syn.shift i
  let Δ := lt (var 0) (succ (rank a b)) :: Γ.map Fm.shift
  have ih : Δ ⊢[PRAAx] lt c (length a) := by simpa [Δ,a,c,Fm.shift,Syn.shift] using hi.shift.wk
  have bh : Δ ⊢[PRAAx] neg (bit (bestRow a b) c ≐ ConciseIPRA.PTm.zero) := by simpa [Δ,a,b,c,Fm.shift,Syn.shift] using hb.shift.wk
  simpa [Δ,a,b,c,Fm.shift,Syn.shift] using value_equal_of_code (retained_repeated_cell a b c (var 0) ih bh Prf.hyp0)

theorem retained_determinant_zero (P d i : PTm n) (hi : Γ ⊢[PRAAx] lt i (length P))
    (hb : Γ ⊢[PRAAx] neg (bit (bestRow P d) i ≐ ConciseIPRA.PTm.zero)) : Γ ⊢[PRAAx]
    scalarDet (bordered P d i) (succ (rank P d)) ≐ qzero :=
  repeated_last_determinant _ _ _ (retained_position P d i hi hb).andE₁ (retained_repeated P d i hi hb)

/-- Every original row gives a zero bordered determinant, from the actual
maximum-minor scan and its masks alone. -/
theorem bordered_determinant_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P)) :
    Γ ⊢[PRAAx] scalarDet (bordered P d i) (succ (rank P d)) ≐ qzero :=
  .orE (eq_or_ne (bit (bestRow P d) i) ConciseIPRA.PTm.zero)
    (outside_determinant_zero P d i h.wk hi.wk Prf.hyp0) (retained_determinant_zero P d i hi.wk Prf.hyp0)

theorem bordered_length (P d i : PTm n) : Γ ⊢[PRAAx] length (bordered P d i) ≐ succ (rank P d) := table_length _ _ _ _
theorem bordered_row_length (P d i r : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) :
    Γ ⊢[PRAAx] length (entry (bordered P d i) r) ≐ succ (rank P d) := table_row_length _ _ _ _ _ hr
theorem bordered_shape (P d i : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (bordered P d i) (succ (rank P d)) := by
  refine .andI (bordered_length _ _ _) (.allI (.impI ?_))
  simpa only [Syn.shift,subst_bordered,RationalMaximalMinors.subst_rank,ConciseIPRA.PTm.subst_succ] using
    bordered_row_length (Syn.shift P) (Syn.shift d) (Syn.shift i) (var 0) Prf.hyp0
theorem bordered_canonical (P d i r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ (rank P d))) (hj : Γ ⊢[PRAAx] lt j (succ (rank P d))) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (cell (bordered P d i) r j) :=
  GaussianRationalHorner.canonical_congr (bordered_lookup P d i r j hr hj) (cleared_cell_canonical _ _ _ _)

/-- Actual table, actual determinant, original chosen rank and retained position. -/
def output (P d i : PTm n) : PTm n := pairT (bordered P d i)
  (pairT (scalarDet (bordered P d i) (succ (rank P d))) (pairT (rank P d) (insertionPosition P d i)))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (P d i : PTm n) : PTm n := ap3 outputF P d i
@[simp] theorem subst_output {k : ℕ} (σ : Fin n → PTm k) (P d i : PTm n) :
    Syn.subst σ (output P d i) = output (Syn.subst σ P) (Syn.subst σ d) (Syn.subst σ i) := by simp [output]
theorem program_at (P d i : PTm n) : Γ ⊢[PRAAx] run P d i ≐ output P d i := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![P,d,i]
theorem returned_table (P d i : PTm n) : Γ ⊢[PRAAx] fstT (run P d i) ≐ bordered P d i :=
  (congrFst (program_at P d i)).eqTrans (fst_pair _ _)
theorem returned_tail (P d i : PTm n) : Γ ⊢[PRAAx] sndT (run P d i) ≐
    pairT (scalarDet (bordered P d i) (succ (rank P d))) (pairT (rank P d) (insertionPosition P d i)) :=
  (congrSnd (program_at P d i)).eqTrans (snd_pair _ _)
theorem returned_determinant (P d i : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run P d i)) ≐ scalarDet (bordered P d i) (succ (rank P d)) :=
  (congrFst (returned_tail P d i)).eqTrans (fst_pair _ _)
theorem returned_indices (P d i : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run P d i)) ≐ pairT (rank P d) (insertionPosition P d i) :=
  (congrSnd (returned_tail P d i)).eqTrans (snd_pair _ _)
theorem returned_rank (P d i : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run P d i))) ≐ rank P d :=
  (congrFst (returned_indices P d i)).eqTrans (fst_pair _ _)
theorem returned_position (P d i : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run P d i))) ≐ insertionPosition P d i :=
  (congrSnd (returned_indices P d i)).eqTrans (snd_pair _ _)
theorem returned_zero (P d i : PTm n) (h : Γ ⊢[PRAAx] lt (rank P d) d) (hi : Γ ⊢[PRAAx] lt i (length P)) :
    Γ ⊢[PRAAx] fstT (sndT (run P d i)) ≐ qzero :=
  (returned_determinant P d i).eqTrans (bordered_determinant_zero P d i h hi)

theorem actual_bordered_last_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 3) (succ (rank (var 0) (var 1))) ⟶
      cell (bordered (var 0) (var 1) (var 2)) (rank (var 0) (var 1)) (var 3) ≐
        clearedCell (var 0) (var 1) (var 2) (index (var 1) (extendedColumn (var 0) (var 1)) (var 3))) :=
  closeUniv 4 (.impI (bordered_last _ _ _ _ Prf.hyp0))
theorem actual_bordered_retained_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 3) (rank (var 0) (var 1)) ⟶ lt (var 4) (succ (rank (var 0) (var 1))) ⟶
      cell (bordered (var 0) (var 1) (var 2)) (var 3) (var 4) ≐
        clearedCell (var 0) (var 1) (index (length (var 0)) (bestRow (var 0) (var 1)) (var 3))
          (index (var 1) (extendedColumn (var 0) (var 1)) (var 4))) :=
  closeUniv 5 (.impI (.impI (bordered_old _ _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_augmented_minor_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      bit (bestRow (var 0) (var 1)) (var 2) ≐ ConciseIPRA.PTm.zero ⟶
        scalarDet (augmented (var 0) (var 1) (var 2)) (succ (rank (var 0) (var 1))) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (.impI (augmented_zero _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_outside_bordered_comparison_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      bit (bestRow (var 0) (var 1)) (var 2) ≐ ConciseIPRA.PTm.zero ⟶
        scalarCellsEqual (bordered (var 0) (var 1) (var 2)) (moved (var 0) (var 1) (var 2)) (succ (rank (var 0) (var 1)))) :=
  closeUniv 3 (.impI (.impI (.impI (outside_cells _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_retained_bordered_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (length (var 0)) ⟶ neg (bit (bestRow (var 0) (var 1)) (var 2) ≐ ConciseIPRA.PTm.zero) ⟶
      scalarDet (bordered (var 0) (var 1) (var 2)) (succ (rank (var 0) (var 1))) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (retained_determinant_zero _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_bordered_determinant_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶
      scalarDet (bordered (var 0) (var 1) (var 2)) (succ (rank (var 0) (var 1))) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (bordered_determinant_zero _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_bordered_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMatrixFiniteSums.squareShape (bordered (var 0) (var 1) (var 2)) (succ (rank (var 0) (var 1)))) :=
  closeUniv 3 (bordered_shape _ _ _)
theorem actual_bordered_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_bordered_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (rank (var 0) (var 1)) (var 1) ⟶ lt (var 2) (length (var 0)) ⟶ fstT (sndT (run (var 0) (var 1) (var 2))) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (returned_zero _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.RationalCofactorBorderedRows

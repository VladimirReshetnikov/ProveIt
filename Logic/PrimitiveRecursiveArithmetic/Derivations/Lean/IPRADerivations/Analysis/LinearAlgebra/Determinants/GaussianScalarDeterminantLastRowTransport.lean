import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarDeterminantRowSelection

/-!
# Actual last-row transports for a vanishing scalar determinant

A numerical row selector moves row p to the last position and reads all
other rows through the original skip-slot program. A second actual table
zeros the last row; selecting a repeated retained row from that table
proves the repeated-last-row determinant is zero. Only bounded native
field equality of the repeated cells is required, including raw entries.
No determinant covariance or row-sign law is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLastRowTransport

open_ipra
open GaussianRationalFiberVandermonde (table table_lookup)
open GaussianPolynomialDeterminantTerms (cell)
open GaussianScalarDeterminant (scalarDet scalarCellsEqual scalar_det_congr)
open GaussianScalarDeterminantRowSelection
  (selected selected_lookup selected_determinant_zero zeroLastRow zero_last_determinant)
open GaussianRationalHorner (qzero)
open GaussianTranslatedNonconstant (recode recode_congr recode_eq recode_canonical)
open GaussianRationalValueEquality (valueEqual recode_equal_of_equal_values equal_values_of_recode_equal value_equal_symm)
open GaussianScalarColumnSelection (cell_congr)
open LeanProofs.IPRA.Foundations.RuntimePermutationDeletion (slot slot_bound)
open LeanProofs.IPRA.Foundations.GuardedTotalization (sel sel_one sel_zero)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def moveIndex (m p r : PTm n) : PTm n := sel (eqb r m) p (slot p r)
def moveBody : PTm 2 := moveIndex (fstT (var 1)) (sndT (var 1)) (var 0)
def moveToLast (A m p : PTm n) : PTm n := selected moveBody A (succ m) (pairT m p)

ipra_subst moveIndex [sel]
ipra_subst moveToLast

theorem move_index_congr {m b p q r s : PTm n} (hm : Γ ⊢[PRAAx] m ≐ b) (hp : Γ ⊢[PRAAx] p ≐ q)
    (hr : Γ ⊢[PRAAx] r ≐ s) : Γ ⊢[PRAAx] moveIndex m p r ≐ moveIndex b q s := by
  ipra_congr (moveIndex (var 0) (var 1) (var 2) : PTm 3) with [hm, hp, hr]

theorem move_body_at (m p r : PTm n) : Γ ⊢[PRAAx] inst2 moveBody r (pairT m p) ≐ moveIndex m p r := by
  simpa only [moveBody,inst2,subst_moveIndex,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    move_index_congr (fst_pair (Γ := Γ) m p) (snd_pair m p) (.eqRefl r)
theorem move_index_last (m p : PTm n) : Γ ⊢[PRAAx] moveIndex m p m ≐ p := sel_one (eqb_of_eq (.eqRefl _))
theorem move_index_other (m p r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] moveIndex m p r ≐ slot p r :=
  sel_zero (eqb_of_ne (Foundations.RuntimeAdjacentPermutationSwap.different_of_lt hr))
theorem move_index_bound (m p r : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hr : Γ ⊢[PRAAx] lt r (succ m)) :
    Γ ⊢[PRAAx] lt (moveIndex m p r) (succ m) := by
  have rm : Γ ⊢[PRAAx] le r m := (succ_monus_succ r m).eqSymm.eqTrans hr
  refine .orE (lt_or_eq_of_le rm) ?_ ?_
  · exact lt_congr (move_index_other m p r Prf.hyp0).eqSymm (.eqRefl _) (slot_bound m p r Prf.hyp0)
  · exact lt_congr ((move_index_congr (.eqRefl m) (.eqRefl p) Prf.hyp0).eqTrans (move_index_last m p)).eqSymm (.eqRefl _) hp.wk

theorem moved_lookup (A m p r j : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m))
    (hr : Γ ⊢[PRAAx] lt r (succ m)) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    cell (moveToLast A m p) r j ≐ recode (cell A (moveIndex m p r) j) := by
  have hIndex : Γ ⊢[PRAAx] lt (inst2 moveBody r (pairT m p)) (succ m) :=
    lt_congr (move_body_at m p r).eqSymm (.eqRefl _) (move_index_bound m p r hp hr)
  exact (selected_lookup moveBody A (succ m) (pairT m p) r j hr hj hIndex).eqTrans
    (recode_congr (cell_congr (.eqRefl A) (move_body_at m p r) (.eqRefl j)))
theorem moved_last_lookup (A m p j : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m)) (hj : Γ ⊢[PRAAx] lt j (succ m)) :
    Γ ⊢[PRAAx] cell (moveToLast A m p) m j ≐ recode (cell A p j) :=
  (moved_lookup A m p m j hp (le_refl _) hj).eqTrans (recode_congr (cell_congr (.eqRefl A) (move_index_last m p) (.eqRefl j)))
theorem moved_other_lookup (A m p r j : PTm n) (hp : Γ ⊢[PRAAx] lt p (succ m))
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    cell (moveToLast A m p) r j ≐ recode (cell A (slot p r) j) :=
  (moved_lookup A m p r j hp (lt_of_lt_of_le hr (le_succ_self m)) hj).eqTrans
    (recode_congr (cell_congr (.eqRefl A) (move_index_other m p r hr) (.eqRefl j)))
theorem moved_shape (A m p : PTm n) : Γ ⊢[PRAAx] GaussianRationalMatrixFiniteSums.squareShape (moveToLast A m p) (succ m) :=
  GaussianRationalMatrixFiniteSums.product_shape _ _ _
theorem moved_determinant_zero (A m p : PTm n) (h : Γ ⊢[PRAAx] scalarDet A (succ m) ≐ qzero) :
    Γ ⊢[PRAAx] scalarDet (moveToLast A m p) (succ m) ≐ qzero :=
  selected_determinant_zero moveBody A (succ m) (pairT m p) h

/-- Zeroing and repeated-row selection are actual tables on the SAME input. -/
def zeroedBody : PTm 3 := sel (eqb (var 0) (sndT (var 2))) qzero (cell (fstT (var 2)) (var 0) (var 1))
def zeroedLast (A m : PTm n) : PTm n := table zeroedBody (succ m) (succ m) (pairT A m)
def duplicateIndex (m k r : PTm n) : PTm n := sel (eqb r m) k r
def duplicateBody : PTm 2 := duplicateIndex (fstT (var 1)) (sndT (var 1)) (var 0)
def duplicated (A m k : PTm n) : PTm n := selected duplicateBody (zeroedLast A m) (succ m) (pairT m k)
def repeatedLastRow (A m k : PTm n) : Fm PTm n := .all
  (lt (var 0) (succ (Syn.shift m)) ⟶ valueEqual (cell (Syn.shift A) (Syn.shift m) (var 0)) (cell (Syn.shift A) (Syn.shift k) (var 0)))

ipra_subst zeroedLast
ipra_subst duplicateIndex [sel]
ipra_subst duplicated
ipra_subst repeatedLastRow [Syn.subst_shift, Syn.shift_subst]

theorem zeroed_lookup (A m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r (succ m)) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    cell (zeroedLast A m) r j ≐ sel (eqb r m) qzero (cell A r j) := by
  have e := table_lookup (Γ := Γ) zeroedBody (succ m) (succ m) (pairT A m) r j hr hj
  simp [zeroedBody,sel] at e
  exact e.eqTrans (by
    have hs : Γ ⊢[PRAAx] sndT (pairT A m) ≐ m := snd_pair _ _
    have ha : Γ ⊢[PRAAx] fstT (pairT A m) ≐ A := fst_pair _ _
    simpa [sel] using
      Prf.eqCongr (Ax := PRAAx) (Γ := Γ) (sel (eqb (var 0) (var 1)) qzero (cell (var 2) (var 0) (var 3)) : PTm 4)
        (σ := ![r,sndT (pairT A m),fstT (pairT A m),j]) (σ' := ![r,m,A,j])
        (fun i => by fin_cases i; exact .eqRefl _; exact hs; exact ha; exact .eqRefl _))
theorem zeroed_last_lookup (A m j : PTm n) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx] cell (zeroedLast A m) m j ≐ qzero :=
  (zeroed_lookup A m m j (le_refl _) hj).eqTrans (sel_one (eqb_of_eq (.eqRefl _)))
theorem zeroed_other_lookup (A m r j : PTm n) (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j (succ m)) :
    Γ ⊢[PRAAx] cell (zeroedLast A m) r j ≐ cell A r j :=
  (zeroed_lookup A m r j (lt_of_lt_of_le hr (le_succ_self m)) hj).eqTrans
    (sel_zero (eqb_of_ne (Foundations.RuntimeAdjacentPermutationSwap.different_of_lt hr)))

theorem zeroed_last_row (A m : PTm n) : Γ ⊢[PRAAx] zeroLastRow (zeroedLast A m) m := by
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_zeroedLast,ConciseIPRA.PTm.subst_succ] using
    zeroed_last_lookup (Γ := lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift) (Syn.shift A) (Syn.shift m) (var 0) Prf.hyp0
theorem zeroed_determinant (A m : PTm n) : Γ ⊢[PRAAx] scalarDet (zeroedLast A m) (succ m) ≐ qzero :=
  zero_last_determinant _ _ (zeroed_last_row A m)

theorem duplicate_index_congr {m b k l r s : PTm n} (hm : Γ ⊢[PRAAx] m ≐ b) (hk : Γ ⊢[PRAAx] k ≐ l)
    (hr : Γ ⊢[PRAAx] r ≐ s) : Γ ⊢[PRAAx] duplicateIndex m k r ≐ duplicateIndex b l s := by
  ipra_congr (duplicateIndex (var 0) (var 1) (var 2) : PTm 3) with [hm, hk, hr]
theorem duplicate_body_at (m k r : PTm n) : Γ ⊢[PRAAx] inst2 duplicateBody r (pairT m k) ≐ duplicateIndex m k r := by
  simpa only [duplicateBody,inst2,subst_duplicateIndex,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    duplicate_index_congr (fst_pair (Γ := Γ) m k) (snd_pair m k) (.eqRefl r)
theorem duplicate_index_last (m k : PTm n) : Γ ⊢[PRAAx] duplicateIndex m k m ≐ k := sel_one (eqb_of_eq (.eqRefl _))
theorem duplicate_index_other (m k r : PTm n) (hr : Γ ⊢[PRAAx] lt r m) : Γ ⊢[PRAAx] duplicateIndex m k r ≐ r :=
  sel_zero (eqb_of_ne (Foundations.RuntimeAdjacentPermutationSwap.different_of_lt hr))
theorem duplicate_index_bound (m k r : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (hr : Γ ⊢[PRAAx] lt r (succ m)) :
    Γ ⊢[PRAAx] lt (duplicateIndex m k r) (succ m) := by
  have rm : Γ ⊢[PRAAx] le r m := (succ_monus_succ r m).eqSymm.eqTrans hr
  refine .orE (lt_or_eq_of_le rm) ?_ ?_
  · exact lt_congr (duplicate_index_other m k r Prf.hyp0).eqSymm (.eqRefl _) hr.wk
  · exact lt_congr ((duplicate_index_congr (.eqRefl m) (.eqRefl k) Prf.hyp0).eqTrans (duplicate_index_last m k)).eqSymm
      (.eqRefl _) (lt_of_lt_of_le hk.wk (le_succ_self m))

theorem duplicated_lookup (A m k r j : PTm n) (hk : Γ ⊢[PRAAx] lt k m)
    (hr : Γ ⊢[PRAAx] lt r (succ m)) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    cell (duplicated A m k) r j ≐ recode (cell (zeroedLast A m) (duplicateIndex m k r) j) := by
  have hIndex : Γ ⊢[PRAAx] lt (inst2 duplicateBody r (pairT m k)) (succ m) :=
    lt_congr (duplicate_body_at m k r).eqSymm (.eqRefl _) (duplicate_index_bound m k r hk hr)
  exact (selected_lookup duplicateBody (zeroedLast A m) (succ m) (pairT m k) r j hr hj hIndex).eqTrans
    (recode_congr (cell_congr (.eqRefl _) (duplicate_body_at m k r) (.eqRefl j)))
theorem duplicated_last_lookup (A m k j : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    cell (duplicated A m k) m j ≐ recode (cell A k j) :=
  (duplicated_lookup A m k m j hk (le_refl _) hj).eqTrans
    ((recode_congr (cell_congr (.eqRefl _) (duplicate_index_last m k) (.eqRefl j))).eqTrans
      (recode_congr (zeroed_other_lookup A m k j hk hj)))
theorem duplicated_other_lookup (A m k r j : PTm n) (hk : Γ ⊢[PRAAx] lt k m)
    (hr : Γ ⊢[PRAAx] lt r m) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    cell (duplicated A m k) r j ≐ recode (cell A r j) :=
  (duplicated_lookup A m k r j hk (lt_of_lt_of_le hr (le_succ_self m)) hj).eqTrans
    ((recode_congr (cell_congr (.eqRefl _) (duplicate_index_other m k r hr) (.eqRefl j))).eqTrans
      (recode_congr (zeroed_other_lookup A m r j hr hj)))
theorem repeated_last_at (A m k j : PTm n) (h : Γ ⊢[PRAAx] repeatedLastRow A m k) (hj : Γ ⊢[PRAAx] lt j (succ m)) :
    Γ ⊢[PRAAx] valueEqual (cell A m j) (cell A k j) := by
  have rule : Γ ⊢[PRAAx] lt j (succ m) ⟶ valueEqual (cell A m j) (cell A k j) := by simpa [repeatedLastRow] using h.allE j
  exact .impE rule hj

theorem normalized_read_value {q r : PTm n} (h : Γ ⊢[PRAAx] q ≐ recode r) : Γ ⊢[PRAAx] valueEqual q r :=
  equal_values_of_recode_equal _ _ ((recode_congr h).eqTrans (recode_eq _ (recode_canonical _)))
theorem duplicated_cell_value (A m k r j : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (h : Γ ⊢[PRAAx] repeatedLastRow A m k)
    (hr : Γ ⊢[PRAAx] lt r (succ m)) (hj : Γ ⊢[PRAAx] lt j (succ m)) : Γ ⊢[PRAAx]
    valueEqual (cell (duplicated A m k) r j) (cell A r j) := by
  have rm : Γ ⊢[PRAAx] le r m := (succ_monus_succ r m).eqSymm.eqTrans hr
  refine .orE (lt_or_eq_of_le rm) ?_ ?_
  · exact normalized_read_value (duplicated_other_lookup A m k r j hk.wk Prf.hyp0 hj.wk)
  · have read : (r ≐ m) :: Γ ⊢[PRAAx] cell (duplicated A m k) r j ≐ recode (cell A k j) :=
      (cell_congr (.eqRefl _) Prf.hyp0 (.eqRefl _)).eqTrans (duplicated_last_lookup A m k j hk.wk hj.wk)
    have native : (r ≐ m) :: Γ ⊢[PRAAx] recode (cell A m j) ≐ recode (cell A k j) :=
      recode_equal_of_equal_values _ _ (repeated_last_at A m k j h.wk hj.wk)
    exact equal_values_of_recode_equal _ _ (((recode_congr read).eqTrans (recode_eq _ (recode_canonical _))).eqTrans
      (native.eqSymm.eqTrans (recode_congr (cell_congr (.eqRefl A) Prf.hyp0.eqSymm (.eqRefl j)))))

theorem duplicated_values (A m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (h : Γ ⊢[PRAAx] repeatedLastRow A m k) :
    Γ ⊢[PRAAx] scalarCellsEqual (duplicated A m k) A (succ m) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let a := Syn.shift (Syn.shift A)
  let b := Syn.shift (Syn.shift m)
  let c := Syn.shift (Syn.shift k)
  let Δ := lt (var 0) (succ b) :: List.map Fm.shift (lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift)
  have rr : Δ ⊢[PRAAx] lt (var 1) (succ b) := by
    simpa only [Δ,b,List.map_cons,Fm.shift,subst_lt,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,ConciseIPRA.PTm.subst_succ] using
      (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (succ (Syn.shift m))).shift)
  have jj : Δ ⊢[PRAAx] lt (var 0) (succ b) := Prf.hyp0
  have kh : Δ ⊢[PRAAx] lt c b := by
    simpa only [Δ,b,c,List.map_cons,Fm.shift,subst_lt,Syn.shift] using hk.shift.shift.wk.wk
  have hh : Δ ⊢[PRAAx] repeatedLastRow a b c := by
    simpa only [Δ,a,b,c,List.map_cons,Fm.shift,subst_repeatedLastRow,Syn.shift] using h.shift.shift.wk.wk
  simpa only [Δ,a,b,c,Syn.shift,Syn.subst_var,Fin.succ_zero_eq_one,subst_duplicated,ConciseIPRA.PTm.subst_succ] using
    duplicated_cell_value a b c (var 1) (var 0) kh hh rr jj

theorem duplicated_determinant_zero (A m k : PTm n) : Γ ⊢[PRAAx] scalarDet (duplicated A m k) (succ m) ≐ qzero :=
  selected_determinant_zero duplicateBody (zeroedLast A m) (succ m) (pairT m k) (zeroed_determinant A m)

/-- A last row equal as a field value to an earlier row forces the original
raw table determinant to vanish. The witness table and selectors are computed. -/
theorem repeated_last_determinant (A m k : PTm n) (hk : Γ ⊢[PRAAx] lt k m) (h : Γ ⊢[PRAAx] repeatedLastRow A m k) :
    Γ ⊢[PRAAx] scalarDet A (succ m) ≐ qzero :=
  (scalar_det_congr (duplicated A m k) A (succ m) (duplicated_values A m k hk h)).eqSymm.eqTrans
    (duplicated_determinant_zero A m k)

/-- One fixed program returns all three actual tables on numerical A,m,p. -/
def output (A m p : PTm n) : PTm n := pairT (moveToLast A m p) (pairT (zeroedLast A m) (duplicated A m p))
def outputF : PR 3 := PTm.toPR (output (var 0) (var 1) (var 2))
def run (A m p : PTm n) : PTm n := ap3 outputF A m p
ipra_subst output
theorem program_at (A m p : PTm n) : Γ ⊢[PRAAx] run A m p ≐ output A m p := by
  simpa [run,outputF,ap3] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) : PTm 3) ![A,m,p]
theorem returned_moved (A m p : PTm n) : Γ ⊢[PRAAx] fstT (run A m p) ≐ moveToLast A m p :=
  (program_at A m p).fstE
theorem returned_tail (A m p : PTm n) : Γ ⊢[PRAAx] sndT (run A m p) ≐ pairT (zeroedLast A m) (duplicated A m p) :=
  (program_at A m p).sndE
theorem returned_zeroed (A m p : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run A m p)) ≐ zeroedLast A m :=
  (returned_tail A m p).fstE
theorem returned_duplicated (A m p : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run A m p)) ≐ duplicated A m p :=
  (returned_tail A m p).sndE

theorem actual_move_row_to_last_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2) (succ (var 1)) ⟶ lt (var 3) (succ (var 1)) ⟶
      cell (moveToLast (var 0) (var 1) (var 2)) (var 1) (var 3) ≐ recode (cell (var 0) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (moved_last_lookup _ _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_move_remaining_rows_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lt (var 2) (succ (var 1)) ⟶ lt (var 3) (var 1) ⟶ lt (var 4) (succ (var 1)) ⟶
      cell (moveToLast (var 0) (var 1) (var 2)) (var 3) (var 4) ≐ recode (cell (var 0) (slot (var 2) (var 3)) (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (moved_other_lookup _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_moved_square_shape_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (GaussianRationalMatrixFiniteSums.squareShape (moveToLast (var 0) (var 1) (var 2)) (succ (var 1))) :=
  closeUniv 3 (moved_shape _ _ _)
theorem actual_moved_determinant_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (scalarDet (var 0) (succ (var 1)) ≐ qzero ⟶ scalarDet (moveToLast (var 0) (var 1) (var 2)) (succ (var 1)) ≐ qzero) :=
  closeUniv 3 (.impI (moved_determinant_zero _ _ _ Prf.hyp0))
theorem actual_zeroed_last_row_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (zeroLastRow (zeroedLast (var 0) (var 1)) (var 1)) := closeUniv 2 (zeroed_last_row _ _)
theorem actual_zeroed_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (scalarDet (zeroedLast (var 0) (var 1)) (succ (var 1)) ≐ qzero) := closeUniv 2 (zeroed_determinant _ _)
theorem actual_repeated_last_determinant_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 2) (var 1) ⟶ repeatedLastRow (var 0) (var 1) (var 2) ⟶ scalarDet (var 0) (succ (var 1)) ≐ qzero) :=
  closeUniv 3 (.impI (.impI (repeated_last_determinant _ _ _ Prf.hyp1 Prf.hyp0)))
theorem actual_last_row_transport_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (run (var 0) (var 1) (var 2) ≐ output (var 0) (var 1) (var 2)) := closeUniv 3 (program_at _ _ _)
theorem actual_returned_last_row_transport_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (fstT (run (var 0) (var 1) (var 2)) ≐ moveToLast (var 0) (var 1) (var 2) ⋏
      fstT (sndT (run (var 0) (var 1) (var 2))) ≐ zeroedLast (var 0) (var 1) ⋏
        sndT (sndT (run (var 0) (var 1) (var 2))) ≐ duplicated (var 0) (var 1) (var 2)) :=
  closeUniv 3 (.andI (returned_moved _ _ _) (.andI (returned_zeroed _ _ _) (returned_duplicated _ _ _)))

end LeanProofs.IPRA.Analysis.GaussianScalarDeterminantLastRowTransport

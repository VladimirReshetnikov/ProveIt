import IPRADerivations.Analysis.LinearAlgebra.Matrices.RationalMatrixClearingBounds

/-!
# A computed bound for the original rational matrix entries

The sum of numerator magnitudes and positive denominators, plus one,
bounds all entries at the original numerical dimensions. This discharges
the height hypothesis when only integrality of the cleared minors is needed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalMatrixInputHeight

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open RationalSupMetric (rationalNumerator rationalDenominator)
open RationalMatrixClearingBounds (inputMatrix inputRow subst_inputRow)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def entrySize (v i : PTm n) : PTm n := zabs (rationalNumerator v i) + rationalDenominator v i
def rowBody : PTm 2 := entrySize (var 1) (var 0)
def rowTotal (v d : PTm n) : PTm n := ap2 (sumF rowBody) d v
def matrixBody : PTm 2 := rowTotal (entry (fstT (var 1)) (var 0)) (sndT (var 1))
def matrixTotal (P d : PTm n) : PTm n := ap2 (sumF matrixBody) (length P) (pairT P d)
def height (P d : PTm n) : PTm n := succ (matrixTotal P d)

@[simp] theorem subst_entrySize {k : ℕ} (σ : Fin n → PTm k) (v i : PTm n) :
    Syn.subst σ (entrySize v i) = entrySize (Syn.subst σ v) (Syn.subst σ i) := by
  unfold entrySize
  rw [PTm.subst_add, Foundations.GapDecision.subst_zabs, RationalSupMetric.subst_rationalNumerator,
    RationalSupMetric.subst_rationalDenominator]
ipra_subst rowTotal
ipra_subst height [matrixTotal]

theorem matrix_body_at (P d j : PTm n) : Γ ⊢[PRAAx] inst2 matrixBody j (pairT P d) ≐ rowTotal (entry P j) d := by
  simpa [matrixBody,inst2,rowTotal] using
    congrAp2 (sumF rowBody) (snd_pair (Γ := Γ) P d)
      (Foundations.SequenceComposition.entry_congr (fst_pair P d) (.eqRefl j))

theorem entry_le_row (v d i : PTm n) (hi : Γ ⊢[PRAAx] lt i d) : Γ ⊢[PRAAx] le (entrySize v i) (rowTotal v d) := by
  simpa only [rowBody,inst2,subst_entrySize,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,rowTotal] using
    (term_le_sum rowBody (x := v) hi)

theorem row_le_matrix (P d j : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) :
    Γ ⊢[PRAAx] le (rowTotal (entry P j) d) (matrixTotal P d) :=
  le_congr (matrix_body_at P d j) (.eqRefl _) (term_le_sum matrixBody (x := pairT P d) hj)

theorem height_positive (P d : PTm n) : Γ ⊢[PRAAx] le one (height P d) := zero_lt_succ (matrixTotal P d)

theorem coordinate_bound (P d j i : PTm n) (hj : Γ ⊢[PRAAx] lt j (length P)) (hi : Γ ⊢[PRAAx] lt i d) :
    Γ ⊢[PRAAx] le (zabs (rationalNumerator (entry P j) i)) (height P d) ⋏
      le (rationalDenominator (entry P j) i) (height P d) := by
  have rest := le_trans (entry_le_row _ _ _ hi) (le_trans (row_le_matrix _ _ _ hj) (le_succ_self _))
  exact .andI (le_trans (le_add_right _ _) rest) (le_trans (le_add_left _ _) rest)

theorem input_height (P d : PTm n) : Γ ⊢[PRAAx] inputMatrix P d (height P d) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let shift2 (t : PTm n) := Syn.shift (Syn.shift t)
  let P' := shift2 P
  let d' := shift2 d
  let Δ := lt (var 0) d' :: (lt (var 0) (length (Syn.shift P)) :: Γ.map Fm.shift).map Fm.shift
  have hj : Δ ⊢[PRAAx] lt (var 1) (length P') := by
    simpa only [Δ,P',d',shift2,List.map_cons,Fm.shift,subst_lt,Foundations.SequenceComposition.subst_length,Syn.shift,Syn.subst_var,
      Fin.succ_zero_eq_one] using (Prf.hyp1 : Δ ⊢[PRAAx] (lt (var 0) (length (Syn.shift P))).shift)
  have hi : Δ ⊢[PRAAx] lt (var 0) d' := Prf.hyp0
  simpa only [Δ,P',d',shift2,Syn.shift,subst_height,Foundations.MasterCertificate.subst_entry,Syn.subst_var,Fin.succ_zero_eq_one] using
    coordinate_bound P' d' (var 1) (var 0) hj hi

def heightF : PR 2 := PTm.toPR (height (var 0) (var 1))

theorem height_at (P d : PTm n) : Γ ⊢[PRAAx] ap2 heightF P d ≐ height P d := by
  simpa [heightF,ap2] using toPR_eq (Γ := Γ) (height (var 0) (var 1) : PTm 2) ![P,d]

theorem actual_computed_input_height_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (height (var 0) (var 1)) ⋏ inputMatrix (var 0) (var 1) (height (var 0) (var 1))) :=
  closeUniv 2 (.andI (height_positive _ _) (input_height _ _))

theorem actual_input_height_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (ap2 heightF (var 0) (var 1) ≐ height (var 0) (var 1)) := closeUniv 2 (height_at _ _)

end LeanProofs.IPRA.Analysis.RationalMatrixInputHeight

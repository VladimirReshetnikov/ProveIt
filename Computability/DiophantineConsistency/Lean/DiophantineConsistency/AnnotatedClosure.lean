import DiophantineConsistency.AnnotatedRenameArithmetic

/-! # Literal numeric universal closure

The closing length is an explicit input. Computing that length from formula
syntax is a separate arithmetic-table operation. -/

namespace DiophantineConsistency.AnnotatedClosure

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename
open ScalarPRCode DirectScalar

set_option maxRecDepth 12000
set_option maxHeartbeats 600000
attribute [local irreducible] Nat.unpair

def closeCode (input length : Nat) : Nat :=
  length.rec input (fun _ acc => unaryCode 6 acc)

theorem closeN_all (length : Nat) (f : Form) :
    closeN length (fAll f)=fAll (closeN length f) := by
  induction length generalizing f with
  | zero => rfl
  | succ length ih => exact ih (fAll f)

theorem closeCode_formCode (f : Form) (length : Nat) :
    closeCode (formCode f) length=formCode (closeN length f) := by
  induction length with
  | zero => rfl
  | succ length ih =>
    simp only [closeCode] at *
    rw [ih,←code_all,closeN,closeN_all]

theorem closeCode_sealF (f : Form) :
    closeCode (formCode f) (bound f)=formCode (sealF f) :=
  closeCode_formCode f (bound f)

/-- The literal supplied program receives `(formulaCode,closingLength)`. -/
def program : R (fun n => closeCode n.unpair.1 n.unpair.2) :=
  recursion (g := fun _ _ acc => unaryCode 6 acc) identity
    (AnnotatedRenameArithmetic.unary (constant 6)
      (Realizes.right.comp Realizes.right))

theorem program_input (input length : Nat) :
    program.val.eval (Nat.pair input length)=closeCode input length := by
  rw [program.property]
  simp only [Nat.unpair_pair]

theorem program_sealF (f : Form) :
    program.val.eval (Nat.pair (formCode f) (bound f))=formCode (sealF f) := by
  rw [program_input,closeCode_sealF]

theorem program_primrec : Nat.Primrec program.val.eval := program.val.primrec

private theorem right_square_le_pair (a b : Nat) : b*b≤Nat.pair a b := by
  unfold Nat.pair
  split_ifs with h
  · omega
  · have hb : b≤a := by omega
    have hm : b*b≤a*a := Nat.mul_self_le_mul_self hb
    omega

private theorem atom_pos (n : Nat) : 1≤atomCode n := by
  change 1≤Nat.pair 0 n+1
  omega

private theorem fork_ge_eight (a b : Nat) (ha : 1≤a) (hb : 1≤b) :
    8≤forkCode a b := by
  unfold forkCode Nat.pair
  split_ifs with h
  · have hbb : 9≤b*b := by nlinarith
    omega
  · have haa : 4≤(a+1)*(a+1) := by nlinarith
    omega

private theorem fork_ge_right_square (a b : Nat) : b*b+1≤forkCode a b := by
  exact Nat.add_le_add_right (right_square_le_pair (a+1) b) 1

/-- Valid formula codes lie above the fixed universal-tag code. -/
theorem formCode_ge (f : Form) : 44≤formCode f := by
  induction f with
  | fMem i j =>
    have h := fork_ge_eight (atomCode i) (atomCode j) (atom_pos i) (atom_pos j)
    have hh := fork_ge_right_square (atomCode 0) (forkCode (atomCode i) (atomCode j))
    change 44≤forkCode (atomCode 0) (forkCode (atomCode i) (atomCode j))
    nlinarith
  | fEq i j =>
    have h := fork_ge_eight (atomCode i) (atomCode j) (atom_pos i) (atom_pos j)
    have hh := fork_ge_right_square (atomCode 1) (forkCode (atomCode i) (atomCode j))
    change 44≤forkCode (atomCode 1) (forkCode (atomCode i) (atomCode j))
    nlinarith
  | fBot => decide
  | fImp a b ha hb | fAnd a b ha hb | fOr a b ha hb =>
    first
    | change 44≤forkCode (atomCode 3) (forkCode (formCode a) (formCode b))
    | change 44≤forkCode (atomCode 4) (forkCode (formCode a) (formCode b))
    | change 44≤forkCode (atomCode 5) (forkCode (formCode a) (formCode b))
    have h := fork_ge_right_square (formCode a) (formCode b)
    first
    | have hh := fork_ge_right_square (atomCode 3) (forkCode (formCode a) (formCode b)); nlinarith
    | have hh := fork_ge_right_square (atomCode 4) (forkCode (formCode a) (formCode b)); nlinarith
    | have hh := fork_ge_right_square (atomCode 5) (forkCode (formCode a) (formCode b)); nlinarith
  | fAll a ha =>
    have h := fork_ge_right_square (atomCode 6) (formCode a)
    change 44≤forkCode (atomCode 6) (formCode a)
    nlinarith
  | fEx a ha =>
    have h := fork_ge_right_square (atomCode 7) (formCode a)
    change 44≤forkCode (atomCode 7) (formCode a)
    nlinarith

theorem unary_six_eq_quadratic (c : Nat) (hc : 38<c) :
    unaryCode 6 c=c*c+39 := by
  change Nat.pair 38 c+1=c*c+39
  simp only [Nat.pair,hc,if_true]

theorem code_all_quadratic (f : Form) :
    formCode (fAll f)=formCode f*formCode f+39 := by
  rw [code_all,unary_six_eq_quadratic]
  have h := formCode_ge f
  omega

def closeQuadratic (input length : Nat) : Nat :=
  length.rec input (fun _ acc => acc*acc+39)

theorem closeQuadratic_formCode (f : Form) (length : Nat) :
    closeQuadratic (formCode f) length=formCode (closeN length f) := by
  induction length with
  | zero => rfl
  | succ length ih =>
    simp only [closeQuadratic] at *
    rw [ih,←code_all_quadratic,closeN,closeN_all]

def quadraticProgram : R (fun n => closeQuadratic n.unpair.1 n.unpair.2) :=
  recursion (g := fun _ _ acc => acc*acc+39) identity
    (add (mul (Realizes.right.comp Realizes.right)
      (Realizes.right.comp Realizes.right)) (constant 39))

theorem quadraticProgram_sealF (f : Form) :
    quadraticProgram.val.eval (Nat.pair (formCode f) (bound f))=formCode (sealF f) := by
  rw [quadraticProgram.property]
  simp only [Nat.unpair_pair]
  exact closeQuadratic_formCode f (bound f)

theorem program_nodeCount : program.val.nodeCount=37 := by decide
theorem quadraticProgram_nodeCount : quadraticProgram.val.nodeCount=119 := by decide

end DiophantineConsistency.AnnotatedClosure

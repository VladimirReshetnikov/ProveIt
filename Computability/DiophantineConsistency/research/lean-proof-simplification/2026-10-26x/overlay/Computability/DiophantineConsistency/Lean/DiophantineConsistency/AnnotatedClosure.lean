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

private theorem pair_mono {a a' b b' : Nat} (ha : a≤a') (hb : b≤b') :
    Nat.pair a b≤Nat.pair a' b' :=
  ((show StrictMono (fun a => Nat.pair a b) from fun _ _ h =>
    Nat.pair_lt_pair_left b h).monotone ha).trans
      ((show StrictMono (Nat.pair a') from fun _ _ h =>
        Nat.pair_lt_pair_right a' h).monotone hb)

private theorem fork_mono {a a' b b' : Nat} (ha : a≤a') (hb : b≤b') :
    forkCode a b≤forkCode a' b' :=
  Nat.add_le_add_right (pair_mono (Nat.add_le_add_right ha 1) hb) 1

private theorem atom_pos (n : Nat) : 1≤atomCode n := by
  change 1≤Nat.pair 0 n+1
  omega

private theorem variable_min (tag i j : Nat) :
    44≤variableCode tag i j :=
  (by decide : 44≤forkCode 1 (forkCode 1 1)).trans
    (fork_mono (atom_pos tag) (fork_mono (atom_pos i) (atom_pos j)))

private theorem connective_min (tag payload : Nat) (htag : 3≤tag) :
    44≤forkCode (atomCode tag) payload :=
  (by decide : 44≤forkCode (atomCode 3) 0).trans
    (fork_mono (Nat.add_le_add_right (pair_mono le_rfl htag) 1) (Nat.zero_le _))

/-- The bottom code 44 is a lower bound determined by the outer constructor;
no induction hypothesis about subformula codes is needed. -/
theorem formCode_ge (f : Form) : 44≤formCode f := by
  cases f with
  | fMem i j => exact variable_min 0 i j
  | fEq i j => exact variable_min 1 i j
  | fBot => decide
  | fImp a b => exact connective_min 3 _ (by decide)
  | fAnd a b => exact connective_min 4 _ (by decide)
  | fOr a b => exact connective_min 5 _ (by decide)
  | fAll a => exact connective_min 6 _ (by decide)
  | fEx a => exact connective_min 7 _ (by decide)

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

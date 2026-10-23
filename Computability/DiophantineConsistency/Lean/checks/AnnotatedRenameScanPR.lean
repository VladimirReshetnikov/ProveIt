import DiophantineConsistency.AnnotatedRenameScanPR

open SetTheory SetTheory.Form
open DiophantineConsistency
open AnnotatedProofCode AnnotatedRename AnnotatedRenameLocal AnnotatedRenameScan AnnotatedRenameScanPR

example (n : Nat) : Program.localProgram.val.eval n=Program.localInput n :=
  Program.localProgram.property n
example (n : Nat) : P.program.val.eval n=P.value n := P.program.property n
example (n : Nat) : optimizedProgram.val.eval n=P.value n := optimizedProgram.property n
example (mode k d i o c : Nat) : P.program.val.eval (inputCode mode k d i o c)=
    truth (checkCode mode k d i o c) := program_input mode k d i o c
example (f : Form) : ∃ c : Nat,P.program.val.eval
    (inputCode 0 0 0 (formCode f) (formCode (rename Nat.succ f)) c)=1 := by
  apply (exists_program_iff 0 0 0 f _).mpr
  simp only [renamed,index_shift]
example (f : Form) (k : Nat) : ∃ c : Nat,P.program.val.eval
    (inputCode 1 k 0 (formCode f) (formCode (rename (inst k) f)) c)=1 := by
  apply (exists_program_iff 1 k 0 f _).mpr
  simp only [renamed,index_inst 1 k (by decide)]

example : Program.localProgram.val.nodeCount=3119 := localProgram_nodeCount
example : Program.localProgram.optimize.val.nodeCount=2931 := optimizedLocalProgram_nodeCount
example : P.stepProgram.val.nodeCount=3223 := stepProgram_nodeCount
example : P.scannerProgram.val.nodeCount=3271 := scannerProgram_nodeCount
example : P.finishProgram.val.nodeCount=297 := finishProgram_nodeCount
example : P.program.val.nodeCount=3605 := program_nodeCount
example : optimizedProgram.val.nodeCount=3329 := optimizedProgram_nodeCount

#print axioms Program.bottom
#print axioms Program.binary
#print axioms Program.unary
#print axioms Program.localProgram
#print axioms P.stepProgram
#print axioms P.scannerProgram
#print axioms P.finishProgram
#print axioms P.program
#print axioms program_eq_checkCode
#print axioms program_primrec
#print axioms value_primrec
#print axioms program_input
#print axioms exists_program_iff
#print axioms program_nodeCount
#print axioms optimizedProgram_nodeCount

/- Only the tiny all-zero input is executed. The literal primitive-recursive
arithmetic deliberately has no efficient-runtime claim on large numeric codes. -/
#eval P.program.val.eval 0==0
#eval optimizedProgram.val.eval 0==0

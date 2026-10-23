import DiophantineConsistency.AnnotatedBoundScan

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedRename
open AnnotatedBoundScan

example (n : Nat) : P.program.val.eval n=P.value n := P.program.property n
example (f : Form) (out : Nat) :
    (∃ code,P.program.val.eval (inputCode (formCode f) out code)=1) ↔ out=bound f :=
  exists_program_iff f out
example (f : Form) (out : Nat) :
    (∃ code len,sealProgram.val.eval (sealInput (formCode f) out len code)=1) ↔
      out=formCode (sealF f) := exists_seal_program_iff f out
example (f : Form) : ∃ code len,sealProgram.val.eval
    (sealInput (formCode f) (formCode (sealF f)) len code)=1 :=
  (exists_seal_program_iff f _).mpr rfl

private def atomRow : Row := ⟨0,0,0,1,formCode (fMem 0 1),3⟩
private def allRow : Row := ⟨6,0,0,0,formCode (fAll (fMem 0 1)),3⟩
private def badRow : Row := ⟨6,0,1,0,formCode (fAll (fMem 0 1)),3⟩

/- Runtime controls use a supplied table-length bound. Canonical checkNat
uses numeric-code fuel, so nonempty gigantic-code runtime is not tested. -/
#eval finish (formCode (fAll (fMem 0 1))) 3
  (scan 2 (Nat.pair (tableCode [atomRow,allRow]) 0))==1
#eval finish (formCode (fAll (fMem 0 1))) 3
  (scan 2 (Nat.pair (tableCode [atomRow,badRow]) 0))==0
#eval finish (formCode (fAll (fMem 0 1))) 3
  (scan 1 (Nat.pair (tableCode [atomRow,allRow]) 0))==0
#eval P.program.val.eval 0==0
#eval optimizedProgram.val.eval 0==0
#eval sealProgram.val.eval 0==0

#print axioms AnnotatedBoundLocal.P.atomicProgram
#print axioms AnnotatedBoundLocal.P.bottomProgram
#print axioms AnnotatedBoundLocal.P.binaryProgram
#print axioms AnnotatedBoundLocal.P.unaryProgram
#print axioms AnnotatedBoundLocal.P.localProgram
#print axioms P.stepProgram
#print axioms P.scannerProgram
#print axioms P.finishProgram
#print axioms P.program
#print axioms checkNat_eq_checkCode
#print axioms program_input
#print axioms exists_program_iff
#print axioms program_primrec
#print axioms sealProgram
#print axioms sealProgram_input
#print axioms exists_seal_program_iff
#print axioms sealProgram_primrec

example : P.program.val.nodeCount=2095 := program_nodeCount
example : optimizedProgram.val.nodeCount=1807 := optimizedProgram_nodeCount
example : sealProgram.val.nodeCount=2279 := sealProgram_nodeCount
example : sealProgram.optimize.val.nodeCount=1983 := optimizedSealProgram_nodeCount
#print axioms localProgram_nodeCount
#print axioms optimizedLocalProgram_nodeCount
#print axioms stepProgram_nodeCount
#print axioms scannerProgram_nodeCount
#print axioms finishProgram_nodeCount
#print axioms program_nodeCount
#print axioms optimizedProgram_nodeCount
#print axioms sealProgram_nodeCount
#print axioms optimizedSealProgram_nodeCount

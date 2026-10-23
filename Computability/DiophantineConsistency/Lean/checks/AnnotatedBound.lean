import DiophantineConsistency.AnnotatedBound

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedRename
open AnnotatedBound

example (f : Form) : ∃ rows,AnnotatedBound.checkTable (formCode f) (bound f) rows=true :=
  AnnotatedBound.checkTable_complete f
example (f : Form) (n : Nat) :
    (∃ code,AnnotatedBound.checkCode (formCode f) n code=true) ↔ n=bound f :=
  AnnotatedBound.exists_code_iff f n
example (f : Form) (out : Nat) :
    (∃ table length,checkSeal (formCode f) out table length=true) ↔
      out=formCode (sealF f) := exists_seal_iff f out

private def atomRow : Row := ⟨0,0,0,1,formCode (fMem 0 1),3⟩
private def allRow : Row := ⟨6,0,0,0,formCode (fAll (fMem 0 1)),3⟩
private def badAll : Row := ⟨6,0,0,0,formCode (fAll (fMem 0 1)),2⟩
private def badRef : Row := ⟨6,0,1,0,formCode (fAll (fMem 0 1)),3⟩
private def badTag : Row := ⟨8,0,0,0,formCode fBot,0⟩
private def eqRow : Row := ⟨1,0,2,4,formCode (fEq 2 4),8⟩
private def botRow : Row := ⟨2,0,0,0,formCode fBot,0⟩
private def andRow : Row := ⟨4,0,1,0,formCode (fAnd (fMem 0 1) (fEq 2 4)),11⟩
private def exRow : Row := ⟨7,0,0,0,formCode (fEx (fMem 0 1)),3⟩

#eval AnnotatedBound.checkTable (formCode (fMem 0 1)) 3 [atomRow]
#eval AnnotatedBound.checkTable (formCode (fAll (fMem 0 1))) 3 [atomRow,allRow]
#eval !(AnnotatedBound.checkTable (formCode (fAll (fMem 0 1))) 2 [atomRow,badAll])
#eval !(AnnotatedBound.checkTable (formCode (fAll (fMem 0 1))) 3 [atomRow,badRef])
#eval !(AnnotatedBound.checkTable (formCode fBot) 0 [badTag])
#eval checkSeal (formCode (fMem 0 1)) (formCode (sealF (fMem 0 1)))
  (tableCode [atomRow]) 3
#eval !(checkSeal (formCode (fMem 0 1)) (formCode (sealF (fMem 0 1)))
  (tableCode [atomRow]) 2)
#eval AnnotatedBound.checkTable (formCode (fEq 2 4)) 8 [eqRow]
#eval AnnotatedBound.checkTable (formCode fBot) 0 [botRow]
#eval AnnotatedBound.checkTable (formCode (fAnd (fMem 0 1) (fEq 2 4))) 11 [atomRow,eqRow,andRow]
#eval AnnotatedBound.checkTable (formCode (fEx (fMem 0 1))) 3 [atomRow,exRow]

#print axioms atomicEquations
#print axioms Good
#print axioms row_sound
#print axioms ready
#print axioms AnnotatedBound.checkTable_sound
#print axioms AnnotatedBound.checkTable_complete
#print axioms AnnotatedBound.checkCode_sound
#print axioms AnnotatedBound.exists_code_iff
#print axioms checkSeal
#print axioms exists_seal_iff

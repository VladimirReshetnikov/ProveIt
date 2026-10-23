import DiophantineConsistency.AnnotatedClosure

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedClosure

example (f : Form) (n : Nat) : closeCode (formCode f) n=formCode (closeN n f) :=
  closeCode_formCode f n
example (f : Form) : program.val.eval (Nat.pair (formCode f) (bound f))=formCode (sealF f) :=
  program_sealF f
example (f : Form) : quadraticProgram.val.eval (Nat.pair (formCode f) (bound f))=
    formCode (sealF f) := quadraticProgram_sealF f
example (f : Form) : 44≤formCode f := formCode_ge f
example (f : Form) : formCode (fAll f)=formCode f*formCode f+39 := code_all_quadratic f

#print axioms closeCode
#print axioms program
#print axioms closeCode_formCode
#print axioms program_sealF
#print axioms program_primrec
#print axioms formCode_ge
#print axioms code_all_quadratic
#print axioms closeQuadratic_formCode
#print axioms quadraticProgram
#print axioms quadraticProgram_sealF

#eval closeCode (formCode fBot) 0==formCode fBot
#eval closeCode (formCode fBot) 2==formCode (fAll (fAll fBot))
#eval closeQuadratic (formCode (fMem 0 1)) 3==closeCode (formCode (fMem 0 1)) 3
example : program.val.nodeCount=37 := program_nodeCount
example : quadraticProgram.val.nodeCount=119 := quadraticProgram_nodeCount
#print axioms program_nodeCount
#print axioms quadraticProgram_nodeCount

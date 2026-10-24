import DiophantineConsistency.AnnotatedAssumption

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedContext AnnotatedAssumption

example (G : List Form) (f : Form) :
    (∃ shifted e i,program.val.eval
      (AnnotatedAssumption.inputCode (contextCode G) (formCode f) shifted e i)=1) ↔ f∈G :=
  exists_program_iff G f
example (G : List Form) (f : Form) :
    (∃ shifted e i,program.val.eval
      (AnnotatedAssumption.inputCode (contextCode G) (formCode f) shifted e i)=1) ↔
        (AnnotatedProofChecker.Line.mk (.ass G f) []).valid []=true :=
  exists_program_iff_line G f
example (f : Form) : ¬∃ shifted e i,program.val.eval
    (AnnotatedAssumption.inputCode (contextCode []) (formCode f) shifted e i)=1 := by
  rw [exists_program_iff]
  simp

#eval program.val.eval 0==0
#eval optimizedProgram.val.eval 0==0

#print axioms value
#print axioms program
#print axioms program_input
#print axioms program_sound
#print axioms exists_program_iff
#print axioms exists_program_iff_line
#print axioms program_provable
#print axioms program_primrec

example : program.val.nodeCount=4753 := program_nodeCount
example : optimizedProgram.val.nodeCount=4391 := optimizedProgram_nodeCount
#print axioms program_nodeCount
#print axioms optimizedProgram_nodeCount

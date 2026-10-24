import DiophantineConsistency.AnnotatedContextPR

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedContext AnnotatedContextPR

example (n : Nat) : P.program.val.eval n=P.value n := P.program.property n
example (i o e : Nat) (h : P.program.val.eval (inputCode i o e)=1) :
    ∃ G : List Form,i=contextCode G ∧ o=contextCode (G.map (rename Nat.succ)) :=
  program_sound i o e h
example (G : List Form) (o : Nat) :
    (∃ e,P.program.val.eval (inputCode (contextCode G) o e)=1) ↔
      o=contextCode (G.map (rename Nat.succ)) := exists_program_iff G o

#eval P.program.val.eval 0==0
#eval P.program.val.eval (inputCode 1 1 0)==1
#eval optimizedProgram.val.eval (inputCode 1 1 0)==1

#print axioms P.localProgram
#print axioms P.stepProgram
#print axioms P.scannerProgram
#print axioms P.finishProgram
#print axioms P.program
#print axioms program_input
#print axioms program_sound
#print axioms exists_program_iff
#print axioms program_primrec

example : P.program.val.nodeCount=4177 := program_nodeCount
example : optimizedProgram.val.nodeCount=3855 := optimizedProgram_nodeCount
#print axioms localProgram_nodeCount
#print axioms stepProgram_nodeCount
#print axioms scannerProgram_nodeCount
#print axioms finishProgram_nodeCount
#print axioms program_nodeCount
#print axioms optimizedProgram_nodeCount

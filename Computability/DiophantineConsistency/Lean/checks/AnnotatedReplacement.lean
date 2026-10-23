import DiophantineConsistency.AnnotatedReplacement

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedReplacement

example (n : Nat) : program.val.eval n=value n := program.property n
example (f : Form) (goal : Nat) :
    (∃ a b c e1 e2 e3 len table,program.val.eval
      (inputCode (formCode f) goal a b c e1 e2 e3 len table)=1) ↔
        goal=formCode (sealF (Repl_form f)) := exists_program_iff f goal
example (f : Form) : ∃ a b c e1 e2 e3 len table,program.val.eval
    (inputCode (formCode f) (formCode (sealF (Repl_form f))) a b c e1 e2 e3 len table)=1 :=
  (exists_program_iff f _).mpr rfl
example (arg goal a b c e1 e2 e3 len table : Nat)
    (h : program.val.eval (inputCode arg goal a b c e1 e2 e3 len table)=1) :
    ∃ f : Form,arg=formCode f ∧ goal=formCode (sealF (Repl_form f)) :=
  program_sound arg goal a b c e1 e2 e3 len table h

#print axioms inputCode
#print axioms value
#print axioms program
#print axioms program_input
#print axioms exists_program_iff
#print axioms program_sound
#print axioms program_primrec

example : program.val.nodeCount=25535 := program_nodeCount
example : program.optimize.val.nodeCount=23463 := optimizedProgram_nodeCount
#print axioms program_nodeCount
#print axioms optimizedProgram_nodeCount
#print axioms program_axiom

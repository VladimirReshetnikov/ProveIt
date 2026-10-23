import DiophantineConsistency.AnnotatedSchema

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedSchema

example (f : Form) : (formulaProgram f).val.eval 0 = formCode f := (formulaProgram f).property 0
example (f : Form) (goal : Nat) :
    (∃ renamed e len table,separationProgram.val.eval
      (separationInput (formCode f) goal renamed e len table)=1) ↔
        goal=formCode (sealF (Sep_form f)) := exists_separation_program_iff f goal
example (argument goal renamed e len table : Nat)
    (h : separationProgram.val.eval (separationInput argument goal renamed e len table)=1) :
    ∃ f : Form,argument=formCode f ∧ goal=formCode (sealF (Sep_form f)) :=
  separationProgram_sound argument goal renamed e len table h

#eval separationBody (formCode (rename rsep fBot))==formCode (Sep_form fBot)
#eval replacementBody (formCode (rename rf1 fBot)) (formCode (rename rf2 fBot))
  (formCode (rename ri fBot))==formCode (Repl_form fBot)
#eval separationBodyProgram.val.eval (formCode fBot)==separationBody (formCode fBot)
#eval replacementBodyProgram.val.eval (Nat.pair (formCode fBot)
  (Nat.pair (formCode fBot) (formCode fBot)))==
    replacementBody (formCode fBot) (formCode fBot) (formCode fBot)
#eval (formulaProgram (fAll (fMem 0 2))).val.eval 0==formCode (fAll (fMem 0 2))

#print axioms separationBody
#print axioms replacementBody
#print axioms separationBody_formCode
#print axioms replacementBody_formCode
#print axioms formulaProgram
#print axioms separationBodyProgram
#print axioms replacementBodyProgram
#print axioms separationProgram
#print axioms separationProgram_input
#print axioms exists_separation_program_iff
#print axioms separationProgram_sound
#print axioms separationProgram_primrec

example : separationBodyProgram.val.nodeCount=461 := separationBodyProgram_nodeCount
example : replacementBodyProgram.val.nodeCount=773 := replacementBodyProgram_nodeCount
example : separationProgram.val.nodeCount=10241 := separationProgram_nodeCount
example : separationProgram.optimize.val.nodeCount=9333 := optimizedSeparationProgram_nodeCount
#print axioms separationBodyProgram_nodeCount
#print axioms replacementBodyProgram_nodeCount
#print axioms separationProgram_nodeCount
#print axioms optimizedSeparationProgram_nodeCount
#print axioms separationProgram_axiom

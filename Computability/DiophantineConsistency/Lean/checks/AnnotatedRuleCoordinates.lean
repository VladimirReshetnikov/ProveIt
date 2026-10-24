import DiophantineConsistency.AnnotatedRuleCoordinates

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedRuleCoordinates

example (r : Coordinates) : AnnotatedRuleCoordinates.decode (encode r)=r := decode_encode r
example (n : Nat) (h : P.program.val.eval n=1) : Good (AnnotatedRuleCoordinates.decode n.unpair.1) :=
  program_sound n h
example (G : List Form) (a b c : Form) (i j : Nat) :
    ∃ evidence,P.program.val.eval (Nat.pair (encode (quote G a b c i j)) evidence)=1 := by
  apply (exists_program_iff _).mpr
  exact ⟨G,a,b,c,rfl⟩
example (r : Coordinates) (e : AnnotatedRename.Row) (h : check r e=1) :
    ∃ G : List Form,∃ a b c : Form,r=quote G a b c r.i r.j := check_sound r e h

#eval P.program.val.eval 0==0
#eval optimizedProgram.val.eval 0==0
example : P.program.val.nodeCount=17371 := program_nodeCount
example : optimizedProgram.val.nodeCount=15933 := optimizedProgram_nodeCount

#print axioms encode
#print axioms AnnotatedRuleCoordinates.decode
#print axioms quote
#print axioms check
#print axioms check_sound
#print axioms check_complete
#print axioms P.renameProgram
#print axioms P.boundProgram
#print axioms P.contextProgram
#print axioms P.bProgram
#print axioms P.iProgram
#print axioms P.jProgram
#print axioms P.cProgram
#print axioms P.program
#print axioms program_input
#print axioms program_sound
#print axioms exists_program_iff
#print axioms program_primrec
#print axioms program_nodeCount
#print axioms optimizedProgram_nodeCount

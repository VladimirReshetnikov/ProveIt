import DiophantineConsistency.AnnotatedRuleSchedules

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedRuleSchedules

example (tag : Fin 17) (G : List Form) (a b c : Form) (i j : Nat) :
    outputCode tag.val (AnnotatedRuleCoordinates.quote G a b c i j)=
      judgmentCode (rule tag G a b c i j).output := output_quote tag G a b c i j
example (tag : Fin 17) (G : List Form) (a b c : Form) (i j : Nat) :
    premiseBodies tag.val (AnnotatedRuleCoordinates.quote G a b c i j)=
      (rule tag G a b c i j).premises.map judgmentCode := premises_quote tag G a b c i j
example (original : AnnotatedProofChecker.Rule) :
    ∃ coordinates evidence : Nat,
      AnnotatedRuleCoordinates.P.program.val.eval (Nat.pair coordinates evidence)=1 ∧
      P.outputProgram.val.eval (Nat.pair (ofRule original).1.val coordinates)=
        judgmentCode original.output ∧
      P.premiseProgram.val.eval (Nat.pair (ofRule original).1.val coordinates)=
        listCode (original.premises.map judgmentCode) := programs_complete original

private def r := AnnotatedRuleCoordinates.quote [] (fMem 0 0) (fEq 0 1) fBot 1 2
#eval (List.range 17).map (fun tag => (premiseBodies tag r).length)==
  [0,1,2,1,0,2,1,1,1,1,3,1,1,1,2,0,2]
#eval (List.range 17).all (fun tag =>
  P.outputProgram.val.eval (Nat.pair tag (AnnotatedRuleCoordinates.encode r))==outputCode tag r)
#eval (List.range 17).all (fun tag =>
  P.premiseProgram.val.eval (Nat.pair tag (AnnotatedRuleCoordinates.encode r))==premiseCode tag r)
#eval P.outputProgram.val.eval (Nat.pair 17 0)==0
#eval P.premiseProgram.val.eval (Nat.pair 99 0)==0
#eval tagProgram.val.eval 16==1
#eval tagProgram.val.eval 17==0

example : P.outputProgram.val.nodeCount=2537 := outputProgram_nodeCount
example : P.outputProgram.optimize.val.nodeCount=2377 := optimizedOutputProgram_nodeCount
example : P.premiseProgram.val.nodeCount=2683 := premiseProgram_nodeCount
example : P.premiseProgram.optimize.val.nodeCount=2483 := optimizedPremiseProgram_nodeCount

#print axioms rule
#print axioms outputBody
#print axioms premiseBodies
#print axioms tagProgram
#print axioms tagValue_eq_one
#print axioms output_quote
#print axioms premises_quote
#print axioms schedules_sound
#print axioms ofRule
#print axioms ofRule_good
#print axioms ofRule_output
#print axioms ofRule_premises
#print axioms P.outputBodyProgram
#print axioms P.premiseBodyProgram
#print axioms P.outputProgram
#print axioms P.premiseProgram
#print axioms outputProgram_input
#print axioms premiseProgram_input
#print axioms outputProgram_primrec
#print axioms premiseProgram_primrec
#print axioms programs_sound
#print axioms programs_complete
#print axioms outputProgram_nodeCount
#print axioms optimizedOutputProgram_nodeCount
#print axioms premiseProgram_nodeCount
#print axioms optimizedPremiseProgram_nodeCount

import DiophantineConsistency.AnnotatedClosureGraphs

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedClosureGraphs

example : quadraticStep.witnessCount=0 := quadraticStep_witnessCount
example (f : Form) : formCode (fAll f)=formCode f*formCode f+39 :=
  AnnotatedClosure.code_all_quadratic f
#print axioms quadraticStep
#print axioms quadraticStep_witnessCount

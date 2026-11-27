import DiophantineConsistency.AnnotatedConstructorTemplates

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedRename AnnotatedTemplateSyntax AnnotatedConstructorTemplates

example (f : Form) : value separation ![formCode (rename rsep f)]=formCode (Sep_form f) :=
  separation_actual f
example (f : Form) :
    value replacement ![formCode (rename rf1 f),formCode (rename rf2 f),formCode (rename ri f)]=
      formCode (Repl_form f) := replacement_actual f
example (x : Fin 3 → Nat) :
    value replacement x=AnnotatedSchema.replacementBody (x 0) (x 1) (x 2) := replacement_eq x
example (G : List Form) (f : Form) :
    value judgment ![AnnotatedContext.contextCode G,formCode f]=AnnotatedCodeArithmetic.judgmentCode ⟨G,f⟩ :=
  judgment_actual G f
example : replacementGraph.witnessCount=136 := replacementGraph_witnessCount
example : replacementGraph.expression.toPolynomial.totalDegree≤4 := replacementGraph_degree
example : separationGraph.witnessCount=84 := separationGraph_witnessCount
example : separationGraph.expression.toPolynomial.totalDegree≤4 := separationGraph_degree

#eval value contextCons ![0,0]==forkCode 0 0
#eval value membership ![0,1]==formCode (fMem 0 1)
#eval value equality ![1,2]==formCode (fEq 1 2)
#eval value reflexivity ![2]==formCode (fEq 2 2)
#eval value taggedVariable ![1,2,3]==variableCode 1 2 3
#eval value taggedBinary ![3,0,0]==binaryCode 3 0 0
#eval value separation ![0]==AnnotatedSchema.separationBody 0
#eval value functionBody ![0,1]==AnnotatedSchema.functionBody 0 1
#eval value imageBody ![0]==AnnotatedSchema.imageBody 0
#eval value replacement ![0,1,2]==AnnotatedSchema.replacementBody 0 1 2

#print axioms binary
#print axioms unary
#print axioms dynamicVariable
#print axioms value_dynamicVariable
#print axioms contextCons_actual
#print axioms judgment_actual
#print axioms separation
#print axioms replacement
#print axioms separation_eq
#print axioms functionBody_eq
#print axioms imageBody_eq
#print axioms replacement_eq
#print axioms separation_actual
#print axioms replacement_actual
#print axioms separationGraph
#print axioms functionGraph
#print axioms imageGraph
#print axioms replacementGraph
#print axioms template_widths
#print axioms separationGraph_witnessCount
#print axioms functionGraph_witnessCount
#print axioms imageGraph_witnessCount
#print axioms replacementGraph_witnessCount
#print axioms separationGraph_degree
#print axioms functionGraph_degree
#print axioms imageGraph_degree
#print axioms replacementGraph_degree

import DiophantineConsistency.AnnotatedRuleSide

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedRuleSide
open AnnotatedRuleCoordinates (quote)

example (original : AnnotatedProofChecker.Rule) :
    (∃ index,value (AnnotatedRuleSchedules.ofRule original).1.val
      (AnnotatedRuleSchedules.ofRule original).2 index=1) ↔ original.side=true :=
  exists_ofRule_iff original
example (tag : Fin 17) (G : List Form) (a b c : Form) (i j index : Nat)
    (h : value tag.val (quote G a b c i j) index=1) :
    (AnnotatedRuleSchedules.rule tag G a b c i j).side=true :=
  quote_sound tag G a b c i j index h

#eval value 0 (quote [fBot] fBot fBot fBot 0 0) 0==1
#eval value 0 (quote [] fBot fBot fBot 0 0) 0==0
#eval value 0 (quote [fBot] fBot fBot fBot 0 0) 1==0
#eval value 1 (quote [] fBot fBot fBot 0 0) 0==1
#eval P.program.val.eval (Nat.pair 1 0)==1
example : P.program.val.nodeCount=597 := by decide
example : P.program.optimize.val.nodeCount=573 := by decide

#print axioms value
#print axioms exists_quote_iff
#print axioms quote_sound
#print axioms exists_ofRule_iff
#print axioms P.program
#print axioms program_input
#print axioms program_primrec

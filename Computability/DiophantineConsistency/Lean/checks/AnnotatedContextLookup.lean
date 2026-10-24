import DiophantineConsistency.AnnotatedContextLookup

open SetTheory SetTheory.Form DiophantineConsistency
open AnnotatedProofCode AnnotatedContext AnnotatedContextLookup

example (G : List Form) (i : Nat) (f : Form) :
    referenceValue (Nat.pair (contextCode G) (Nat.pair i (formCode f)))=1 ↔ G[i]?=some f :=
  reference_context G i f
example (G : List Form) (i c : Nat)
    (h : referenceValue (Nat.pair (contextCode G) (Nat.pair i c))=1) :
    ∃ f : Form,G[i]?=some f ∧ c=formCode f := reference_raw G i c h

#eval lookup (contextCode []) 0==0
#eval lookup (contextCode [fBot,fMem 0 0]) 0==formCode fBot+1
#eval lookup (contextCode [fBot,fMem 0 0]) 1==formCode (fMem 0 0)+1
#eval lookup (contextCode [fBot,fMem 0 0]) 2==0
#eval referenceValue (Nat.pair (contextCode []) (Nat.pair 0 (formCode fBot)))==0
#eval referenceProgram.val.eval (Nat.pair (contextCode []) (Nat.pair 0 0))==0

#print axioms headProgram
#print axioms tailProgram
#print axioms dropProgram
#print axioms lookupProgram
#print axioms lookup_contextCode
#print axioms referenceProgram
#print axioms reference_raw
#print axioms reference_context
#print axioms lookupProgram_primrec

example : lookupProgram.val.nodeCount=207 := lookupProgram_nodeCount
example : referenceProgram.val.nodeCount=501 := referenceProgram_nodeCount
example : referenceProgram.optimize.val.nodeCount=485 := optimizedReferenceProgram_nodeCount
#print axioms lookupProgram_nodeCount
#print axioms referenceProgram_nodeCount
#print axioms optimizedReferenceProgram_nodeCount

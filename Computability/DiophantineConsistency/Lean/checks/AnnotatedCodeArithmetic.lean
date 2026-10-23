import DiophantineConsistency.AnnotatedCodeArithmetic

open SetTheory SetTheory.Form
open DiophantineConsistency
open AnnotatedProofChecker AnnotatedProofCode AnnotatedCodeArithmetic

/- A zero history value is present, whereas nil and an out-of-range index
are absent. Guarding the head is necessary for this distinction. -/
example : lookup (listCode [0,4]) 0=1 := by
  rw [lookup_listCode]
  rfl
example : lookup (listCode [0,4]) 1=5 := by
  rw [lookup_listCode]
  rfl
example : lookup (listCode [0,4]) 2=0 := by
  rw [lookup_listCode]
  rfl
example : lookup (listCode []) 0=0 := by
  rw [lookup_listCode]
  rfl
example : referenceCheck (Nat.pair (listCode [0,4]) (Nat.pair 0 0))=1 :=
  (referenceCheck_listCode [0,4] 0 0).mpr rfl
example : referenceCheck (Nat.pair (listCode [0,4]) (Nat.pair 2 0))≠1 := by
  simp only [ne_eq,referenceCheck_listCode]
  decide

private def goal : Judgment := ⟨[],fEq 0 0⟩
private def wrongContext : Judgment := ⟨[fBot],fEq 0 0⟩
private def wrongFormula : Judgment := ⟨[],fEq 0 1⟩
example : referenceCheck (Nat.pair (listCode ([goal].map judgmentCode))
    (Nat.pair 0 (judgmentCode goal)))=1 :=
  (referenceCheck_judgments [goal] 0 goal).mpr rfl
example : referenceCheck (Nat.pair (listCode ([goal].map judgmentCode))
    (Nat.pair 0 (judgmentCode wrongContext)))≠1 := by
  simp only [ne_eq,referenceCheck_judgments]
  decide
example : referenceCheck (Nat.pair (listCode ([goal].map judgmentCode))
    (Nat.pair 0 (judgmentCode wrongFormula)))≠1 := by
  simp only [ne_eq,referenceCheck_judgments]
  decide

example : treeKindProgram.val.nodeCount=45 := by decide
example : atomConstructor.val.nodeCount=7 := by decide
example : forkConstructor.val.nodeCount=7 := by decide
example : listHeadProgram.val.nodeCount=31 := by decide
example : listTailProgram.val.nodeCount=29 := by decide
example : dropProgram.val.nodeCount=37 := by decide
example : lookupProgram.val.nodeCount=69 := lookupProgram_nodeCount
example : referenceProgram.val.nodeCount=225 := referenceProgram_nodeCount
example : optimizedReferenceProgram.val.nodeCount=209 := optimizedReferenceProgram_nodeCount

example (n : Nat) : referenceProgram.val.eval n=referenceCheck n := referenceProgram.property n
example (n : Nat) : optimizedReferenceProgram.val.eval n=referenceCheck n :=
  optimizedReferenceProgram.property n

#print axioms treeKindProgram
#print axioms atomConstructor
#print axioms forkConstructor
#print axioms dropProgram
#print axioms lookupProgram
#print axioms referenceProgram
#print axioms lookup_listCode
#print axioms referenceCheck_listCode
#print axioms judgmentCode_injective
#print axioms referenceCheck_judgments
#print axioms referenceProgram_primrec
#print axioms lookupProgram_nodeCount
#print axioms referenceProgram_nodeCount
#print axioms optimizedReferenceProgram_nodeCount

/- Runtime controls execute supplied program data, including their recursive
lookup/guard branches. Every result is a tiny natural. -/
#eval lookupProgram.val.eval (Nat.pair (listCode [0,4]) 0)==1
#eval lookupProgram.val.eval (Nat.pair (listCode [0,4]) 2)==0
#eval optimizedReferenceProgram.val.eval (Nat.pair (listCode [0,4]) (Nat.pair 0 0))==1
#eval optimizedReferenceProgram.val.eval (Nat.pair (listCode [0,4]) (Nat.pair 2 0))==0

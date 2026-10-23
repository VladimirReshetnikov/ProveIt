import DiophantineConsistency.AnnotatedCodeGraphs

open DiophantineConsistency
open AnnotatedCodeGraphs

private def values (n out : ℤ) : Option (Fin 1) ⊕ Fin 0 → ℤ
  | .inl none => out
  | .inl (some _) => n
  | .inr i => Fin.elim0 i

/- These reduce the actual supplied zero-witness polynomial expressions,
including both small natural predecessor branches. -/
example : predecessor.expression.eval (values 0 0)=0 := by decide
example : predecessor.expression.eval (values 1 0)=0 := by decide
example : predecessor.expression.eval (values 9 8)=0 := by decide
example : predecessor.expression.eval (values 2 0)=4 := by decide
example : predecessor.expression.eval (values 0 1)=4 := by decide
example : atomConstructor.expression.eval (values 3 10)=0 := by decide
example : atomConstructor.expression.eval (values 3 11)=1 := by decide

example (v : Option (Fin 1) → ℕ) :
    v none=(v (some 0)).pred ↔
      ∃ w : Fin predecessor.witnessCount → ℕ,
        predecessor.expression.eval (natAssignment v w)=0 := predecessor.correct v
example (v : Option (Fin 1) → ℕ) :
    v none=AnnotatedCodeArithmetic.treeKind (v (some 0)) ↔
      ∃ w : Fin treeKind.witnessCount → ℕ,
        treeKind.expression.eval (natAssignment v w)=0 := treeKind.correct v

example : predecessor.witnessCount=0 := predecessor_witnessCount
example : treeLeft.witnessCount=4 := treeLeft_witnessCount
example : treeRight.witnessCount=4 := treeRight_witnessCount
example : treeLeftChild.witnessCount=5 := treeLeftChild_witnessCount
example : treeKind.witnessCount=14 := treeKind_witnessCount
example : listHead.witnessCount=11 := listHead_witnessCount
example : listTail.witnessCount=9 := listTail_witnessCount
example : atomConstructor.witnessCount=0 := atomConstructor_witnessCount
example : forkConstructor.witnessCount=8 := forkConstructor_witnessCount

#print axioms predecessor
#print axioms treeLeft
#print axioms treeRight
#print axioms treeLeftChild
#print axioms treeKind
#print axioms listHead
#print axioms listTail
#print axioms atomConstructor
#print axioms forkConstructor
#print axioms predecessor_witnessCount
#print axioms treeLeft_witnessCount
#print axioms treeKind_witnessCount
#print axioms listHead_witnessCount
#print axioms listTail_witnessCount
#print axioms forkConstructor_witnessCount

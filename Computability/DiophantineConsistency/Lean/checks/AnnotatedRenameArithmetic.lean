import DiophantineConsistency.AnnotatedRenameArithmetic

open DiophantineConsistency
open AnnotatedRename AnnotatedRenameArithmetic

example (n : Nat) : indexProgram.val.eval n=indexInput n := indexProgram.property n
example (n : Nat) : binaryProgram.val.eval n=
    binaryCode n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 := binaryProgram.property n
example (n : Nat) : variableProgram.val.eval n=
    variableCode n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2 := variableProgram.property n
example (n : Nat) : unaryProgram.val.eval n=unaryCode n.unpair.1 n.unpair.2 := unaryProgram.property n

#print axioms indexProgram
#print axioms binaryProgram
#print axioms variableProgram
#print axioms unaryProgram

/- Each runtime input packages `(mode,(k,(depth,index)))`. -/
#eval indexProgram.val.eval (Nat.pair 1 (Nat.pair 3 (Nat.pair 1 0)))==0
#eval indexProgram.val.eval (Nat.pair 1 (Nat.pair 3 (Nat.pair 1 1)))==4
#eval indexProgram.val.eval (Nat.pair 1 (Nat.pair 3 (Nat.pair 1 2)))==1
#eval indexProgram.val.eval (Nat.pair 0 (Nat.pair 0 (Nat.pair 2 2)))==3
#eval indexProgram.val.nodeCount
#eval indexProgram.optimize.val.nodeCount
#eval binaryProgram.val.nodeCount
#eval variableProgram.val.nodeCount
#eval unaryProgram.val.nodeCount

example (n : Nat) : atomicProgram.val.eval n=1 ↔
    atomicEquations n.unpair.1 n.unpair.2.unpair.1 (decodeRow n.unpair.2.unpair.2)=true := by
  rw [atomicProgram.property]
  exact atomicInput_correct n

#print axioms atomicProgram
#print axioms atomicInput_correct
#eval atomicProgram.val.nodeCount
#eval atomicProgram.optimize.val.nodeCount

private def small : Row := ⟨0,0,0,0,variableCode 0 0 0,variableCode 0 1 1⟩
#eval atomicProgram.val.eval (Nat.pair 0 (Nat.pair 0 (rowCode small)))==1
#eval atomicProgram.val.eval (Nat.pair 0 (Nat.pair 0 (rowCode {small with output:=0})))==0

example : indexProgram.val.nodeCount=177 := indexProgram_nodeCount
example : optimizedIndexProgram.val.nodeCount=161 := optimizedIndexProgram_nodeCount
example : binaryProgram.val.nodeCount=33 := binaryProgram_nodeCount
example : variableProgram.val.nodeCount=49 := variableProgram_nodeCount
example : unaryProgram.val.nodeCount=19 := unaryProgram_nodeCount
example : atomicProgram.val.nodeCount=1215 := atomicProgram_nodeCount
example : optimizedAtomicProgram.val.nodeCount=1151 := optimizedAtomicProgram_nodeCount
#print axioms atomicProgram_correct
#print axioms optimizedAtomicProgram_nodeCount

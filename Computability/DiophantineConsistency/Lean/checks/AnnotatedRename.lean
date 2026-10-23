import DiophantineConsistency.AnnotatedRenameCode

open SetTheory SetTheory.Form
open DiophantineConsistency.AnnotatedProofCode
open DiophantineConsistency.AnnotatedRename

/- Binder-edge arithmetic: bound variables stay fixed, the substituted free
variable is lifted, and indices above it are decremented. -/
example : index 1 3 1 0=0 := by decide
example : index 1 3 1 1=4 := by decide
example : index 1 3 1 2=1 := by decide
example : index 0 0 2 0=0 := by decide
example : index 0 0 2 1=1 := by decide
example : index 0 0 2 2=3 := by decide
example : index 1 3 2 2=5 := by decide
example : index 1 3 2 3=2 := by decide

private def child : Row := ⟨1,1,0,1,formCode (fEq 0 1),formCode (fEq 0 4)⟩
private def parent : Row :=
  ⟨6,0,0,0,formCode (fAll (fEq 0 1)),formCode (fAll (fEq 0 4))⟩

example : child.valid 1 3 []=true := by
  simp [Row.valid,child,atomicEquations,index]
example : parent.valid 1 3 [child]=true := by
  simp [Row.valid,parent,child,unaryAt,unaryEquations]
example : ({parent with first:=1}).valid 1 3 [child]=false := by
  simp [Row.valid,parent,unaryAt]
example : parent.valid 1 3 [{child with depth:=0}]=false := by
  simp [Row.valid,parent,child,unaryAt,unaryEquations]
example : parent.valid 1 3 []=false := by
  simp [Row.valid,parent,unaryAt]
example : ({parent with tag:=8}).valid 1 3 [child]=false := by
  simp [Row.valid]
example : ({parent with second:=1}).valid 1 3 [child]=false := by
  simp [Row.valid,parent,child,unaryAt,unaryEquations]

example : checkTable 1 3 0 (formCode (fAll (fEq 0 1)))
    (formCode (fAll (fEq 0 4))) [child,parent]=true := by
  simp [checkTable,run,Row.valid,parent,child,unaryAt,unaryEquations,atomicEquations,index]
example : checkTable 1 3 0 (formCode (fAll (fEq 0 1)))
    (formCode (fAll (fEq 0 4))) [parent,child]=false := by
  simp [checkTable,run,Row.valid,parent,unaryAt]

example (r : Row) : decodeRow (rowCode r)=r := decodeRow_rowCode r
example (rows : List Row) : decodeTable rows.length (tableCode rows)=some rows :=
  decodeTable_tableCode rows rows.length (Nat.le_refl _)
example : decodeTable 0 (tableCode [child])=none := by
  simp [tableCode,DiophantineConsistency.AnnotatedCodeArithmetic.listCode,decodeTable]
example (rows : List Row) : checkCode 1 3 0 (formCode (fAll (fEq 0 1)))
    (formCode (fAll (fEq 0 4))) (tableCode rows)=
      checkTable 1 3 0 (formCode (fAll (fEq 0 1))) (formCode (fAll (fEq 0 4))) rows :=
  checkCode_tableCode _ _ _ _ _ rows
example (f : Form) : ∃ code : Nat,
    checkCode 0 0 0 (formCode f) (formCode (rename Nat.succ f)) code=true :=
  (exists_shift_code_iff f _).mpr rfl
example (f : Form) (k : Nat) : ∃ code : Nat,
    checkCode 1 k 0 (formCode f) (formCode (rename (inst k) f)) code=true :=
  (exists_inst_code_iff k f _).mpr rfl

#print axioms index_up
#print axioms atomicEquations
#print axioms binaryEquations
#print axioms unaryEquations
#print axioms Row.valid
#print axioms Row.sound
#print axioms run_sound
#print axioms ready
#print axioms checkTable_sound
#print axioms checkTable_complete
#print axioms exists_table_iff
#print axioms rowCode
#print axioms decodeRow
#print axioms decodeRow_rowCode
#print axioms decodeTable
#print axioms decodeTable_tableCode
#print axioms checkCode
#print axioms checkCode_sound
#print axioms exists_code_iff
#print axioms exists_shift_code_iff
#print axioms exists_inst_code_iff

private def sharedChild : Row := ⟨1,0,0,0,formCode (fEq 0 0),formCode (fEq 1 1)⟩
private def sharedParent : Row := ⟨4,0,0,0,
  formCode (fAnd (fEq 0 0) (fEq 0 0)),formCode (fAnd (fEq 1 1) (fEq 1 1))⟩
example : sharedParent.valid 0 0 [sharedChild]=true := by
  simp [Row.valid,sharedParent,sharedChild,binaryAt,binaryEquations]
example : sharedParent.valid 0 0 [{sharedChild with depth:=1}]=false := by
  simp [Row.valid,sharedParent,sharedChild,binaryAt,binaryEquations]

/- Runtime controls execute the numeric table parser and local validator. -/
#eval checkCode 1 3 0 (formCode (fAll (fEq 0 1))) (formCode (fAll (fEq 0 4)))
  (tableCode [child,parent])==true
#eval checkCode 1 3 0 (formCode (fAll (fEq 0 1))) (formCode (fAll (fEq 0 4)))
  (tableCode [{child with depth:=0},parent])==false
#eval checkCode 1 3 0 (formCode (fAll (fEq 0 1))) (formCode (fAll (fEq 0 4)))
  (tableCode [child,{parent with first:=1}])==false

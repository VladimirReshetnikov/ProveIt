import DiophantineConsistency.AnnotatedRenameScan

open SetTheory SetTheory.Form
open DiophantineConsistency
open AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedRename AnnotatedRenameLocal AnnotatedRenameScan

private def child : Row := ⟨1,0,0,0,formCode (fEq 0 0),formCode (fEq 1 1)⟩
private def parent : Row := ⟨4,0,0,0,
  formCode (fAnd (fEq 0 0) (fEq 0 0)),formCode (fAnd (fEq 1 1) (fEq 1 1))⟩

example (mode k : Nat) (r : Row) (seen : List Row) :
    localCheck mode k (rowCode r) (tableCode seen)=1 ↔ r.valid mode k seen=true :=
  localCheck_correct mode k r seen
example : localCheck 0 0 (rowCode parent) (tableCode [child])=1 := by
  apply (localCheck_correct 0 0 parent [child]).mpr
  simp [parent,child,Row.valid,binaryAt,binaryEquations]
example : ¬localCheck 0 0 (rowCode {parent with first:=1}) (tableCode [child])=1 := by
  intro h
  have hv := (localCheck_correct 0 0 {parent with first:=1} [child]).mp h
  simp [parent,Row.valid,binaryAt] at hv
example (mode k code history : Nat) : localCheck mode k code history=0 ∨
    localCheck mode k code history=1 := localCheck_boolean mode k code history

example (mode k d i o c : Nat) : checkNat mode k d i o c=truth (checkCode mode k d i o c) :=
  checkNat_eq_checkCode mode k d i o c
example (code : Nat) : ∃ rows,decodeTable code code=some rows :=
  decodeTable_total code code (Nat.le_refl _)
example (fuel code : Nat) (rows : List Row) (h : decodeTable fuel code=some rows) :
    tableCode rows=code := tableCode_of_decode h
example (mode k : Nat) (rows seen : List Row) (fuel : Nat) (h : rows.length≤fuel) :
    scan fuel mode k (Nat.pair (tableCode rows) (tableCode seen))=
      match run mode k rows seen with
      | none => 0
      | some result => Nat.pair 0 (tableCode result) := scan_table mode k rows seen fuel h

#print axioms localCheck
#print axioms localCheck_correct
#print axioms localCheck_boolean
#print axioms step
#print axioms scan
#print axioms scan_table
#print axioms finish
#print axioms rowCode_decodeRow
#print axioms tableCode_of_decode
#print axioms decodeTable_total
#print axioms checkNat_eq_checkCode

/- Bounded source scans exercise the real numeric transitions without running
an impractically large unary primitive recursion on an encoded list value. -/
#eval finish 0 parent.input parent.output (scan 2 0 0 (Nat.pair (tableCode [child,parent]) 0))==1
#eval finish 0 parent.input parent.output (scan 1 0 0 (Nat.pair (tableCode [child,parent]) 0))==0
#eval finish 0 parent.input parent.output (scan 2 0 0
  (Nat.pair (tableCode [child,{parent with first:=1}]) 0))==0
#eval finish 0 parent.input parent.output (scan 2 0 0
  (Nat.pair (tableCode [child,{parent with depth:=1}]) 0))==0
#eval scan 3 0 0 0==0

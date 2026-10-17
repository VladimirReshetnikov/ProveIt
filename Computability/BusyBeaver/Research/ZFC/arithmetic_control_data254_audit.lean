import BusyBeaver.ZFC.ArithmeticControlData254

set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticControlData254 FiniteControlTable254

#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.natBits_code
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.binaryValue_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.binaryTerm_nat
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.compact_lookup_agrees
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.native_lookup_supported
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.native_lookup_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.source_not_node
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.sourceOpcode_bounds
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.sourceRegister_bound
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.successorNumber_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.field_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.fieldValue_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.fieldValue_supported
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.opcode_defined
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.opcodeValue_at
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticControlData254.opcodeValue_nonzero_iff

example : natBits 0 = [] := by simp [natBits]
example (n : Nat) : ArithmeticMachinePerm252.bitsCode (natBits n) = n := natBits_code n

section Open
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]
example (n : Nat) : (ArithmeticFiniteControl254.binaryTerm (natBits n)).val
    (![] : Fin 0 → V) = (n : V) := binaryTerm_nat n
example (rows : List (Nat × Nat)) (first : Nat) (q branch : V) :
    ArithmeticFiniteControl254.lookupValue (compactRows first rows) q branch =
      ArithmeticMachineGraphPerm252.lookupValue rows first q branch :=
  compact_lookup_agrees rows first q branch
example (rows : List (Nat × Nat)) (first : Nat) (q branch : V)
    (h : ArithmeticMachineGraphPerm252.lookupValue rows first q branch ≠ 0) :
    ∃ i : Fin rows.length, q = ((first+i.val+1 : Nat) : V) :=
  native_lookup_supported rows first q branch h
example (rows : List (Nat × Nat)) (first index : Nat) (hi : index < rows.length)
    (branch : V) : ArithmeticMachineGraphPerm252.lookupValue rows first
      ((first+index+1 : Nat) : V) branch =
      if branch = 0 then ((rows[index]'hi).1 : V) else ((rows[index]'hi).2 : V) :=
  native_lookup_at rows first index hi branch
example (i : Control) : 0 < sourceOpcode i ∧ sourceOpcode i ≤ 4 := sourceOpcode_bounds i
example (i : Control) : sourceRegister i < 9 := sourceRegister_bound i
example (i : Control) (positive : Bool) :
    successorNumber i positive = 0 ↔ (source i).2 = .halt := successorNumber_zero_iff i positive
example (f g : Control → Nat) (out q branch : V) :
    (fieldDef f g).val.Evalb ![out,q,branch] ↔ out = fieldValue f g q branch := by simp
example (f g : Control → Nat) (i : Control) (branch : V) :
    fieldValue f g (number i : V) branch = if branch=0 then (f i : V) else (g i : V) :=
  fieldValue_at f g i branch
example (f g : Control → Nat) (q branch : V) (h : fieldValue f g q branch ≠ 0) :
    ∃ i : Control, q=(number i : V) := fieldValue_supported f g q branch h
example (out q : V) : (opcodeDef.val.Evalb ![out,q]) ↔ out=opcodeValue q := by simp
example (i : Control) : opcodeValue (V := V) (number i : V) = (sourceOpcode i : V) :=
  opcodeValue_at i
example (q : V) : opcodeValue q ≠ 0 ↔ ∃ i : Control, q=(number i : V) :=
  opcodeValue_nonzero_iff q
/-- Different columns use one exact source index, without a table oracle. -/
example (i : Control) (branch : V) :
    fieldValue sourceOpcode sourceOpcode (number i : V) branch = (sourceOpcode i : V) ∧
    fieldValue sourceRegister sourceRegister (number i : V) branch = (sourceRegister i : V) := by
  constructor <;> rw [fieldValue_at] <;> split <;> rfl
end Open

example (i : Control) (r : Nat) : (source i).2 ≠ .node r := source_not_node i r
example (i : Control) : sourcePC i = ArithmeticMachinePerm252.bitsCode (source i).1 := rfl
example (i : Control) (positive : Bool) : sourceSpareDelta i positive ≤ 1 := by
  cases he : (source i).2 <;> cases positive <;> simp [sourceSpareDelta,he]
example (i : Control) (positive : Bool) (h : (source i).2 ≠ .halt) :
    0 < successorNumber i positive := by
  have hn : successorNumber i positive ≠ 0 := fun hz => h ((successorNumber_zero_iff i positive).mp hz)
  omega

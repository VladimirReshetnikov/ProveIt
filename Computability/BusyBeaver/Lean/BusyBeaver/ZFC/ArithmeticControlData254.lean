import BusyBeaver.ZFC.ArithmeticFiniteControl254
import BusyBeaver.ZFC.FiniteControlTable254

set_option autoImplicit false

/-!
External natural constants and actual source-derived finite control data, with
compact bounded lookup calibration. The actual catalogue/resolver is imported,
not copied from a Python table. No logical step/run, represented register state,
binary runtime or internal scheduler equivalence is claimed here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticControlData254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open RegisterPath FiniteControlTable254
open ArithmeticFiniteControl254 (Row binaryValue binaryTerm)
open ArithmeticMachinePerm252 (bitsCode)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- Canonical least-significant-first bits of a fixed external natural.
This recursion does not inspect an arithmetic-model element. -/
def natBits (n : Nat) : List Bool :=
  if n = 0 then [] else decide (n%2=1) :: natBits (n/2)
termination_by n
decreasing_by omega

theorem natBits_code (n : Nat) : bitsCode (natBits n) = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n = 0
    · subst n; rw [natBits,if_pos rfl]; rfl
    · rw [natBits,if_neg hn,bitsCode,ih (n/2) (by omega)]
      have hb : (decide (n%2=1)).toNat = n%2 := by
        rcases Nat.mod_two_eq_zero_or_one n with hz | ho
        · simp [hz]
        · simp [ho]
      rw [hb]
      omega

/-- Uniform key order avoids independent-column priority ambiguities. -/
def compactRows : Nat → List (Nat × Nat) → List Row
  | _, [] => []
  | first, row :: rows =>
      ⟨natBits (first+1),natBits row.1,natBits row.2⟩ :: compactRows (first+1) rows

section Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

theorem binaryValue_nat (n : Nat) : binaryValue (V := V) (natBits n) = (n : V) := by
  rw [ArithmeticFiniteControl254.binaryValue_cast,natBits_code]

theorem binaryTerm_nat (n : Nat) :
    (binaryTerm (natBits n)).val (![] : Fin 0 → V) = (n : V) := by
  rw [ArithmeticFiniteControl254.binaryTerm_val,binaryValue_nat]

/-- Exact agreement with the existing finite arithmetic lookup on every
internal key and branch input, while the syntax uses compact binary constants. -/
theorem compact_lookup_agrees (rows : List (Nat × Nat)) (first : Nat) (q branch : V) :
    ArithmeticFiniteControl254.lookupValue (compactRows first rows) q branch =
      ArithmeticMachineGraphPerm252.lookupValue rows first q branch := by
  induction rows generalizing first with
  | nil => rfl
  | cons row rows ih =>
    simp only [compactRows,ArithmeticFiniteControl254.lookupValue,
      ArithmeticMachineGraphPerm252.lookupValue,binaryValue_nat,numeral_eq_natCast,ih]

/-- A positive result classifies an arbitrary internal key by one fixed
external row index. It does not assume that the key is standard. -/
theorem native_lookup_supported (rows : List (Nat × Nat)) (first : Nat) (q branch : V)
    (hn : ArithmeticMachineGraphPerm252.lookupValue rows first q branch ≠ 0) :
    ∃ i : Fin rows.length, q = ((first+i.val+1 : Nat) : V) := by
  induction rows generalizing first with
  | nil => simp [ArithmeticMachineGraphPerm252.lookupValue] at hn
  | cons row rows ih =>
    classical
    by_cases hq : q = ORingStructure.numeral (first+1)
    · exact ⟨⟨0,by simp⟩,by simpa only [Nat.add_zero,numeral_eq_natCast] using hq⟩
    · obtain ⟨i,hi⟩ := ih (first+1) (by
        simpa only [ArithmeticMachineGraphPerm252.lookupValue,if_neg hq] using hn)
      refine ⟨⟨i.val+1,by simpa only [List.length_cons] using Nat.succ_lt_succ i.isLt⟩,?_⟩
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hi

/-- All uniformly generated columns agree at a selected external index. -/
theorem native_lookup_at (rows : List (Nat × Nat)) (first index : Nat)
    (hi : index < rows.length) (branch : V) :
    ArithmeticMachineGraphPerm252.lookupValue rows first ((first+index+1 : Nat) : V) branch =
      if branch = 0 then ((rows[index]'hi).1 : V) else ((rows[index]'hi).2 : V) := by
  induction rows generalizing first index with
  | nil => simp at hi
  | cons row rows ih =>
    classical
    cases index with
    | zero =>
      simp only [Nat.add_zero,ArithmeticMachineGraphPerm252.lookupValue,
        numeral_eq_natCast,if_true,List.getElem_cons_zero]
    | succ index =>
      have hlt : ((first+1 : Nat) : V) < ((first+(index+1)+1 : Nat) : V) :=
        (Nat.cast_lt (α := V)).mpr (by omega)
      have hne : ((first+(index+1)+1 : Nat) : V) ≠ ((first+1 : Nat) : V) := ne_of_gt hlt
      simp only [ArithmeticMachineGraphPerm252.lookupValue,numeral_eq_natCast,
        if_neg hne,List.getElem_cons_succ]
      have hi' : index < rows.length := Nat.lt_of_succ_lt_succ (by
        simpa only [List.length_cons] using hi)
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (first+1) index hi'

end Arithmetic

/-- Instruction tags preserve the actual source: break/continue are resolved
control-only steps; the genuine halt remains a positive instruction opcode. -/
def edgeOpcode : Edge → Nat
  | .node _ => 0
  | .inc _ => 1
  | .decnz _ => 2
  | .brk _ | .cont _ => 3
  | .halt => 4

def sourceOpcode (i : Control) : Nat := edgeOpcode (source i).2

def sourceRegister (i : Control) : Nat :=
  match (source i).2 with
  | .inc r | .decnz r => Permutation252Frame.physOf r
  | _ => 0

def outgoingPath (i : Control) (positive : Bool) : List Bool :=
  let P := (source i).1
  match (source i).2 with
  | .node _ | .halt => P
  | .inc _ => incPath P
  | .decnz _ => if positive then incPath P else breakPath 1 P
  | .brk k => breakPath k P
  | .cont k => continuePath k P

/-- Zero is an actual halt successor only for the halt opcode; invalid node
leaves are excluded by source_accepted. Other successors are in1..6460. -/
def successorNumber (i : Control) (positive : Bool) : Nat :=
  match (source i).2 with
  | .node _ | .halt => 0
  | _ => number (resolveControl (outgoingPath i positive))

def sourceOverflow (i : Control) (positive : Bool) : Bool :=
  let P := (source i).1
  match (source i).2 with
  | .inc _ => SitePerm252.allOnes P
  | .decnz _ => if positive then SitePerm252.allOnes P else
      SitePerm252.allOnes (stripPath false 1 P)
  | .brk k => SitePerm252.allOnes (stripPath false k P)
  | _ => false

def sourceSpareDelta (i : Control) (positive : Bool) : Nat :=
  match (source i).2 with
  | .decnz _ => if positive then 1 else 0
  | _ => 0

def sourcePC (i : Control) : Nat := bitsCode (source i).1

/-- Actual catalogue entries are instruction leaves, never decoder nodes. -/
theorem source_not_node (i : Control) (r : Nat) : (source i).2 ≠ .node r := by
  intro he
  have h := source_accepted i
  rw [he,SitePerm252.check_node_false] at h
  cases h

theorem sourceOpcode_bounds (i : Control) : 0 < sourceOpcode i ∧ sourceOpcode i ≤ 4 := by
  cases he : (source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r => simp only [sourceOpcode,he,edgeOpcode]; omega
  | decnz r => simp only [sourceOpcode,he,edgeOpcode]; omega
  | brk k => simp only [sourceOpcode,he,edgeOpcode]; omega
  | cont k => simp only [sourceOpcode,he,edgeOpcode]; omega
  | halt => simp only [sourceOpcode,he,edgeOpcode]; omega

theorem sourceRegister_bound (i : Control) : sourceRegister i < 9 := by
  have hs := source_accepted i
  cases he : (source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r =>
      have hr := SitePerm252.check_inc_bound (source i).1 r (by simpa only [he] using hs)
      simpa only [sourceRegister,he] using (Permutation252Frame.physOf_lt ⟨r,hr⟩)
  | decnz r =>
      have hr := SitePerm252.check_decnz_bound (source i).1 r (by simpa only [he] using hs)
      simpa only [sourceRegister,he] using (Permutation252Frame.physOf_lt ⟨r,hr⟩)
  | brk k => simp only [sourceRegister,he]; omega
  | cont k => simp only [sourceRegister,he]; omega
  | halt => simp only [sourceRegister,he]; omega

/-- The live successor key is positive; only the genuine halt has no successor.
This does not infer a binary halt from a missing or out-of-range numeric key. -/
theorem successorNumber_zero_iff (i : Control) (positive : Bool) :
    successorNumber i positive = 0 ↔ (source i).2 = .halt := by
  cases he : (source i).2 with
  | node r => exact False.elim (source_not_node i r he)
  | inc r => simp [successorNumber,he,number]
  | decnz r => simp [successorNumber,he,number]
  | brk k => simp [successorNumber,he,number]
  | cont k => simp [successorNumber,he,number]
  | halt => simp [successorNumber,he]

/-- Fixed finite data computed from the imported source catalogue/resolver,
not supplied as arithmetic-model parameters or an assumed table oracle. -/
def fieldRows (zero positive : Control → Nat) : List (Nat × Nat) :=
  List.ofFn (fun i : Control => (zero i,positive i))

section Columns
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻]

noncomputable def fieldValue (zero positive : Control → Nat) (q branch : V) : V :=
  ArithmeticFiniteControl254.lookupValue (compactRows 0 (fieldRows zero positive)) q branch

def fieldDef (zero positive : Control → Nat) : 𝚺₀.Semisentence 3 :=
  ArithmeticFiniteControl254.lookupDef (compactRows 0 (fieldRows zero positive))

instance field_defined (zero positive : Control → Nat) :
    𝚺₀-Function₂[V] (fieldValue zero positive) via fieldDef zero positive :=
  ArithmeticFiniteControl254.lookup_defined _

theorem fieldValue_at (zero positive : Control → Nat) (i : Control) (branch : V) :
    fieldValue zero positive (number i : V) branch =
      if branch = 0 then (zero i : V) else (positive i : V) := by
  rw [fieldValue,compact_lookup_agrees]
  have h := native_lookup_at (fieldRows zero positive) 0 i.val
    (by simpa only [fieldRows,List.length_ofFn] using i.isLt) branch
  simpa only [fieldRows,List.getElem_ofFn,Nat.zero_add,number] using h

theorem fieldValue_supported (zero positive : Control → Nat) (q branch : V)
    (hn : fieldValue zero positive q branch ≠ 0) :
    ∃ i : Control, q = (number i : V) := by
  rw [fieldValue,compact_lookup_agrees] at hn
  obtain ⟨i,hi⟩ := native_lookup_supported (fieldRows zero positive) 0 q branch hn
  refine ⟨⟨i.val,by simpa only [fieldRows,List.length_ofFn] using i.isLt⟩,?_⟩
  simpa only [Nat.zero_add,number] using hi


/-- The actual opcode lookup is zero exactly outside the fixed live catalogue.
The actual halt opcode is four and remains distinct from this default. -/
noncomputable def opcodeValue (q : V) : V := fieldValue sourceOpcode sourceOpcode q 0

def opcodeDef : 𝚺₀.Semisentence 2 := .mkSigma
  “output control. !(fieldDef sourceOpcode sourceOpcode) output control 0”

instance opcode_defined : 𝚺₀-Function₁[V] opcodeValue via opcodeDef :=
  .mk fun e => by simp [opcodeDef,opcodeValue,(field_defined sourceOpcode sourceOpcode).iff]

theorem opcodeValue_at (i : Control) : opcodeValue (V := V) (number i : V) =
    (sourceOpcode i : V) := by
  simp only [opcodeValue,fieldValue_at,ite_self]

theorem opcodeValue_nonzero_iff (q : V) :
    opcodeValue q ≠ 0 ↔ ∃ i : Control, q = (number i : V) := by
  constructor
  · exact fieldValue_supported sourceOpcode sourceOpcode q 0
  · rintro ⟨i,rfl⟩
    rw [opcodeValue_at]
    exact ne_of_gt ((Nat.cast_pos (α := V)).mpr (sourceOpcode_bounds i).1)

end Columns
end SetTheory.BusyBeaver.ZFC.ArithmeticControlData254

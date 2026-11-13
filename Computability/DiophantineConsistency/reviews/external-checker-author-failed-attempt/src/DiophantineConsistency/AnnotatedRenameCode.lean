import DiophantineConsistency.AnnotatedRename

/-! # Explicit numeric certificates for annotated formula renaming -/

namespace DiophantineConsistency.AnnotatedRename
open SetTheory SetTheory.Form
open AnnotatedProofCode AnnotatedCodeArithmetic
set_option maxRecDepth 12000
set_option maxHeartbeats 600000
attribute [local irreducible] Nat.unpair

/-- A six-field row is packed without a recursive syntax decoder. -/
def rowCode (r : Row) : Nat :=
  Nat.pair r.tag (Nat.pair r.depth (Nat.pair r.first (Nat.pair r.second (Nat.pair r.input r.output))))

def decodeRow (n : Nat) : Row :=
  ⟨n.unpair.1,n.unpair.2.unpair.1,n.unpair.2.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.2.unpair.1,n.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2⟩

@[simp] theorem decodeRow_rowCode (r : Row) : decodeRow (rowCode r)=r := by
  cases r
  simp [decodeRow,rowCode]

def tableCode (rows : List Row) : Nat := listCode (rows.map rowCode)

/-- Zero is a terminal list marker; a positive code has one row and a tail.
Fuel bounds only the table length, not the numeric formula-code magnitudes. -/
def decodeTable : Nat → Nat → Option (List Row)
  | _,0 => some []
  | 0,_+1 => none
  | fuel+1,code+1 => do
    let rows ← decodeTable fuel code.unpair.2
    pure (decodeRow code.unpair.1::rows)

theorem decodeTable_tableCode (rows : List Row) (fuel : Nat) (h : rows.length≤fuel) :
    decodeTable fuel (tableCode rows)=some rows := by
  induction rows generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons r rows ih =>
    cases fuel with
    | zero => simp at h
    | succ fuel =>
      have hf : rows.length≤fuel := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using h
      simp only [tableCode,List.map_cons,listCode,decodeTable,Nat.unpair_pair,decodeRow_rowCode]
      change (do let rs ← decodeTable fuel (tableCode rows); pure (r::rs))=some (r::rows)
      rw [ih fuel hf]
      rfl

theorem length_le_tableCode (rows : List Row) : rows.length≤tableCode rows := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons r rows ih =>
    have hr := Nat.right_le_pair (rowCode r) (tableCode rows)
    change rows.length+1≤Nat.pair (rowCode r) (tableCode rows)+1
    omega

def checkCode (mode k depth input output code : Nat) : Bool :=
  match decodeTable code code with
  | some rows => checkTable mode k depth input output rows
  | none => false

@[simp] theorem checkCode_tableCode (mode k depth input output : Nat) (rows : List Row) :
    checkCode mode k depth input output (tableCode rows)=checkTable mode k depth input output rows := by
  simp only [checkCode,decodeTable_tableCode rows (tableCode rows) (length_le_tableCode rows)]

theorem checkCode_sound (mode k depth input output code : Nat)
    (h : checkCode mode k depth input output code=true) :
    ∃ f : Form,input=formCode f ∧ output=formCode (renamed mode k depth f) := by
  unfold checkCode at h
  cases hr : decodeTable code code with
  | none => simp [hr] at h
  | some rows =>
    rw [hr] at h
    exact checkTable_sound mode k depth input output rows h

/-- The explicit numeric-certificate language is exactly the original
renaming operation on each supplied formula. -/
theorem exists_code_iff (mode k depth : Nat) (f : Form) (output : Nat) :
    (∃ code : Nat,checkCode mode k depth (formCode f) output code=true) ↔
      output=formCode (renamed mode k depth f) := by
  constructor
  · rintro ⟨code,h⟩
    obtain ⟨g,hg,ho⟩ := checkCode_sound mode k depth (formCode f) output code h
    have he : f=g := formCode_injective hg
    simpa only [←he] using ho
  · intro h
    obtain ⟨rows,hr⟩ := (exists_table_iff mode k depth f output).mpr h
    exact ⟨tableCode rows,by simpa only [checkCode_tableCode] using hr⟩

theorem exists_shift_code_iff (f : Form) (output : Nat) :
    (∃ code : Nat,checkCode 0 0 0 (formCode f) output code=true) ↔
      output=formCode (rename Nat.succ f) := by
  simpa only [renamed,index_shift] using exists_code_iff 0 0 0 f output

theorem exists_inst_code_iff (k : Nat) (f : Form) (output : Nat) :
    (∃ code : Nat,checkCode 1 k 0 (formCode f) output code=true) ↔
      output=formCode (rename (inst k) f) := by
  simpa only [renamed,index_inst 1 k (by decide)] using exists_code_iff 1 k 0 f output

end DiophantineConsistency.AnnotatedRename

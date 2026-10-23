import DiophantineConsistency.AnnotatedRenameArithmetic

/-! # Supplied arithmetic validator for every local renaming-table row -/

namespace DiophantineConsistency.AnnotatedRenameLocal

open ScalarPRCode DirectScalar
open AnnotatedCodeArithmetic AnnotatedRename AnnotatedRenameArithmetic

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

/-- A boolean classifier remains a numeric zero/one value. -/
def truth (b : Bool) : Nat := if b then 1 else 0

@[simp] theorem truth_eq_one (b : Bool) : truth b=1 ↔ b=true := by cases b <;> decide

theorem truth_boolean (b : Bool) : truth b=0 ∨ truth b=1 := by cases b <;> simp [truth]

def atomicCheck (mode k code : Nat) : Nat :=
  atomicInput (Nat.pair mode (Nat.pair k code))
def bottomCheck (code : Nat) : Nat := truth (bottomEquations (decodeRow code))

def binaryCheck (code history : Nat) : Nat :=
  let r := decodeRow code
  let a := lookup history r.first
  let b := lookup history r.second
  if a=0 then 0 else if b=0 then 0 else
    truth (binaryEquations r (decodeRow a.pred) (decodeRow b.pred))

def unaryCheck (code history : Nat) : Nat :=
  let r := decodeRow code
  let a := lookup history r.first
  if a=0 then 0 else truth (unaryEquations r (decodeRow a.pred))

/-- Thresholds are checked in order, so the bodies for three binary tags and
two unary tags each occur only once in the supplied program. -/
def localCheck (mode k code history : Nat) : Nat :=
  let tag := (decodeRow code).tag
  if tag-1=0 then atomicCheck mode k code
  else if tag=2 then bottomCheck code
  else if tag-5=0 then binaryCheck code history
  else if tag-7=0 then unaryCheck code history
  else 0

theorem atomicCheck_correct (mode k : Nat) (r : Row) :
    atomicCheck mode k (rowCode r)=1 ↔ atomicEquations mode k r=true := by
  simpa only [atomicCheck,Nat.unpair_pair,decodeRow_rowCode] using
    atomicInput_correct (Nat.pair mode (Nat.pair k (rowCode r)))

theorem binaryCheck_correct (r : Row) (seen : List Row) :
    binaryCheck (rowCode r) (listCode (seen.map rowCode))=1 ↔ binaryAt r seen=true := by
  simp only [binaryCheck,decodeRow_rowCode,lookup_listCode,List.getElem?_map]
  cases ha : seen[r.first]? <;> cases hb : seen[r.second]? <;>
    simp [ha,hb,optionCode,binaryAt,decodeRow_rowCode]

theorem unaryCheck_correct (r : Row) (seen : List Row) :
    unaryCheck (rowCode r) (listCode (seen.map rowCode))=1 ↔ unaryAt r seen=true := by
  simp only [unaryCheck,decodeRow_rowCode,lookup_listCode,List.getElem?_map]
  cases ha : seen[r.first]? <;> simp [ha,optionCode,unaryAt,decodeRow_rowCode]

theorem localCheck_correct (mode k : Nat) (r : Row) (seen : List Row) :
    localCheck mode k (rowCode r) (listCode (seen.map rowCode))=1 ↔ r.valid mode k seen=true := by
  have ht : r.tag=0 ∨ r.tag=1 ∨ r.tag=2 ∨ r.tag=3 ∨ r.tag=4 ∨ r.tag=5 ∨
      r.tag=6 ∨ r.tag=7 ∨ 8≤r.tag := by omega
  rcases ht with h | h | h | h | h | h | h | h | h
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,atomicCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,atomicCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,bottomCheck]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,binaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,binaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,binaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,unaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,Row.valid,unaryCheck_correct]
  · have h0 : r.tag≠0 := by omega
    have h1 : r.tag≠1 := by omega
    have h2 : r.tag≠2 := by omega
    have h3 : r.tag≠3 := by omega
    have h4 : r.tag≠4 := by omega
    have h5 : r.tag≠5 := by omega
    have h6 : r.tag≠6 := by omega
    have h7 : r.tag≠7 := by omega
    have hs1 : r.tag-1≠0 := by omega
    have hs5 : r.tag-5≠0 := by omega
    have hs7 : r.tag-7≠0 := by omega
    simp [localCheck,decodeRow_rowCode,hs1,hs5,hs7,h0,h1,h2,h3,h4,h5,h6,h7,Row.valid]

theorem localCheck_boolean (mode k code history : Nat) :
    localCheck mode k code history=0 ∨ localCheck mode k code history=1 := by
  simp only [localCheck]
  split_ifs
  · simp only [atomicCheck,atomicInput,Nat.unpair_pair]; split_ifs <;> simp
  · exact truth_boolean _
  · simp only [binaryCheck]
    split_ifs <;> first | exact Or.inl rfl | exact truth_boolean _
  · simp only [unaryCheck]
    split_ifs <;> first | exact Or.inl rfl | exact truth_boolean _
  · simp


end DiophantineConsistency.AnnotatedRenameLocal

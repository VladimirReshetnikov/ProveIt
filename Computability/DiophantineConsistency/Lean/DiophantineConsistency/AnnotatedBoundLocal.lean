import DiophantineConsistency.AnnotatedBound
import DiophantineConsistency.AnnotatedRenameLocalPR

/-! # Supplied local arithmetic validators for additive bound tables -/
namespace DiophantineConsistency.AnnotatedBoundLocal
open ScalarPRCode DirectScalar AnnotatedProofCode AnnotatedCodeArithmetic
open AnnotatedRename (Row rowCode decodeRow decodeRow_rowCode)
open AnnotatedBound
open AnnotatedRenameLocal (truth truth_eq_one truth_boolean)
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

def atomicCheck (code : Nat) : Nat := truth (atomicEquations (decodeRow code))

theorem atomicCheck_correct (r : Row) :
    atomicCheck (rowCode r)=1 ↔ atomicEquations r=true := by
  simp only [atomicCheck,decodeRow_rowCode,truth_eq_one]

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
def localCheck (code history : Nat) : Nat :=
  let tag := (decodeRow code).tag
  if tag-1=0 then atomicCheck code
  else if tag=2 then bottomCheck code
  else if tag-5=0 then binaryCheck code history
  else if tag-7=0 then unaryCheck code history
  else 0

theorem binaryCheck_correct (r : Row) (seen : List Row) :
    binaryCheck (rowCode r) (listCode (seen.map rowCode))=1 ↔ binaryAt r seen=true := by
  simp only [binaryCheck,decodeRow_rowCode,lookup_listCode,List.getElem?_map]
  cases ha : seen[r.first]? <;> cases hb : seen[r.second]? <;>
    simp [ha,hb,optionCode,binaryAt,decodeRow_rowCode]

theorem unaryCheck_correct (r : Row) (seen : List Row) :
    unaryCheck (rowCode r) (listCode (seen.map rowCode))=1 ↔ unaryAt r seen=true := by
  simp only [unaryCheck,decodeRow_rowCode,lookup_listCode,List.getElem?_map]
  cases ha : seen[r.first]? <;> simp [ha,optionCode,unaryAt,decodeRow_rowCode]

theorem localCheck_correct (r : Row) (seen : List Row) :
    localCheck (rowCode r) (listCode (seen.map rowCode))=1 ↔ valid r seen=true := by
  have ht : r.tag=0 ∨ r.tag=1 ∨ r.tag=2 ∨ r.tag=3 ∨ r.tag=4 ∨ r.tag=5 ∨
      r.tag=6 ∨ r.tag=7 ∨ 8≤r.tag := by omega
  rcases ht with h | h | h | h | h | h | h | h | h
  · simp [localCheck,decodeRow_rowCode,h,valid,atomicCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,valid,atomicCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,valid,bottomCheck]
  · simp [localCheck,decodeRow_rowCode,h,valid,binaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,valid,binaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,valid,binaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,valid,unaryCheck_correct]
  · simp [localCheck,decodeRow_rowCode,h,valid,unaryCheck_correct]
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
    simp [localCheck,decodeRow_rowCode,hs1,hs5,hs7,h0,h1,h2,h3,h4,h5,h6,h7,valid]

theorem localCheck_boolean (code history : Nat) :
    localCheck code history=0 ∨ localCheck code history=1 := by
  simp only [localCheck]
  split_ifs
  · exact truth_boolean _
  · exact truth_boolean _
  · simp only [binaryCheck]
    split_ifs <;> first | exact Or.inl rfl | exact truth_boolean _
  · simp only [unaryCheck]
    split_ifs <;> first | exact Or.inl rfl | exact truth_boolean _
  · simp

namespace P
open AnnotatedRenameLocal.Program (left right tag depth first second input output lookup block4)

def atomicProgram : R atomicCheck := by
  let actual := (input identity).pair (output identity)
  let expected := (AnnotatedRenameArithmetic.variableNode (tag identity)
    (first identity) (second identity)).pair
      (add (successor (first identity)) (successor (second identity)))
  let p := ifEq actual expected (constant 1) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [atomicCheck,truth,atomicEquations,Nat.pair_eq_pair,decide_eq_true_eq,id_eq]

def bottomProgram : R bottomCheck := by
  let actual := (input identity).pair (output identity)
  let expected := (constant 44).pair Realizes.zero
  let p := ifEq actual expected (constant 1) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [bottomCheck,truth,bottomEquations,Nat.pair_eq_pair,decide_eq_true_eq]
  rfl

def binaryCore (n : Nat) : Nat :=
  if n.unpair.2.unpair.1=0 then 0 else if n.unpair.2.unpair.2=0 then 0 else
    truth (binaryEquations (decodeRow n.unpair.1)
      (decodeRow n.unpair.2.unpair.1.pred) (decodeRow n.unpair.2.unpair.2.pred))

def binaryCoreProgram : R binaryCore := by
  let r := Realizes.left
  let ar := left Realizes.right
  let br := right Realizes.right
  let a := pred ar
  let b := pred br
  let actual := (input r).pair (output r)
  let expected := (AnnotatedRenameArithmetic.binary (tag r) (input a) (input b)).pair
    (add (output a) (output b))
  let body := ifEq actual expected (constant 1) Realizes.zero
  let p := ifZero ar Realizes.zero (ifZero br Realizes.zero body)
  refine p.ofEq ?_
  intro n
  simp only [Nat.pair_eq_pair,binaryCore,truth,binaryEquations,decide_eq_true_eq]

def binaryProgram : R (fun n => binaryCheck n.unpair.1 n.unpair.2) :=
  (binaryCoreProgram.comp
    (Realizes.left.pair ((lookup Realizes.right (first Realizes.left)).pair
      (lookup Realizes.right (second Realizes.left))))).ofEq
    (fun _ => by simp [binaryCore,binaryCheck])

def unaryCore (n : Nat) : Nat :=
  if n.unpair.2=0 then 0 else
    truth (unaryEquations (decodeRow n.unpair.1) (decodeRow n.unpair.2.pred))

def unaryCoreProgram : R unaryCore := by
  let r := Realizes.left
  let ar := Realizes.right
  let a := pred ar
  let actual := (second r).pair ((input r).pair (output r))
  let expected := Realizes.zero.pair
    ((AnnotatedRenameArithmetic.unary (tag r) (input a)).pair (output a))
  let body := ifEq actual expected (constant 1) Realizes.zero
  let p := ifZero ar Realizes.zero body
  refine p.ofEq ?_
  intro n
  simp only [Nat.pair_eq_pair,unaryCore,truth,unaryEquations,decide_eq_true_eq]

def unaryProgram : R (fun n => unaryCheck n.unpair.1 n.unpair.2) :=
  (unaryCoreProgram.comp (Realizes.left.pair (lookup Realizes.right (first Realizes.left)))).ofEq
    (fun _ => by simp [unaryCore,unaryCheck])

def localInput (n : Nat) : Nat := localCheck n.unpair.1 n.unpair.2

def localProgram : R localInput := by
  let r := Realizes.left
  let a := atomicProgram.comp r
  let b := bottomProgram.comp r
  let p := ifZero (sub (tag r) (constant 1)) a
    (ifEq (tag r) (constant 2) b
      (ifZero (sub (tag r) (constant 5)) binaryProgram
        (ifZero (sub (tag r) (constant 7)) unaryProgram Realizes.zero)))
  refine p.ofEq ?_
  intro n
  rfl

end P
end DiophantineConsistency.AnnotatedBoundLocal

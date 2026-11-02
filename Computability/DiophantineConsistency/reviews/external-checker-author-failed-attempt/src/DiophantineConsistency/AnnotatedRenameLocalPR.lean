import DiophantineConsistency.AnnotatedRenameLocal

/-! # Literal scalar programs for every local renaming-row condition -/
namespace DiophantineConsistency.AnnotatedRenameLocal
open ScalarPRCode DirectScalar
open AnnotatedCodeArithmetic AnnotatedRename AnnotatedRenameArithmetic
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

namespace Program

def left {f : Nat → Nat} (r : R f) : R (fun n => (f n).unpair.1) := Realizes.left.comp r
def right {f : Nat → Nat} (r : R f) : R (fun n => (f n).unpair.2) := Realizes.right.comp r

def tag {f : Nat → Nat} (r : R f) : R (fun n => (decodeRow (f n)).tag) := left r
def depth {f : Nat → Nat} (r : R f) : R (fun n => (decodeRow (f n)).depth) := left (right r)
def first {f : Nat → Nat} (r : R f) : R (fun n => (decodeRow (f n)).first) := left (right (right r))
def second {f : Nat → Nat} (r : R f) : R (fun n => (decodeRow (f n)).second) := left (right (right (right r)))
def input {f : Nat → Nat} (r : R f) : R (fun n => (decodeRow (f n)).input) := left (right (right (right (right r))))
def output {f : Nat → Nat} (r : R f) : R (fun n => (decodeRow (f n)).output) := right (right (right (right (right r))))

def lookup {f g : Nat → Nat} (r : R f) (i : R g) : R (fun n => AnnotatedCodeArithmetic.lookup (f n) (g n)) :=
  (lookupProgram.comp (r.pair i)).ofEq (fun _ => by simp)

def block4 {f g h i : Nat → Nat} (a : R f) (b : R g) (c : R h) (d : R i) :
    R (fun n => Nat.pair (f n) (Nat.pair (g n) (Nat.pair (h n) (i n)))) :=
  a.pair (b.pair (c.pair d))

/-- Bottom's fixed literal code is 44. One equality compares all four fields. -/
def bottom : R bottomCheck := by
  let r := identity
  let actual := block4 (first r) (second r) (input r) (output r)
  let expected := block4 Realizes.zero Realizes.zero (constant 44) (constant 44)
  let p := ifEq actual expected (constant 1) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [Nat.pair_eq_pair,bottomCheck,truth,bottomEquations,decodeRow,decide_eq_true_eq]
  rfl

/-- Arguments are `(row,(firstReferenceValue,secondReferenceValue))`; the
reference values use zero/successor option coding. -/
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
  let actual := block4 (depth a) (depth b) (input r) (output r)
  let expected := block4 (depth r) (depth r)
    (AnnotatedRenameArithmetic.binary (tag r) (input a) (input b))
    (AnnotatedRenameArithmetic.binary (tag r) (output a) (output b))
  let body := ifEq actual expected (constant 1) Realizes.zero
  let p := ifZero ar Realizes.zero (ifZero br Realizes.zero body)
  refine p.ofEq ?_
  intro n
  simp only [Nat.pair_eq_pair,binaryCore,truth,binaryEquations,decodeRow,decide_eq_true_eq]


def binary : R (fun n => binaryCheck n.unpair.1 n.unpair.2) :=
  (binaryCoreProgram.comp
    (Realizes.left.pair ((lookup Realizes.right (first Realizes.left)).pair
      (lookup Realizes.right (second Realizes.left))))).ofEq
    (fun _ => by simp [binaryCore,binaryCheck])

/-- Arguments are `(row,referenceValue)`. -/
def unaryCore (n : Nat) : Nat :=
  if n.unpair.2=0 then 0 else
    truth (unaryEquations (decodeRow n.unpair.1) (decodeRow n.unpair.2.pred))

def unaryCoreProgram : R unaryCore := by
  let r := Realizes.left
  let ar := Realizes.right
  let a := pred ar
  let actual := block4 (second r) (depth a) (input r) (output r)
  let expected := block4 Realizes.zero (successor (depth r))
    (AnnotatedRenameArithmetic.unary (tag r) (input a))
    (AnnotatedRenameArithmetic.unary (tag r) (output a))
  let body := ifEq actual expected (constant 1) Realizes.zero
  let p := ifZero ar Realizes.zero body
  refine p.ofEq ?_
  intro n
  simp only [Nat.pair_eq_pair,unaryCore,truth,unaryEquations,decodeRow,decide_eq_true_eq]


def unary : R (fun n => unaryCheck n.unpair.1 n.unpair.2) :=
  (unaryCoreProgram.comp (Realizes.left.pair (lookup Realizes.right (first Realizes.left)))).ofEq
    (fun _ => by simp [unaryCore,unaryCheck])

/-- Input is `(mode,(k,(rowCode,historyCode)))`. -/
def localInput (n : Nat) : Nat :=
  localCheck n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2

def localProgram : R localInput := by
  let mode := Realizes.left
  let k := left Realizes.right
  let r := left (right Realizes.right)
  let h := right (right Realizes.right)
  let a : R (fun n => atomicCheck n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.1) :=
    optimizedAtomicProgram.comp (mode.pair (k.pair r))
  let b := bottom.comp r
  let c : R (fun n => binaryCheck n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2) :=
    (binary.comp (r.pair h)).ofEq (fun _ => by simp)
  let d : R (fun n => unaryCheck n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2) :=
    (unary.comp (r.pair h)).ofEq (fun _ => by simp)
  let p := ifZero (sub (tag r) (constant 1)) a
    (ifEq (tag r) (constant 2) b
      (ifZero (sub (tag r) (constant 5)) c
        (ifZero (sub (tag r) (constant 7)) d Realizes.zero)))
  refine p.ofEq ?_
  intro n
  rfl

end Program
end DiophantineConsistency.AnnotatedRenameLocal

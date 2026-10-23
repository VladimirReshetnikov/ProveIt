import DiophantineConsistency.AnnotatedRenameCode

/-! # Supplied primitive-recursive local renaming transitions -/

namespace DiophantineConsistency.AnnotatedRenameArithmetic

open ScalarPRCode DirectScalar AnnotatedRename

set_option maxRecDepth 12000
set_option maxHeartbeats 600000
attribute [local irreducible] Nat.unpair

def indexInput (n : Nat) : Nat :=
  index n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2

def indexProgram : R indexInput := by
  let mode := Realizes.left
  let k := Realizes.left.comp Realizes.right
  let d := Realizes.left.comp (Realizes.right.comp Realizes.right)
  let i := Realizes.right.comp (Realizes.right.comp Realizes.right)
  let p := ifZero (sub d i)
    (ifZero mode (successor i) (ifEq i d (add k d) (pred i))) i
  refine p.ofEq ?_
  intro n
  simp only [indexInput,index]
  by_cases h : n.unpair.2.unpair.2.unpair.2<n.unpair.2.unpair.2.unpair.1
  · have hs : n.unpair.2.unpair.2.unpair.1-n.unpair.2.unpair.2.unpair.2≠0 := by omega
    simp only [h,hs,if_false,if_true]
  · have hs : n.unpair.2.unpair.2.unpair.1-n.unpair.2.unpair.2.unpair.2=0 := by omega
    simp only [h,hs,if_false,if_true,Nat.pred_eq_sub_one]

def atom {f : Nat → Nat} (p : R f) : R (fun n => atomCode (f n)) :=
  AnnotatedCodeArithmetic.atomConstructor.comp p

def fork {f g : Nat → Nat} (p : R f) (q : R g) : R (fun n => forkCode (f n) (g n)) :=
  (AnnotatedCodeArithmetic.forkConstructor.comp (p.pair q)).ofEq (fun _ => by simp [forkCode])

def binary {f g h : Nat → Nat} (tag : R f) (a : R g) (b : R h) :
    R (fun n => binaryCode (f n) (g n) (h n)) := fork (atom tag) (fork a b)

def variableNode {f g h : Nat → Nat} (tag : R f) (i : R g) (j : R h) :
    R (fun n => variableCode (f n) (g n) (h n)) := binary tag (atom i) (atom j)

def unary {f g : Nat → Nat} (tag : R f) (a : R g) :
    R (fun n => unaryCode (f n) (g n)) := fork (atom tag) a

/-- Constructor-program arguments are `(tag,(left,right))`. -/
def binaryProgram : R (fun n => binaryCode n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) :=
  binary Realizes.left (Realizes.left.comp Realizes.right) (Realizes.right.comp Realizes.right)

def variableProgram : R (fun n => variableCode n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2) :=
  variableNode Realizes.left (Realizes.left.comp Realizes.right) (Realizes.right.comp Realizes.right)

/-- The unary constructor uses `(tag,child)`. -/
def unaryProgram : R (fun n => unaryCode n.unpair.1 n.unpair.2) :=
  unary Realizes.left Realizes.right

def lifted {m k d i : Nat → Nat} (pm : R m) (pk : R k) (pd : R d) (pi : R i) :
    R (fun n => index (m n) (k n) (d n) (i n)) :=
  (indexProgram.comp (pm.pair (pk.pair (pd.pair pi)))).ofEq
    (fun _ => by simp [indexInput])

/-- Input is `(mode,(k,rowCode))`; this is the atomic row condition, classified
as one for true and zero for false. Tag-domain checking remains a separate
condition in `Row.valid`. -/
def atomicInput (n : Nat) : Nat :=
  let r := decodeRow n.unpair.2.unpair.2
  if r.input=variableCode r.tag r.first r.second ∧
    r.output=variableCode r.tag (index n.unpair.1 n.unpair.2.unpair.1 r.depth r.first)
      (index n.unpair.1 n.unpair.2.unpair.1 r.depth r.second) then 1 else 0

def atomicProgram : R atomicInput := by
  let mode := Realizes.left
  let k := Realizes.left.comp Realizes.right
  let rr := Realizes.right.comp Realizes.right
  let r1 := Realizes.right.comp rr
  let r2 := Realizes.right.comp r1
  let r3 := Realizes.right.comp r2
  let r4 := Realizes.right.comp r3
  let tag := Realizes.left.comp rr
  let d := Realizes.left.comp r1
  let i := Realizes.left.comp r2
  let j := Realizes.left.comp r3
  let input := Realizes.left.comp r4
  let output := Realizes.right.comp r4
  let expectedInput := variableNode tag i j
  let expectedOutput := variableNode tag (lifted mode k d i) (lifted mode k d j)
  let p := ifEq input expectedInput (ifEq output expectedOutput (constant 1) Realizes.zero) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [atomicInput,decodeRow]
  split_ifs <;> simp_all

theorem atomicInput_correct (n : Nat) : atomicInput n=1 ↔
    atomicEquations n.unpair.1 n.unpair.2.unpair.1 (decodeRow n.unpair.2.unpair.2)=true := by
  simp [atomicInput,atomicEquations]

def optimizedIndexProgram : R indexInput := indexProgram.optimize

def optimizedAtomicProgram : R atomicInput := atomicProgram.optimize

theorem indexProgram_nodeCount : indexProgram.val.nodeCount=177 := by decide
theorem optimizedIndexProgram_nodeCount : optimizedIndexProgram.val.nodeCount=161 := by decide
theorem binaryProgram_nodeCount : binaryProgram.val.nodeCount=33 := by decide
theorem variableProgram_nodeCount : variableProgram.val.nodeCount=49 := by decide
theorem unaryProgram_nodeCount : unaryProgram.val.nodeCount=19 := by decide
theorem atomicProgram_nodeCount : atomicProgram.val.nodeCount=1215 := by decide
theorem optimizedAtomicProgram_nodeCount : optimizedAtomicProgram.val.nodeCount=1151 := by decide

theorem atomicProgram_correct (n : Nat) : optimizedAtomicProgram.val.eval n=1 ↔
    atomicEquations n.unpair.1 n.unpair.2.unpair.1 (decodeRow n.unpair.2.unpair.2)=true := by
  rw [optimizedAtomicProgram.property]
  exact atomicInput_correct n

end DiophantineConsistency.AnnotatedRenameArithmetic

import DiophantineConsistency.AnnotatedContext

/-! # Literal supplied PR programs for whole context validation and shifting -/
namespace DiophantineConsistency.AnnotatedContextPR
open ScalarPRCode DirectScalar AnnotatedContext
open AnnotatedRenameLocal.Program (left right)

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair localCheck step scan

namespace P

def localInput (n : Nat) : Nat :=
  localCheck n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def localProgram : R localInput := by
  let i := Realizes.left
  let o := left Realizes.right
  let e := right Realizes.right
  let entry := left (pred e)
  let a := left entry
  let b := left (right entry)
  let table := right (right entry)
  let it := right (pred i)
  let ot := right (pred o)
  let actual := i.pair o
  let expected := (AnnotatedRenameArithmetic.fork a it).pair
    (AnnotatedRenameArithmetic.fork b ot)
  let checked := AnnotatedSchemaMaps.stepProgram shiftStep a b table
  let p := ifZero e Realizes.zero (ifEq actual expected checked Realizes.zero)
  refine p.ofEq ?_
  intro n
  simp only [localInput,localCheck]

def stepProgram : R step := by
  let i := Realizes.left
  let o := left Realizes.right
  let e := right Realizes.right
  let next := (right (pred i)).pair ((right (pred o)).pair (right (pred e)))
  let p := ifEq i (constant 1) identity (ifZero localProgram Realizes.zero next)
  refine p.ofEq ?_
  intro n
  simp only [step,inputCode,localInput,id_eq]
  rfl

def scannerRecursion (n : Nat) : Nat := n.unpair.2.rec n.unpair.1 (fun _ acc => step acc)

def scannerRecursionProgram : R scannerRecursion :=
  recursion (g := fun _ _ acc => step acc) identity (stepProgram.comp (right Realizes.right))

def scannerProgram : R (fun n => scan n.unpair.1 n) :=
  (scannerRecursionProgram.comp (identity.pair Realizes.left)).ofEq
    (fun _ => by simp only [scannerRecursion,Nat.unpair_pair,scan,id_eq])

def finishProgram : R finish := by
  let actual := Realizes.left.pair (left Realizes.right)
  let expected := (constant 1).pair (constant 1)
  let p := ifEq actual expected (constant 1) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [finish,AnnotatedRenameLocal.truth,Nat.pair_eq_pair,decide_eq_true_eq]

def value (n : Nat) : Nat := checkNat n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def program : R value :=
  (finishProgram.comp scannerProgram).ofEq (fun _ => by
    simp only [value,checkNat,inputCode,Nat.pair_unpair])

end P

theorem program_input (input output evidence : Nat) :
    P.program.val.eval (inputCode input output evidence)=checkNat input output evidence := by
  rw [P.program.property]
  simp only [P.value,inputCode,Nat.unpair_pair]

theorem program_sound (input output evidence : Nat)
    (h : P.program.val.eval (inputCode input output evidence)=1) :
    ∃ G : List SetTheory.Form,input=contextCode G ∧
      output=contextCode (G.map (SetTheory.rename Nat.succ)) := by
  rw [program_input] at h
  exact checkNat_sound input output evidence h

theorem exists_program_iff (G : List SetTheory.Form) (output : Nat) :
    (∃ evidence,P.program.val.eval (inputCode (contextCode G) output evidence)=1) ↔
      output=contextCode (G.map (SetTheory.rename Nat.succ)) := by
  simp only [program_input]
  exact exists_check_iff G output

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

theorem localProgram_nodeCount : P.localProgram.val.nodeCount=3941 := by decide
theorem stepProgram_nodeCount : P.stepProgram.val.nodeCount=4073 := by decide
theorem scannerProgram_nodeCount : P.scannerProgram.val.nodeCount=4087 := by decide
theorem finishProgram_nodeCount : P.finishProgram.val.nodeCount=89 := by decide
theorem program_nodeCount : P.program.val.nodeCount=4177 := by decide
theorem optimizedProgram_nodeCount : optimizedProgram.val.nodeCount=3855 := by decide

end DiophantineConsistency.AnnotatedContextPR

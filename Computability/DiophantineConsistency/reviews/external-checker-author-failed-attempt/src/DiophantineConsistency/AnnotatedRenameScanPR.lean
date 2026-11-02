import DiophantineConsistency.AnnotatedRenameScan
import DiophantineConsistency.AnnotatedRenameLocalPR

/-! # A supplied primitive-recursive program for the entire numeric renaming validator -/

namespace DiophantineConsistency.AnnotatedRenameScanPR

open ScalarPRCode DirectScalar
open AnnotatedRename AnnotatedRenameScan AnnotatedRenameLocal

set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair AnnotatedRenameLocal.localCheck AnnotatedRenameScan.step AnnotatedRenameScan.scan

namespace P
open AnnotatedRenameLocal.Program

def localRow {m k r h : Nat → Nat} (pm : R m) (pk : R k) (pr : R r) (ph : R h) :
    R (fun n => localCheck (m n) (k n) (r n) (h n)) :=
  (localProgram.comp (pm.pair (pk.pair (pr.pair ph)))).ofEq
    (fun _ => by simp only [localInput,Nat.unpair_pair])

/-- Step input is `(mode,(k,state))`. -/
def stepInput (n : Nat) : Nat := step n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def stepProgram : R stepInput := by
  let mode := Realizes.left
  let k := left Realizes.right
  let state := right Realizes.right
  let remaining := left state
  let history := right state
  let raw := pred remaining
  let row := left raw
  let tail := right raw
  let lc := localRow mode k row history
  let next := tail.pair (successor (row.pair history))
  let p := ifZero remaining state (ifZero lc Realizes.zero next)
  refine p.ofEq ?_
  intro n
  simp only [stepInput,step]

/-- The six input coordinates reuse the already explicit fixed-field row
packing: mode, k, root depth, input formula code, output formula code, table. -/
def value (n : Nat) : Nat :=
  let r := decodeRow n
  checkNat r.tag r.depth r.first r.second r.input r.output

def scannerBase (n : Nat) : Nat := Nat.pair (decodeRow n).output 0

def scannerBaseProgram : R scannerBase := (output identity).pair Realizes.zero

def stepOf {m k s : Nat → Nat} (pm : R m) (pk : R k) (ps : R s) :
    R (fun n => step (m n) (k n) (s n)) :=
  (stepProgram.comp (pm.pair (pk.pair ps))).ofEq
    (fun _ => by simp only [stepInput,Nat.unpair_pair])

def scannerTransition (n : Nat) : Nat :=
  step (decodeRow n.unpair.1).tag (decodeRow n.unpair.1).depth n.unpair.2.unpair.2

def scannerTransitionProgram : R scannerTransition :=
  stepOf (tag Realizes.left) (depth Realizes.left) (right Realizes.right)

def scannerRecursion (n : Nat) : Nat :=
  n.unpair.2.rec (scannerBase n.unpair.1)
    (fun _ acc => step (decodeRow n.unpair.1).tag (decodeRow n.unpair.1).depth acc)

def scannerRecursionProgram : R scannerRecursion :=
  recursion (g := fun z _ acc => step (decodeRow z).tag (decodeRow z).depth acc)
    scannerBaseProgram scannerTransitionProgram

def scannerProgram : R (fun n =>
    scan (decodeRow n).output (decodeRow n).tag (decodeRow n).depth
      (Nat.pair (decodeRow n).output 0)) :=
  (scannerRecursionProgram.comp (identity.pair (output identity))).ofEq
    (fun _ => by simp only [scannerRecursion,scannerBase,Nat.unpair_pair,scan,id_eq])

/-- Terminal-check input is `(depth,(inputCode,(outputCode,state)))`. -/
def finishInput (n : Nat) : Nat :=
  finish n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2

def finishProgram : R finishInput := by
  let d := Realizes.left
  let i := left Realizes.right
  let o := left (right Realizes.right)
  let state := right (right Realizes.right)
  let remaining := left state
  let history := right state
  let row := left (pred history)
  let actual := (depth row).pair ((input row).pair (output row))
  let expected := d.pair (i.pair o)
  let body := ifEq actual expected (constant 1) Realizes.zero
  let p := ifZero remaining (ifZero history Realizes.zero body) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [finishInput,finish,truth,Nat.pair_eq_pair,decide_eq_true_eq,decodeRow]

/-- The scanner appears once in the supplied program tree, as the last value
of a fixed argument block for the terminal checker. -/
def program : R value :=
  (finishProgram.comp ((first identity).pair ((second identity).pair
    ((input identity).pair scannerProgram)))).ofEq
      (fun _ => by simp only [finishInput,Nat.unpair_pair,value,checkNat,id_eq])

end P

/-- A pointwise proof for the actual complete supplied program, not an
existential computability assertion used to select code. -/
theorem program_eq_checkCode (n : Nat) : P.program.val.eval n=
    truth (checkCode (decodeRow n).tag (decodeRow n).depth (decodeRow n).first
      (decodeRow n).second (decodeRow n).input (decodeRow n).output) := by
  rw [P.program.property]
  exact checkNat_eq_checkCode _ _ _ _ _ _

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

theorem value_primrec : Nat.Primrec P.value := P.program.val.primrec.of_eq P.program.property

/-- Explicit six-coordinate parameter packing for the complete validator. -/
def inputCode (mode k depth input output table : Nat) : Nat :=
  rowCode ⟨mode,k,depth,input,output,table⟩

theorem program_input (mode k depth input output table : Nat) :
    P.program.val.eval (inputCode mode k depth input output table)=
      truth (checkCode mode k depth input output table) := by
  simpa only [inputCode,decodeRow_rowCode] using
    program_eq_checkCode (inputCode mode k depth input output table)

/-- Exact renaming language accepted by the actual supplied primitive-recursive
program. This concerns external naturals, not arbitrary model-omega codes. -/
theorem exists_program_iff (mode k depth : Nat) (f : SetTheory.Form) (output : Nat) :
    (∃ table : Nat,P.program.val.eval
      (inputCode mode k depth (AnnotatedProofCode.formCode f) output table)=1) ↔
        output=AnnotatedProofCode.formCode (renamed mode k depth f) := by
  simp only [program_input,truth_eq_one]
  exact exists_code_iff mode k depth f output

theorem localProgram_nodeCount : Program.localProgram.val.nodeCount=3119 := by decide
theorem optimizedLocalProgram_nodeCount : Program.localProgram.optimize.val.nodeCount=2931 := by decide
theorem stepProgram_nodeCount : P.stepProgram.val.nodeCount=3223 := by decide
theorem scannerProgram_nodeCount : P.scannerProgram.val.nodeCount=3271 := by decide
theorem finishProgram_nodeCount : P.finishProgram.val.nodeCount=297 := by decide
theorem program_nodeCount : P.program.val.nodeCount=3605 := by decide
theorem optimizedProgram_nodeCount : optimizedProgram.val.nodeCount=3329 := by decide

end DiophantineConsistency.AnnotatedRenameScanPR

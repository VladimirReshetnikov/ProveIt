import DiophantineConsistency.AnnotatedBoundLocal
import DiophantineConsistency.AnnotatedRenameScanPR

/-! # Complete supplied primitive-recursive bound and sealing validators -/
namespace DiophantineConsistency.AnnotatedBoundScan
open AnnotatedBound AnnotatedBoundLocal AnnotatedCodeArithmetic
open AnnotatedRename (Row rowCode decodeRow tableCode decodeTable decodeRow_rowCode
  length_le_tableCode)
open AnnotatedRenameLocal (truth truth_eq_one truth_boolean)
open ScalarPRCode DirectScalar
set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

/-- State is `(remainingCode,acceptedHistoryCode)`. Invalid rows reset to
zero, an absorbing rejecting state. A finished nonempty history is retained. -/
def step (state : Nat) : Nat :=
  let remaining := state.unpair.1
  let history := state.unpair.2
  if remaining=0 then state else
    let row := remaining.pred.unpair.1
    if localCheck row history=0 then 0 else
      Nat.pair remaining.pred.unpair.2 (Nat.pair row history+1)

def scan (fuel initial : Nat) : Nat :=
  fuel.rec initial (fun _ acc => step acc)

@[simp] theorem step_zero : step 0=0 := by simp [step]

@[simp] theorem scan_zero (fuel : Nat) : scan fuel 0=0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [scan] at *; rw [ih,step_zero]

theorem scan_succ (fuel state : Nat) :
    scan (fuel+1) state=scan fuel (step state) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (scan (fuel+1) state)=
      step (scan fuel (step state))
    rw [ih]

theorem scan_done (fuel history : Nat) :
    scan fuel (Nat.pair 0 history)=Nat.pair 0 history := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (scan fuel (Nat.pair 0 history))=Nat.pair 0 history
    rw [ih]
    simp [step]

theorem step_cons (r : Row) (rows seen : List Row) :
    step (Nat.pair (tableCode (r::rows)) (tableCode seen))=
      if valid r seen then Nat.pair (tableCode rows) (tableCode (r::seen)) else 0 := by
  by_cases hv : valid r seen=true
  · have hl := (localCheck_correct r seen).mpr hv
    change localCheck (rowCode r) (listCode (seen.map rowCode))=1 at hl
    simp [step,tableCode,List.map_cons,listCode,hl,hv]
  · have hn : localCheck (rowCode r) (tableCode seen)≠1 :=
      fun h => hv ((localCheck_correct r seen).mp h)
    have hl : localCheck (rowCode r) (tableCode seen)=0 :=
      (localCheck_boolean (rowCode r) (tableCode seen)).resolve_right hn
    change localCheck (rowCode r) (listCode (seen.map rowCode))=0 at hl
    simp [step,tableCode,List.map_cons,listCode,hl,hv]

theorem scan_table (rows seen : List Row) (fuel : Nat)
    (hf : rows.length≤fuel) :
    scan fuel (Nat.pair (tableCode rows) (tableCode seen))=
      match run rows seen with
      | none => 0
      | some result => Nat.pair 0 (tableCode result) := by
  induction rows generalizing seen fuel with
  | nil => simpa only [run,tableCode,List.map_nil,listCode] using scan_done fuel (tableCode seen)
  | cons r rows ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hff : rows.length≤fuel := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hf
      rw [scan_succ,step_cons]
      by_cases hv : valid r seen=true
      · simpa only [hv,if_true,run] using ih (r::seen) fuel hff
      · simp [hv,run]

def finish (input output state : Nat) : Nat :=
  if state.unpair.1=0 then
    if state.unpair.2=0 then 0 else
      let r := decodeRow state.unpair.2.pred.unpair.1
      truth (decide (r.input=input ∧ r.output=output))
  else 0

def checkNat (input output code : Nat) : Nat :=
  finish input output (scan code (Nat.pair code 0))

theorem finish_run (input output : Nat) (rows : List Row) :
    finish input output
      (match run rows [] with
      | none => 0
      | some result => Nat.pair 0 (tableCode result))=
        truth (checkTable input output rows) := by
  cases hr : run rows [] with
  | none => simp [finish,checkTable,hr,truth]
  | some result =>
    cases result with
    | nil => simp [finish,checkTable,hr,tableCode,listCode,truth]
    | cons r tail => simp [finish,checkTable,hr,tableCode,listCode,decodeRow_rowCode]

theorem checkNat_tableCode (input output : Nat) (rows : List Row) :
    checkNat input output (tableCode rows)=truth (checkTable input output rows) := by
  unfold checkNat
  have hs := scan_table rows [] (tableCode rows) (length_le_tableCode rows)
  change scan (tableCode rows) (Nat.pair (tableCode rows) 0)=_ at hs
  rw [hs]
  exact finish_run input output rows

theorem checkNat_eq_checkCode (input output code : Nat) :
    checkNat input output code=truth (checkCode input output code) := by
  obtain ⟨rows,hr⟩ := AnnotatedRenameScan.decodeTable_total code code (Nat.le_refl _)
  have he := AnnotatedRenameScan.tableCode_of_decode hr
  rw [←he,checkNat_tableCode,checkCode_tableCode]

attribute [local irreducible] localCheck step scan

namespace P
open AnnotatedRenameLocal.Program (left right input output)

/-- The numeric state is `(remainingTable,acceptedHistory)`. -/
def stepProgram : R step := by
  let remaining := Realizes.left
  let history := Realizes.right
  let raw := pred remaining
  let row := left raw
  let tail := right raw
  let lc := AnnotatedBoundLocal.P.localProgram.comp (row.pair history)
  let next := tail.pair (successor (row.pair history))
  let p := ifZero remaining identity (ifZero lc Realizes.zero next)
  refine p.ofEq ?_
  intro n
  simp only [step,AnnotatedBoundLocal.P.localInput,id_eq,Nat.unpair_pair]

/-- Whole-checker input is `(inputFormulaCode,(claimedBound,tableCode))`. -/
def value (n : Nat) : Nat := checkNat n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def scannerBase (n : Nat) : Nat := Nat.pair n.unpair.2.unpair.2 0

def scannerBaseProgram : R scannerBase := (right Realizes.right).pair Realizes.zero

def scannerRecursion (n : Nat) : Nat :=
  n.unpair.2.rec (scannerBase n.unpair.1) (fun _ acc => step acc)

def scannerRecursionProgram : R scannerRecursion :=
  recursion (g := fun _ _ acc => step acc) scannerBaseProgram
    (stepProgram.comp (right Realizes.right))

def scannerProgram : R (fun n => scan n.unpair.2.unpair.2
    (Nat.pair n.unpair.2.unpair.2 0)) :=
  (scannerRecursionProgram.comp (identity.pair (right Realizes.right))).ofEq
    (fun _ => by simp only [scannerRecursion,scannerBase,Nat.unpair_pair,scan,id_eq])

def finishInput (n : Nat) : Nat :=
  finish n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def finishProgram : R finishInput := by
  let i := Realizes.left
  let o := left Realizes.right
  let state := right Realizes.right
  let remaining := left state
  let history := right state
  let row := left (pred history)
  let actual := (input row).pair (output row)
  let expected := i.pair o
  let body := ifEq actual expected (constant 1) Realizes.zero
  let p := ifZero remaining (ifZero history Realizes.zero body) Realizes.zero
  refine p.ofEq ?_
  intro n
  simp only [finishInput,finish,truth,Nat.pair_eq_pair,decide_eq_true_eq]

def program : R value :=
  (finishProgram.comp (Realizes.left.pair ((left Realizes.right).pair scannerProgram))).ofEq
    (fun _ => by simp only [finishInput,Nat.unpair_pair,value,checkNat])

end P

def inputCode (input output table : Nat) : Nat := Nat.pair input (Nat.pair output table)

theorem program_input (input output table : Nat) :
    P.program.val.eval (inputCode input output table)=truth (checkCode input output table) := by
  rw [P.program.property]
  simp only [P.value,inputCode,Nat.unpair_pair]
  exact checkNat_eq_checkCode _ _ _

theorem exists_program_iff (f : SetTheory.Form) (output : Nat) :
    (∃ table : Nat,P.program.val.eval (inputCode (AnnotatedProofCode.formCode f) output table)=1) ↔
      output=SetTheory.bound f := by
  simp only [program_input,truth_eq_one]
  exact exists_code_iff f output

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

/-- Four arguments are `(input,(output,(closingLength,boundTable)))`. The bound
validator and universal iterator are both literal supplied programs. -/
def sealInput (input output length table : Nat) : Nat :=
  Nat.pair input (Nat.pair output (Nat.pair length table))

def sealValue (n : Nat) : Nat :=
  if checkNat n.unpair.1 n.unpair.2.unpair.2.unpair.1 n.unpair.2.unpair.2.unpair.2=0 then 0 else
    if n.unpair.2.unpair.1=AnnotatedClosure.closeCode n.unpair.1 n.unpair.2.unpair.2.unpair.1
    then 1 else 0

def sealProgram : R sealValue := by
  let i := Realizes.left
  let o := AnnotatedRenameLocal.Program.left Realizes.right
  let length := AnnotatedRenameLocal.Program.left (AnnotatedRenameLocal.Program.right Realizes.right)
  let table := AnnotatedRenameLocal.Program.right (AnnotatedRenameLocal.Program.right Realizes.right)
  let checked := P.program.comp (i.pair (length.pair table))
  let closed := AnnotatedClosure.program.comp (i.pair length)
  let p := ifZero checked Realizes.zero (ifEq o closed (constant 1) Realizes.zero)
  refine p.ofEq ?_
  intro n
  simp only [sealValue,P.value,Nat.unpair_pair]

theorem sealProgram_input (input output length table : Nat) :
    sealProgram.val.eval (sealInput input output length table)=
      truth (checkSeal input output table length) := by
  rw [sealProgram.property]
  simp only [sealValue,sealInput,Nat.unpair_pair,checkNat_eq_checkCode,checkSeal]
  cases checkCode input length table <;> simp [truth]

theorem exists_seal_program_iff (f : SetTheory.Form) (output : Nat) :
    (∃ table length : Nat,sealProgram.val.eval
      (sealInput (AnnotatedProofCode.formCode f) output length table)=1) ↔
        output=AnnotatedProofCode.formCode (SetTheory.sealF f) := by
  simp only [sealProgram_input,truth_eq_one]
  exact exists_seal_iff f output

theorem sealProgram_primrec : Nat.Primrec sealProgram.val.eval := sealProgram.val.primrec

theorem localProgram_nodeCount : AnnotatedBoundLocal.P.localProgram.val.nodeCount=1775 := by decide
theorem optimizedLocalProgram_nodeCount :
    AnnotatedBoundLocal.P.localProgram.optimize.val.nodeCount=1551 := by decide
theorem stepProgram_nodeCount : P.stepProgram.val.nodeCount=1849 := by decide
theorem scannerProgram_nodeCount : P.scannerProgram.val.nodeCount=1867 := by decide
theorem finishProgram_nodeCount : P.finishProgram.val.nodeCount=221 := by decide
theorem program_nodeCount : P.program.val.nodeCount=2095 := by decide
theorem optimizedProgram_nodeCount : optimizedProgram.val.nodeCount=1807 := by decide
theorem sealProgram_nodeCount : sealProgram.val.nodeCount=2279 := by decide
theorem optimizedSealProgram_nodeCount : sealProgram.optimize.val.nodeCount=1983 := by decide

end DiophantineConsistency.AnnotatedBoundScan

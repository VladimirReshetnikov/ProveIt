import DiophantineConsistency.AnnotatedRenameLocal
import DiophantineConsistency.NatIterate

/-!
# Numeric scan of complete annotated renaming tables

This external arithmetic state machine scans only the table spine and six
numeric row fields. Recursive formula parsing is absent. No internal
nonstandard-code interpretation is inferred from the external simulation.
-/

namespace DiophantineConsistency.AnnotatedRenameScan

open AnnotatedRename AnnotatedRenameLocal AnnotatedCodeArithmetic

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

/-- State is `(remainingCode,acceptedHistoryCode)`. Invalid rows reset to
zero, an absorbing rejecting state. A finished nonempty history is retained. -/
def step (mode k state : Nat) : Nat :=
  let remaining := state.unpair.1
  let history := state.unpair.2
  if remaining=0 then state else
    let row := remaining.pred.unpair.1
    if localCheck mode k row history=0 then 0 else
      Nat.pair remaining.pred.unpair.2 (Nat.pair row history+1)

def scan (fuel mode k initial : Nat) : Nat :=
  fuel.rec initial (fun _ acc => step mode k acc)

@[simp] theorem step_zero (mode k : Nat) : step mode k 0=0 := by simp [step]

@[simp] theorem scan_zero (fuel mode k : Nat) : scan fuel mode k 0=0 :=
  NatIterate.rec_fixed (step mode k) 0 (step_zero mode k) fuel

theorem scan_succ (fuel mode k state : Nat) :
    scan (fuel+1) mode k state=scan fuel mode k (step mode k state) :=
  NatIterate.rec_succ (step mode k) state fuel

theorem scan_done (fuel mode k history : Nat) :
    scan fuel mode k (Nat.pair 0 history)=Nat.pair 0 history :=
  NatIterate.rec_fixed (step mode k) _ (by simp [step]) fuel

theorem step_cons (mode k : Nat) (r : Row) (rows seen : List Row) :
    step mode k (Nat.pair (tableCode (r::rows)) (tableCode seen))=
      if r.valid mode k seen then Nat.pair (tableCode rows) (tableCode (r::seen)) else 0 := by
  have hl := eq_truth_of_boolean _ _
    (localCheck_boolean mode k (rowCode r) (tableCode seen)) (localCheck_correct mode k r seen)
  change localCheck mode k (rowCode r) (listCode (seen.map rowCode)) = _ at hl
  cases hv : r.valid mode k seen <;> simp [step,tableCode,List.map_cons,listCode,hl,hv,truth]

theorem scan_table (mode k : Nat) (rows seen : List Row) (fuel : Nat)
    (hf : rows.length≤fuel) :
    scan fuel mode k (Nat.pair (tableCode rows) (tableCode seen))=
      match run mode k rows seen with
      | none => 0
      | some result => Nat.pair 0 (tableCode result) := by
  induction rows generalizing seen fuel with
  | nil => simpa only [run,tableCode,List.map_nil,listCode] using scan_done fuel mode k (tableCode seen)
  | cons r rows ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hff : rows.length≤fuel := by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hf
      rw [scan_succ,step_cons]
      by_cases hv : r.valid mode k seen=true
      · simpa only [hv,if_true,run] using ih (r::seen) fuel hff
      · simp [hv,run]

def finish (depth input output state : Nat) : Nat :=
  if state.unpair.1=0 then
    if state.unpair.2=0 then 0 else
      let r := decodeRow state.unpair.2.pred.unpair.1
      truth (decide (r.depth=depth ∧ r.input=input ∧ r.output=output))
  else 0

def checkNat (mode k depth input output code : Nat) : Nat :=
  finish depth input output (scan code mode k (Nat.pair code 0))

theorem finish_run (mode k depth input output : Nat) (rows : List Row) :
    finish depth input output
      (match run mode k rows [] with
      | none => 0
      | some result => Nat.pair 0 (tableCode result))=
        truth (checkTable mode k depth input output rows) := by
  cases hr : run mode k rows [] with
  | none => simp [finish,checkTable,hr,truth]
  | some result =>
    cases result with
    | nil => simp [finish,checkTable,hr,tableCode,listCode,truth]
    | cons r tail => simp [finish,checkTable,hr,tableCode,listCode,decodeRow_rowCode]

theorem checkNat_tableCode (mode k depth input output : Nat) (rows : List Row) :
    checkNat mode k depth input output (tableCode rows)=truth (checkTable mode k depth input output rows) := by
  unfold checkNat
  have hs := scan_table mode k rows [] (tableCode rows) (length_le_tableCode rows)
  change scan (tableCode rows) mode k (Nat.pair (tableCode rows) 0)=_ at hs
  rw [hs]
  exact finish_run mode k depth input output rows

/-- Every six-field row code is canonical; no formula-code claim follows. -/
theorem rowCode_decodeRow (code : Nat) : rowCode (decodeRow code)=code := by
  simp only [rowCode,decodeRow,Nat.pair_unpair]

theorem tableCode_of_decode {fuel code : Nat} {rows : List Row}
    (h : decodeTable fuel code=some rows) : tableCode rows=code := by
  induction fuel generalizing code rows with
  | zero =>
    cases code with
    | zero => cases h; rfl
    | succ code => simp [decodeTable] at h
  | succ fuel ih =>
    cases code with
    | zero => cases h; rfl
    | succ code =>
      simp only [decodeTable] at h
      cases ht : decodeTable fuel code.unpair.2 with
      | none => simp [ht] at h
      | some tail =>
        simp only [ht,Option.pure_def] at h
        cases h
        simp only [tableCode,List.map_cons,listCode,rowCode_decodeRow]
        change Nat.pair code.unpair.1 (tableCode tail)+1=code+1
        rw [ih ht,Nat.pair_unpair]

theorem decodeTable_total (fuel code : Nat) (h : code≤fuel) :
    ∃ rows : List Row,decodeTable fuel code=some rows := by
  induction fuel generalizing code with
  | zero =>
    have he : code=0 := by omega
    subst code
    exact ⟨[],rfl⟩
  | succ fuel ih =>
    cases code with
    | zero => exact ⟨[],rfl⟩
    | succ code =>
      have hr : code.unpair.2≤code := by
        simpa only [Nat.pair_unpair] using Nat.right_le_pair code.unpair.1 code.unpair.2
      obtain ⟨rows,hrows⟩ := ih code.unpair.2 (by omega)
      refine ⟨decodeRow code.unpair.1::rows,?_⟩
      simp only [decodeTable,hrows]
      rfl

/-- Agreement with the frozen checker holds at every natural input, including
all untrusted row and list codes; no formula parser is assumed. -/
theorem checkNat_eq_checkCode (mode k depth input output code : Nat) :
    checkNat mode k depth input output code=truth (checkCode mode k depth input output code) := by
  obtain ⟨rows,hr⟩ := decodeTable_total code code (Nat.le_refl _)
  have he := tableCode_of_decode hr
  rw [←he,checkNat_tableCode,checkCode_tableCode]

end DiophantineConsistency.AnnotatedRenameScan

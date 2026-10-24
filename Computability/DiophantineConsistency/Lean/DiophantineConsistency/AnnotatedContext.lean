import DiophantineConsistency.AnnotatedSchemaMaps

/-! # Numeric arithmetic certificates for actual contexts and their shifts

An accepted raw pair of context codes determines an actual list of formulas.
Each cons cell has an explicit head-renaming certificate and exact numeric
constructor equations. No formula or context parser is assumed. -/
namespace DiophantineConsistency.AnnotatedContext

open SetTheory SetTheory.Form AnnotatedProofCode AnnotatedRename AnnotatedCodeArithmetic
open AnnotatedRenameLocal (truth truth_eq_one truth_boolean)

set_option maxRecDepth 16000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

def contextCode (G : List Form) : Nat := (quoteContext G).quote

@[simp] theorem contextCode_nil : contextCode []=1 := rfl
@[simp] theorem contextCode_cons (f : Form) (G : List Form) :
    contextCode (f::G)=forkCode (formCode f) (contextCode G) := rfl

theorem contextCode_injective : Function.Injective contextCode := by
  intro G H h
  have hh := congrArg (parseWith parseContext) h
  simpa only [contextCode,parseWith_quotation,parseContext_quoteContext,Option.some.injEq] using hh

def shiftStep : AnnotatedSchemaMaps.Step := ⟨0,0,0⟩

def entryCode (input output table : Nat) : Nat := Nat.pair input (Nat.pair output table)
def inputCode (input output evidence : Nat) : Nat := Nat.pair input (Nat.pair output evidence)

def localCheck (input output evidence : Nat) : Nat :=
  if evidence=0 then 0 else
    let entry := evidence.pred.unpair.1
    let a := entry.unpair.1
    let b := entry.unpair.2.unpair.1
    let table := entry.unpair.2.unpair.2
    if Nat.pair input output = Nat.pair (forkCode a input.pred.unpair.2)
        (forkCode b output.pred.unpair.2) then
      AnnotatedSchemaMaps.stepValue shiftStep a b table
    else 0

theorem shiftStep_eq (f : Form) : shiftStep.apply f=rename Nat.succ f := by
  simp only [shiftStep,AnnotatedSchemaMaps.Step.apply,renamed,index_shift]

theorem localCheck_boolean (input output evidence : Nat) :
    localCheck input output evidence=0 ∨ localCheck input output evidence=1 := by
  simp only [localCheck]
  split_ifs
  · exact Or.inl rfl
  · simp only [AnnotatedSchemaMaps.stepValue]
    rw [AnnotatedRenameScan.checkNat_eq_checkCode]
    exact truth_boolean _
  · exact Or.inl rfl

theorem localCheck_sound (input output evidence : Nat)
    (h : localCheck input output evidence=1) :
    ∃ f : Form,input=forkCode (formCode f) input.pred.unpair.2 ∧
      output=forkCode (formCode (rename Nat.succ f)) output.pred.unpair.2 := by
  unfold localCheck at h
  split at h
  next he => contradiction
  next he =>
    dsimp only at h
    split at h
    next hp =>
      simp only [AnnotatedSchemaMaps.stepValue] at h
      rw [AnnotatedRenameScan.checkNat_eq_checkCode,truth_eq_one] at h
      obtain ⟨f,ha,hb⟩ := checkCode_sound 0 0 0 _ _ _ h
      have hbs : evidence.pred.unpair.1.unpair.2.unpair.1=
          formCode (rename Nat.succ f) := by simpa only [renamed,index_shift] using hb
      obtain ⟨hi,ho⟩ := Nat.pair_eq_pair.mp hp
      exact ⟨f,by simpa only [ha] using hi,by simpa only [hbs] using ho⟩
    next hp => contradiction

private theorem fork_ne_one (a b : Nat) : forkCode a b≠1 := by
  have h := Nat.left_le_pair (a+1) b
  unfold forkCode
  omega

/-- State contains `(remainingInput,(remainingOutput,remainingEvidence))`.
Zero is an absorbing rejected state. A terminal input context is retained. -/
def step (state : Nat) : Nat :=
  let input := state.unpair.1
  let output := state.unpair.2.unpair.1
  let evidence := state.unpair.2.unpair.2
  if input=1 then state else if localCheck input output evidence=0 then 0 else
    inputCode input.pred.unpair.2 output.pred.unpair.2 evidence.pred.unpair.2

def scan (fuel initial : Nat) : Nat := fuel.rec initial (fun _ acc => step acc)

def finish (state : Nat) : Nat :=
  truth (decide (state.unpair.1=1 ∧ state.unpair.2.unpair.1=1))

def checkNat (input output evidence : Nat) : Nat :=
  finish (scan input (inputCode input output evidence))

@[simp] theorem step_zero : step 0=0 := by simp [step,localCheck]
@[simp] theorem scan_zero (fuel : Nat) : scan fuel 0=0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [scan] at *; rw [ih,step_zero]

theorem scan_succ (fuel state : Nat) : scan (fuel+1) state=scan fuel (step state) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (scan (fuel+1) state)=step (scan fuel (step state))
    rw [ih]

theorem scan_done (fuel output evidence : Nat) :
    scan fuel (inputCode 1 output evidence)=inputCode 1 output evidence := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (scan fuel (inputCode 1 output evidence))=inputCode 1 output evidence
    rw [ih]
    simp only [step,inputCode,Nat.unpair_pair,if_true]

/-- Strong raw-code soundness, including untrusted context and witness codes. -/
theorem scan_sound (fuel state : Nat) (h : finish (scan fuel state)=1) :
    ∃ G : List Form,state.unpair.1=contextCode G ∧
      state.unpair.2.unpair.1=contextCode (G.map (rename Nat.succ)) := by
  induction fuel generalizing state with
  | zero =>
    simp only [scan,finish,truth_eq_one,decide_eq_true_eq] at h
    exact ⟨[],h⟩
  | succ fuel ih =>
    rw [scan_succ] at h
    by_cases hi : state.unpair.1=1
    · simp only [step,hi,if_true] at h
      exact ih state h
    · by_cases hl : localCheck state.unpair.1 state.unpair.2.unpair.1 state.unpair.2.unpair.2=0
      · simp only [step,hi,if_false,hl,if_true,scan_zero,finish] at h
        simp [AnnotatedRenameLocal.truth] at h
      · have hl1 := (localCheck_boolean state.unpair.1 state.unpair.2.unpair.1
          state.unpair.2.unpair.2).resolve_left hl
        obtain ⟨f,hf,hfo⟩ := localCheck_sound _ _ _ hl1
        simp only [step,hi,hl,if_false] at h
        obtain ⟨G,hg,hgo⟩ := ih _ h
        simp only [inputCode,Nat.unpair_pair] at hg hgo
        refine ⟨f::G,?_,?_⟩
        · simpa only [hg,contextCode_cons] using hf
        · simpa only [hgo,List.map_cons,contextCode_cons] using hfo

theorem checkNat_sound (input output evidence : Nat) (h : checkNat input output evidence=1) :
    ∃ G : List Form,input=contextCode G ∧ output=contextCode (G.map (rename Nat.succ)) := by
  have hh := scan_sound input (inputCode input output evidence) h
  simpa only [inputCode,Nat.unpair_pair] using hh

theorem step_cons (f : Form) (G : List Form) (table remaining : Nat)
    (ht : AnnotatedSchemaMaps.stepValue shiftStep (formCode f)
      (formCode (rename Nat.succ f)) table=1) :
    step (inputCode (contextCode (f::G))
      (contextCode ((f::G).map (rename Nat.succ)))
      (Nat.pair (entryCode (formCode f) (formCode (rename Nat.succ f)) table) remaining+1))=
        inputCode (contextCode G) (contextCode (G.map (rename Nat.succ))) remaining := by
  have hn := fork_ne_one (formCode f) (contextCode G)
  simp only [step,inputCode,Nat.unpair_pair,contextCode_cons,List.map_cons,hn,if_false]
  simp only [localCheck,entryCode,Nat.unpair_pair,forkCode,Nat.add_sub_cancel,
    Nat.pred_eq_sub_one,ht,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,if_false,if_true]

/-- Completeness uses only one finite head-renaming table per context entry. -/
theorem scan_complete (G : List Form) : ∃ evidence : Nat,∀ fuel : Nat,G.length≤fuel →
    finish (scan fuel (inputCode (contextCode G)
      (contextCode (G.map (rename Nat.succ))) evidence))=1 := by
  induction G with
  | nil =>
    refine ⟨0,fun fuel _ => ?_⟩
    rw [contextCode_nil,List.map_nil,contextCode_nil,scan_done]
    simp [finish,inputCode,AnnotatedRenameLocal.truth]
  | cons f G ih =>
    obtain ⟨remaining,hr⟩ := ih
    obtain ⟨table,ht⟩ := (AnnotatedSchemaMaps.exists_step_iff shiftStep f
      (formCode (rename Nat.succ f))).mpr (by rw [shiftStep_eq])
    refine ⟨Nat.pair (entryCode (formCode f) (formCode (rename Nat.succ f)) table) remaining+1,?_⟩
    intro fuel hf
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      rw [scan_succ,step_cons f G table remaining ht]
      exact hr fuel (by simpa only [List.length_cons,Nat.succ_le_succ_iff] using hf)

theorem length_le_contextCode (G : List Form) : G.length≤contextCode G := by
  induction G with
  | nil => simp
  | cons f G ih =>
    have h := Nat.right_le_pair (formCode f+1) (contextCode G)
    change G.length+1≤Nat.pair (formCode f+1) (contextCode G)+1
    omega

theorem exists_check_iff (G : List Form) (output : Nat) :
    (∃ evidence : Nat,checkNat (contextCode G) output evidence=1) ↔
      output=contextCode (G.map (rename Nat.succ)) := by
  constructor
  · rintro ⟨evidence,h⟩
    obtain ⟨H,hi,ho⟩ := checkNat_sound (contextCode G) output evidence h
    have he : G=H := contextCode_injective hi
    simpa only [←he] using ho
  · intro h
    obtain ⟨evidence,he⟩ := scan_complete G
    exact ⟨evidence,by rw [h]; exact he (contextCode G) (length_le_contextCode G)⟩

end DiophantineConsistency.AnnotatedContext

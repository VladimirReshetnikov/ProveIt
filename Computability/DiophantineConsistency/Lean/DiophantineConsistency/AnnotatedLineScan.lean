import DiophantineConsistency.AnnotatedLine
import DiophantineConsistency.NatIterate

/-! # A supplied numeric scanner for all seventeen original proof rules

The fuel is an explicit untrusted natural input. Soundness holds for every
fuel; completeness uses the number of original proof lines. No formula,
context, or line parser is assumed in raw-input soundness.
-/
namespace DiophantineConsistency.AnnotatedLineScan
open SetTheory SetTheory.Form AnnotatedProofChecker AnnotatedProofCode AnnotatedCodeArithmetic
open AnnotatedRename (decodeRow)
open ScalarPRCode DirectScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

def historyCode (seen : List Judgment) : Nat := listCode (seen.map judgmentCode)
@[simp] theorem historyCode_nil : historyCode []=0 := rfl
@[simp] theorem historyCode_cons (j : Judgment) (seen : List Judgment) :
    historyCode (j::seen)=Nat.pair (judgmentCode j) (historyCode seen)+1 := rfl

/-- State is `(remainingLines,acceptedJudgments)`. Only the checked output
field is appended. Zero is an absorbing rejecting state. -/
def step (state : Nat) : Nat :=
  if state.unpair.1=0 then state else
    let line := state.unpair.1.pred.unpair.1
    if AnnotatedLine.check state.unpair.2 line=1 then
      Nat.pair state.unpair.1.pred.unpair.2
        (Nat.pair (decodeRow line).output state.unpair.2+1)
    else 0

def scan (fuel initial : Nat) : Nat := fuel.rec initial (fun _ acc => step acc)

@[simp] theorem step_zero : step 0=0 := by simp [step]
@[simp] theorem scan_zero (fuel : Nat) : scan fuel 0=0 :=
  NatIterate.rec_fixed step 0 step_zero fuel

theorem scan_succ (fuel state : Nat) : scan (fuel+1) state=scan fuel (step state) :=
  NatIterate.rec_succ step state fuel

theorem scan_done (fuel history : Nat) :
    scan fuel (Nat.pair 0 history)=Nat.pair 0 history :=
  NatIterate.rec_fixed step _ (by simp [step]) fuel

/-- Every surviving raw state has an actual provable judgment history. This
invariant begins with the empty list and is independent of any raw parser. -/
theorem scan_sound (fuel remaining : Nat) (seen : List Judgment)
    (hseen : ∀ j∈seen,j.Provable) :
    scan fuel (Nat.pair remaining (historyCode seen))=0 ∨
      ∃ rest result,scan fuel (Nat.pair remaining (historyCode seen))=
        Nat.pair rest (historyCode result) ∧ ∀ j∈result,j.Provable := by
  induction fuel generalizing remaining seen with
  | zero => exact Or.inr ⟨remaining,seen,rfl,hseen⟩
  | succ fuel ih =>
    by_cases hr : remaining=0
    · subst remaining
      exact Or.inr ⟨0,seen,scan_done (fuel+1) _,hseen⟩
    · rw [scan_succ]
      by_cases hc : AnnotatedLine.check (historyCode seen) remaining.pred.unpair.1=1
      · obtain ⟨original,ho,_,hv⟩ := AnnotatedLine.check_sound seen _ hc
        have hnext : ∀ j∈original.rule.output::seen,j.Provable := by
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact original.sound seen hseen hv
          · exact hseen j hj
        have hs : step (Nat.pair remaining (historyCode seen))=
            Nat.pair remaining.pred.unpair.2 (historyCode (original.rule.output::seen)) := by
          simp only [step,Nat.unpair_pair,hr,if_false,hc,if_true,historyCode_cons,ho]
        rw [hs]
        exact ih _ _ hnext
      · left
        have hs : step (Nat.pair remaining (historyCode seen))=0 := by
          simp only [step,Nat.unpair_pair,hr,if_false,hc]
        rw [hs,scan_zero]

/-- Terminal acceptance requires a consumed proof and a nonempty history whose
latest judgment is the claimed goal. -/
def finish (goal state : Nat) : Nat :=
  if state.unpair.1=0 then
    if state.unpair.2=0 then 0 else
      AnnotatedLine.equal state.unpair.2.pred.unpair.1 goal
  else 0

@[simp] theorem finish_zero (goal : Nat) : finish goal 0=0 := by simp [finish]

theorem finish_history (goal remaining : Nat) (seen : List Judgment) :
    finish goal (Nat.pair remaining (historyCode seen))=1 ↔
      remaining=0 ∧ ∃ j tail,seen=j::tail ∧ goal=judgmentCode j := by
  cases seen with
  | nil => simp [finish]
  | cons j tail =>
    by_cases hr : remaining=0
    · by_cases hg : goal=judgmentCode j <;>
        simp [finish,historyCode,listCode,AnnotatedLine.equal,hr,hg,eq_comm]
    · simp [finish,hr]

/-- `(goal,fuel,proofCode)` are all raw natural inputs. -/
def checkNat (goal fuel proofCode : Nat) : Nat :=
  finish goal (scan fuel (Nat.pair proofCode 0))

theorem checkNat_sound (goal fuel proofCode : Nat) (h : checkNat goal fuel proofCode=1) :
    ∃ j : Judgment,goal=judgmentCode j ∧ j.Provable := by
  have hs := scan_sound fuel proofCode [] (by simp)
  change finish goal (scan fuel (Nat.pair proofCode (historyCode [])))=1 at h
  rcases hs with hs | ⟨rest,result,hs,hresult⟩
  · rw [hs,finish_zero] at h
    contradiction
  · rw [hs,finish_history] at h
    obtain ⟨_,j,tail,rfl,hj⟩ := h
    exact ⟨j,hj,hresult j List.mem_cons_self⟩

/-- Pure numeric execution is useful only for the external completeness proof;
the supplied checker below executes the bounded natural-state scanner. -/
def run : List Nat → Nat → Option Nat
  | [],history => some history
  | line::lines,history =>
    if AnnotatedLine.check history line=1 then
      run lines (Nat.pair (decodeRow line).output history+1)
    else none

theorem scan_list (lines : List Nat) (history fuel : Nat) (hf : lines.length≤fuel) :
    scan fuel (Nat.pair (listCode lines) history)=
      match run lines history with
      | none => 0
      | some result => Nat.pair 0 result := by
  induction lines generalizing history fuel with
  | nil => simpa only [run,listCode] using scan_done fuel history
  | cons line lines ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hff : lines.length≤fuel := by
        simpa only [List.length_cons,Nat.succ_le_succ_iff] using hf
      rw [scan_succ]
      by_cases hc : AnnotatedLine.check history line=1
      · have hs : step (Nat.pair (listCode (line::lines)) history)=
            Nat.pair (listCode lines) (Nat.pair (decodeRow line).output history+1) := by
          simp [step,listCode,hc]
        rw [hs]
        simpa only [run,hc,if_true] using ih _ fuel hff
      · simp [step,listCode,hc,run]

/-- Every original valid execution has a numeric annotation with the same
number of lines and exactly the original resulting judgment history. -/
theorem run_complete (lines : List Line) (seen result : List Judgment)
    (h : AnnotatedProofChecker.run lines seen=some result) :
    ∃ raw : List Nat,raw.length=lines.length ∧
      run raw (historyCode seen)=some (historyCode result) := by
  induction lines generalizing seen with
  | nil => cases h; exact ⟨[],rfl,rfl⟩
  | cons line lines ih =>
    simp only [AnnotatedProofChecker.run] at h
    split at h
    next hv =>
      obtain ⟨rawLine,ho,_,hc⟩ := AnnotatedLine.check_complete seen line hv
      change AnnotatedLine.check (historyCode seen) rawLine=1 at hc
      obtain ⟨raw,hlen,hrun⟩ := ih _ h
      refine ⟨rawLine::raw,by simp only [List.length_cons,hlen],?_⟩
      simp only [run,hc,if_true,ho]
      exact hrun
    next hv => contradiction

theorem checkNat_complete (j : Judgment) (h : j.Provable) :
    ∃ fuel proofCode,checkNat (judgmentCode j) fuel proofCode=1 := by
  obtain ⟨lines,tail,hproduces⟩ := fragment_exists h
  have hr := hproduces []
  simp only [List.append_nil] at hr
  obtain ⟨raw,_,hraw⟩ := run_complete lines [] (j::tail) hr
  refine ⟨raw.length,listCode raw,?_⟩
  unfold checkNat
  have hs := scan_list raw 0 raw.length (Nat.le_refl _)
  change run raw 0=some (historyCode (j::tail)) at hraw
  rw [hraw] at hs
  rw [hs]
  exact (finish_history _ _ _).mpr ⟨rfl,j,tail,rfl,rfl⟩

theorem exists_checkNat_iff (j : Judgment) :
    (∃ fuel proofCode,checkNat (judgmentCode j) fuel proofCode=1) ↔ j.Provable := by
  constructor
  · rintro ⟨fuel,proofCode,h⟩
    obtain ⟨j',he,hp⟩ := checkNat_sound _ _ _ h
    exact judgmentCode_injective he ▸ hp
  · exact checkNat_complete j

attribute [local irreducible] step scan checkNat

namespace P
open AnnotatedRenameLocal.Program (left right output)

/-- The large line validator occurs once, as the second coordinate of a fixed
argument block. Branch comparisons inspect that stored result. -/
def stepCore (packet : Nat) : Nat :=
  if packet.unpair.1.unpair.1=0 then packet.unpair.1 else
    if packet.unpair.2=1 then
      Nat.pair packet.unpair.1.unpair.1.pred.unpair.2
        (Nat.pair (decodeRow packet.unpair.1.unpair.1.pred.unpair.1).output packet.unpair.1.unpair.2+1)
    else 0

def stepCoreProgram : R stepCore := by
  let state := Realizes.left
  let remaining := left state
  let history := right state
  let line := left (pred remaining)
  let next := (right (pred remaining)).pair (successor ((output line).pair history))
  refine (ifZero remaining state (ifEq Realizes.right (constant 1) next Realizes.zero)).ofEq ?_
  intro n
  simp only [stepCore]

def checkedStateProgram : R (fun n => AnnotatedLine.check n.unpair.2 n.unpair.1.pred.unpair.1) :=
  (AnnotatedLine.P.program.comp (Realizes.right.pair (left (pred Realizes.left)))).ofEq
    (fun _ => by simp only [AnnotatedLine.P.value,Nat.unpair_pair])

def stepProgram : R step :=
  (stepCoreProgram.comp (identity.pair checkedStateProgram)).ofEq
    (fun _ => by simp only [stepCore,step,Nat.unpair_pair,id_eq])

/-- The whole input is `(goal,(fuel,proofCode))`. -/
def value (n : Nat) : Nat := checkNat n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def scannerBase (n : Nat) : Nat := Nat.pair n.unpair.2.unpair.2 0

def scannerBaseProgram : R scannerBase := (right Realizes.right).pair Realizes.zero

def scannerRecursion (n : Nat) : Nat :=
  n.unpair.2.rec (scannerBase n.unpair.1) (fun _ acc => step acc)

def scannerRecursionProgram : R scannerRecursion :=
  recursion (g := fun _ _ acc => step acc) scannerBaseProgram
    (stepProgram.comp (right Realizes.right))

def scannerProgram : R (fun n => scan n.unpair.2.unpair.1
    (Nat.pair n.unpair.2.unpair.2 0)) :=
  (scannerRecursionProgram.comp (identity.pair (left Realizes.right))).ofEq
    (fun _ => by simp only [scannerRecursion,scannerBase,Nat.unpair_pair,scan,id_eq])

def finishInput (n : Nat) : Nat := finish n.unpair.1 n.unpair.2

def finishProgram : R finishInput := by
  let goal := Realizes.left
  let state := Realizes.right
  let remaining := left state
  let history := right state
  let latest := left (pred history)
  refine (ifZero remaining (ifZero history Realizes.zero
    (ifEq latest goal (constant 1) Realizes.zero)) Realizes.zero).ofEq ?_
  intro n
  simp only [finishInput,finish,AnnotatedLine.equal]

def program : R value :=
  (finishProgram.comp (Realizes.left.pair scannerProgram)).ofEq
    (fun _ => by simp only [finishInput,Nat.unpair_pair,value,checkNat])
end P

def inputCode (goal fuel proofCode : Nat) : Nat := Nat.pair goal (Nat.pair fuel proofCode)

theorem program_input (goal fuel proofCode : Nat) :
    P.program.val.eval (inputCode goal fuel proofCode)=checkNat goal fuel proofCode := by
  rw [P.program.property]
  simp only [P.value,inputCode,Nat.unpair_pair]

theorem program_sound (raw : Nat) (h : P.program.val.eval raw=1) :
    ∃ j : Judgment,raw.unpair.1=judgmentCode j ∧ j.Provable := by
  rw [P.program.property] at h
  exact checkNat_sound _ _ _ h

theorem exists_program_iff (j : Judgment) :
    (∃ fuel proofCode,P.program.val.eval (inputCode (judgmentCode j) fuel proofCode)=1) ↔
      j.Provable := by
  simp only [program_input]
  exact exists_checkNat_iff j

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

end DiophantineConsistency.AnnotatedLineScan

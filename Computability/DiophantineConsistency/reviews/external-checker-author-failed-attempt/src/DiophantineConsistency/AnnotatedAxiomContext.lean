import DiophantineConsistency.AnnotatedAxiomDispatch
import DiophantineConsistency.AnnotatedLine

/-! # Raw numeric certificates for complete sealed-ZFC axiom contexts -/
namespace DiophantineConsistency.AnnotatedAxiomContext
open SetTheory SetTheory.Form LeanProofs.BoundedZFCConsistency
open AnnotatedProofCode AnnotatedCodeArithmetic AnnotatedContext
open ScalarPRCode DirectScalar
set_option maxRecDepth 20000
set_option maxHeartbeats 1200000
attribute [local irreducible] Nat.unpair

def AllAxioms (G : List Form) : Prop := ∀ f∈G,ZFCax_s f

theorem contextCode_ne_zero (G : List Form) : contextCode G≠0 := by
  cases G with
  | nil => decide
  | cons f G => simp only [contextCode_cons,AnnotatedRename.forkCode]; omega

/-- A list cell is the dispatch packet `(tag,(formulaCode,evidence))`.
Checked formulas are prepended to the context. -/
def step (state : Nat) : Nat :=
  if state.unpair.1=0 then state else
    let entry := state.unpair.1.pred.unpair.1
    if AnnotatedAxiomDispatch.value entry.unpair.1 entry.unpair.2.unpair.1 entry.unpair.2.unpair.2=1 then
      Nat.pair state.unpair.1.pred.unpair.2
        (AnnotatedRename.forkCode entry.unpair.2.unpair.1 state.unpair.2)
    else 0

def scan (fuel initial : Nat) : Nat := fuel.rec initial (fun _ acc => step acc)
@[simp] theorem step_zero : step 0=0 := by simp [step]
@[simp] theorem scan_zero (fuel : Nat) : scan fuel 0=0 :=
  NatIterate.rec_fixed step 0 step_zero fuel

theorem scan_succ (fuel state : Nat) : scan (fuel+1) state=scan fuel (step state) :=
  NatIterate.rec_succ step state fuel

theorem scan_done (fuel history : Nat) : scan fuel (Nat.pair 0 history)=Nat.pair 0 history :=
  NatIterate.rec_fixed step _ (by simp [step]) fuel

/-- Every surviving raw state carries the code of an actual axiom context. -/
theorem scan_sound (fuel remaining : Nat) (G : List Form) (hG : AllAxioms G) :
    scan fuel (Nat.pair remaining (contextCode G))=0 ∨
      ∃ rest H,scan fuel (Nat.pair remaining (contextCode G))=Nat.pair rest (contextCode H) ∧
        AllAxioms H := by
  induction fuel generalizing remaining G with
  | zero => exact Or.inr ⟨remaining,G,rfl,hG⟩
  | succ fuel ih =>
    by_cases hr : remaining=0
    · subst remaining
      exact Or.inr ⟨0,G,scan_done (fuel+1) _,hG⟩
    · rw [scan_succ]
      let entry := remaining.pred.unpair.1
      by_cases hc : AnnotatedAxiomDispatch.value entry.unpair.1 entry.unpair.2.unpair.1
          entry.unpair.2.unpair.2=1
      · obtain ⟨f,hf,he⟩ := AnnotatedAxiomDispatch.sound _ _ _ hc
        have hnext : AllAxioms (f::G) := by
          intro g hg
          rcases List.mem_cons.mp hg with rfl | hg
          · exact hf
          · exact hG g hg
        have hs : step (Nat.pair remaining (contextCode G))=
            Nat.pair remaining.pred.unpair.2 (contextCode (f::G)) := by
          simp only [step,Nat.unpair_pair,hr,if_false]
          change (if AnnotatedAxiomDispatch.value entry.unpair.1 entry.unpair.2.unpair.1
            entry.unpair.2.unpair.2=1 then _ else _)=_
          rw [if_pos hc,he,contextCode_cons]
        rw [hs]
        exact ih _ _ hnext
      · left
        have hs : step (Nat.pair remaining (contextCode G))=0 := by
          simp only [step,Nat.unpair_pair,hr,if_false]
          exact if_neg hc
        rw [hs,scan_zero]

def finish (expected state : Nat) : Nat :=
  if state.unpair.1=0 then
    if state.unpair.2=0 then 0 else AnnotatedLine.equal state.unpair.2 expected
  else 0

@[simp] theorem finish_zero (expected : Nat) : finish expected 0=0 := by simp [finish]

theorem finish_context (expected remaining : Nat) (G : List Form) :
    finish expected (Nat.pair remaining (contextCode G))=1 ↔
      remaining=0 ∧ expected=contextCode G := by
  simp only [finish,Nat.unpair_pair,if_neg (contextCode_ne_zero G)]
  by_cases hr : remaining=0 <;> simp [hr,AnnotatedLine.equal,eq_comm]

/-- Expected context, explicit fuel, and certificate list are untrusted. -/
def checkNat (expected fuel certificate : Nat) : Nat :=
  finish expected (scan fuel (Nat.pair certificate 1))

theorem checkNat_sound (expected fuel certificate : Nat)
    (h : checkNat expected fuel certificate=1) :
    ∃ G : List Form,expected=contextCode G ∧ AllAxioms G := by
  have hs := scan_sound fuel certificate [] (by simp [AllAxioms])
  change finish expected (scan fuel (Nat.pair certificate (contextCode [])))=1 at h
  rcases hs with hs | ⟨rest,G,hs,hG⟩
  · rw [hs,finish_zero] at h
    contradiction
  · rw [hs,finish_context] at h
    exact ⟨G,h.2,hG⟩

def run : List Nat → Nat → Option Nat
  | [],history => some history
  | entry::entries,history =>
    if AnnotatedAxiomDispatch.value entry.unpair.1 entry.unpair.2.unpair.1 entry.unpair.2.unpair.2=1 then
      run entries (AnnotatedRename.forkCode entry.unpair.2.unpair.1 history)
    else none

theorem run_append (p q : List Nat) (history : Nat) :
    run (p++q) history=(run p history).bind (run q) := by
  induction p generalizing history with
  | nil => rfl
  | cons entry entries ih =>
    simp only [List.cons_append,run]
    split <;> simp_all

theorem scan_list (entries : List Nat) (history fuel : Nat) (hf : entries.length≤fuel) :
    scan fuel (Nat.pair (listCode entries) history)=
      match run entries history with
      | none => 0
      | some result => Nat.pair 0 result := by
  induction entries generalizing history fuel with
  | nil => simpa only [run,listCode] using scan_done fuel history
  | cons entry entries ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hff : entries.length≤fuel := by
        simpa only [List.length_cons,Nat.succ_le_succ_iff] using hf
      rw [scan_succ]
      by_cases hc : AnnotatedAxiomDispatch.value entry.unpair.1 entry.unpair.2.unpair.1
          entry.unpair.2.unpair.2=1
      · have hs : step (Nat.pair (listCode (entry::entries)) history)=
            Nat.pair (listCode entries) (AnnotatedRename.forkCode entry.unpair.2.unpair.1 history) := by
          simp [step,listCode,hc]
        rw [hs]
        simpa only [run,hc,if_true] using ih _ fuel hff
      · simp [step,listCode,hc,run]

theorem run_complete (G : List Form) (hG : AllAxioms G) :
    ∃ entries : List Nat,run entries 1=some (contextCode G) := by
  induction G with
  | nil => exact ⟨[],rfl⟩
  | cons f G ih =>
    obtain ⟨entries,he⟩ := ih (fun g hg => hG g (List.mem_cons_of_mem f hg))
    obtain ⟨tag,evidence,hf⟩ := (AnnotatedAxiomDispatch.exists_value_iff f).mpr
      (hG f List.mem_cons_self)
    let entry := AnnotatedAxiomDispatch.inputCode tag (formCode f) evidence
    refine ⟨entries++[entry],?_⟩
    rw [run_append,he,Option.bind_some]
    simp only [run,entry,AnnotatedAxiomDispatch.inputCode,Nat.unpair_pair,hf,if_true,contextCode_cons]

theorem checkNat_complete (G : List Form) (hG : AllAxioms G) :
    ∃ fuel certificate,checkNat (contextCode G) fuel certificate=1 := by
  obtain ⟨entries,hr⟩ := run_complete G hG
  refine ⟨entries.length,listCode entries,?_⟩
  unfold checkNat
  have hs := scan_list entries 1 entries.length (Nat.le_refl _)
  rw [hr] at hs
  rw [hs]
  exact (finish_context _ _ _).mpr ⟨rfl,rfl⟩

theorem exists_checkNat_iff (G : List Form) :
    (∃ fuel certificate,checkNat (contextCode G) fuel certificate=1) ↔ AllAxioms G := by
  constructor
  · rintro ⟨fuel,certificate,h⟩
    obtain ⟨H,he,hH⟩ := checkNat_sound _ _ _ h
    exact contextCode_injective he ▸ hH
  · exact checkNat_complete G

attribute [local irreducible] step scan checkNat

namespace P
open AnnotatedRenameLocal.Program (left right)

def stepCore (packet : Nat) : Nat :=
  if packet.unpair.1.unpair.1=0 then packet.unpair.1 else
    if packet.unpair.2=1 then
      Nat.pair packet.unpair.1.unpair.1.pred.unpair.2
        (AnnotatedRename.forkCode packet.unpair.1.unpair.1.pred.unpair.1.unpair.2.unpair.1
          packet.unpair.1.unpair.2)
    else 0

def stepCoreProgram : R stepCore := by
  let state := Realizes.left
  let remaining := left state
  let history := right state
  let entry := left (pred remaining)
  let head := left (right entry)
  let next := (right (pred remaining)).pair (AnnotatedRenameArithmetic.fork head history)
  refine (ifZero remaining state (ifEq Realizes.right (constant 1) next Realizes.zero)).ofEq ?_
  intro n
  simp only [stepCore]

def checkedStateProgram : R (fun n =>
    AnnotatedAxiomDispatch.P.inputValue n.unpair.1.pred.unpair.1) :=
  AnnotatedAxiomDispatch.P.program.comp (left (pred Realizes.left))

def stepProgram : R step :=
  (stepCoreProgram.comp (identity.pair checkedStateProgram)).ofEq
    (fun _ => by simp only [stepCore,step,Nat.unpair_pair,id_eq,AnnotatedAxiomDispatch.P.inputValue])

def value (n : Nat) : Nat := checkNat n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2

def scannerBase (n : Nat) : Nat := Nat.pair n.unpair.2.unpair.2 1

def scannerBaseProgram : R scannerBase := (right Realizes.right).pair (constant 1)

def scannerRecursion (n : Nat) : Nat :=
  n.unpair.2.rec (scannerBase n.unpair.1) (fun _ acc => step acc)

def scannerRecursionProgram : R scannerRecursion :=
  recursion (g := fun _ _ acc => step acc) scannerBaseProgram
    (stepProgram.comp (right Realizes.right))

def scannerProgram : R (fun n => scan n.unpair.2.unpair.1
    (Nat.pair n.unpair.2.unpair.2 1)) :=
  (scannerRecursionProgram.comp (identity.pair (left Realizes.right))).ofEq
    (fun _ => by simp only [scannerRecursion,scannerBase,Nat.unpair_pair,scan,id_eq])

def finishInput (n : Nat) : Nat := finish n.unpair.1 n.unpair.2

def finishProgram : R finishInput := by
  let expected := Realizes.left
  let state := Realizes.right
  let remaining := left state
  let history := right state
  refine (ifZero remaining (ifZero history Realizes.zero
    (ifEq history expected (constant 1) Realizes.zero)) Realizes.zero).ofEq ?_
  intro n
  simp only [finishInput,finish,AnnotatedLine.equal]

def program : R value :=
  (finishProgram.comp (Realizes.left.pair scannerProgram)).ofEq
    (fun _ => by simp only [finishInput,Nat.unpair_pair,value,checkNat])
end P

def inputCode (expected fuel certificate : Nat) : Nat := Nat.pair expected (Nat.pair fuel certificate)

theorem program_input (expected fuel certificate : Nat) :
    P.program.val.eval (inputCode expected fuel certificate)=checkNat expected fuel certificate := by
  rw [P.program.property]
  simp only [P.value,inputCode,Nat.unpair_pair]

theorem program_sound (raw : Nat) (h : P.program.val.eval raw=1) :
    ∃ G : List Form,raw.unpair.1=contextCode G ∧ AllAxioms G := by
  rw [P.program.property] at h
  exact checkNat_sound _ _ _ h

theorem exists_program_iff (G : List Form) :
    (∃ fuel certificate,P.program.val.eval (inputCode (contextCode G) fuel certificate)=1) ↔
      AllAxioms G := by
  simp only [program_input]
  exact exists_checkNat_iff G

theorem program_primrec : Nat.Primrec P.program.val.eval := P.program.val.primrec

def optimizedProgram : R P.value := P.program.optimize

end DiophantineConsistency.AnnotatedAxiomContext

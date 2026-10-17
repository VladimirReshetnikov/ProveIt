import BusyBeaver.ZFC.ArithmeticCommandRun254
import BusyBeaver.ZFC.ArithmeticCommandWordLaws254

/-!
Internal append execution for represented command words.
All words/states/times range over an arbitrary IΣ1 model. The time induction
freezes left, right and initial W; it contains no unbounded forallW premise.
No compiler block/scheduler/PA consistency endpoint is claimed here.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandWord254 ArithmeticCommandAppend254
open ArithmeticCommandWordLaws254 ArithmeticCommandStepWord254
open ArithmeticCommandTick254 ArithmeticCommandRun254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Append a fixed continuation to a live evaluator; halt remains halt.
Completed-left live(0,W) becomes live(right,W), not a halted evaluator. -/
noncomputable def extendValue (right config : V) : V :=
  if config = 0 then 0
  else liveValue (appendValue (remaining config) right) (working config)

def extendDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out right config. (config = 0 ∧ out = 0) ∨
    (config ≠ 0 ∧ ∃ word, !remainingDef word config ∧
      ∃ state, !workingDef state config ∧
      ∃ word1, !appendDef word1 word right ∧ !liveDef out word1 state)”

instance extend_defined : 𝚺₁-Function₂[V] extendValue via extendDef := .mk fun e => by
  classical
  by_cases hc : e 2 = 0 <;> simp [extendDef, extendValue, hc]
instance extend_definable : 𝚺₁-Function₂[V] extendValue := extend_defined.to_definable

@[simp] theorem extend_zero (right : V) : extendValue right 0 = 0 := by
  simp [extendValue]
@[simp] theorem extend_live (right word w : V) :
    extendValue right (liveValue word w) = liveValue (appendValue word right) w := by
  simp [extendValue]
@[simp] theorem extend_done (right w : V) :
    extendValue right (liveValue 0 w) = liveValue right w := by simp

/-- A single active head step commutes with appending a fixed continuation.
The actual cstep is independent of the replaced rest pointer. -/
theorem tick_extend_succ (right raw w : V) :
    tickValue (extendValue right (liveValue (raw+1) w)) =
      extendValue right (tickValue (liveValue (raw+1) w)) := by
  rw [extend_live, appendValue_succ, tick_live_succ, tick_live_succ]
  by_cases hs : ArithmeticCommandStep254.stepValue raw w = 0
  · simp [nextValue, step_replace, hs]
  · simp [nextValue, step_replace, tail_replace, hs]

/-- The local commuting law is needed only while the left evaluator is active.
After left completion, the appended continuation is allowed to progress. -/
theorem tick_extend_active (right config : V) (hc : ¬ Stopped config) :
    tickValue (extendValue right config) = extendValue right (tickValue config) := by
  have h0 : config ≠ 0 := fun h => hc (Or.inl h)
  have hw : remaining config ≠ 0 := fun h => hc (Or.inr h)
  have hcfg : liveValue ((remaining config-1)+1) (working config) = config := by
    rw [pred_add_one (remaining config) hw]
    exact live_decode config h0
  simpa only [hcfg] using tick_extend_succ right (remaining config-1) (working config)

/-- Once an internal time run is stopped, every later time has the same state. -/
theorem run_eq_of_stopped_le (first second initial : V) (hle : first ≤ second)
    (hs : Stopped (run first initial)) : run second initial = run first initial := by
  have hdecomp : second = first + (second-first) := Arithmetic.sub_spec_of_ge hle
  rw [hdecomp, run_add, run_stopped _ _ hs]

/-- Determinism and absorption identify any two stopped times, without an
assumption about which of the two numerical time bounds is larger. -/
theorem stopped_runs_eq (first second initial : V)
    (hf : Stopped (run first initial)) (hs : Stopped (run second initial)) :
    run first initial = run second initial := by
  by_cases hle : first ≤ second
  · exact (run_eq_of_stopped_le first second initial hle hf).symm
  · exact run_eq_of_stopped_le second first initial (le_of_not_ge hle) hs

/-- The word-code terminal time agrees with any stopped witness time. -/
theorem terminal_eq_run (word w time : V)
    (hs : Stopped (run time (liveValue word w))) :
    terminal word w = run time (liveValue word w) :=
  stopped_runs_eq word time _ (terminal_stopped word w) hs

/-- The first tick executes the raw head; shifted word1 therefore executes MP0. -/
theorem run_one_succ (raw w : V) :
    run 1 (liveValue (raw+1) w) = nextValue raw w := by
  simpa only [zero_add,run_zero,tick_live_succ] using
    run_succ (0 : V) (liveValue (raw+1) w)

/-- Internal successor-word execution, before projecting the result convention. -/
theorem terminal_succ (raw w : V) :
    terminal (raw+1) w =
      if ArithmeticCommandStep254.stepValue raw w = 0 then 0
      else terminal (tailValue raw) (ArithmeticCommandStep254.stepValue raw w-1) := by
  by_cases hs : ArithmeticCommandStep254.stepValue raw w = 0
  · have hfirst : run 1 (liveValue (raw+1) w) = 0 := by
      simp only [run_one_succ,nextValue,hs,if_pos]
    have hstop : Stopped (run 1 (liveValue (raw+1) w)) := Or.inl hfirst
    rw [if_pos hs,terminal_eq_run _ _ 1 hstop,hfirst]
  · have hfirst : run 1 (liveValue (raw+1) w) =
        liveValue (tailValue raw) (ArithmeticCommandStep254.stepValue raw w-1) := by
      simp only [run_one_succ,nextValue,hs,if_false]
    have hfinal : run (1+tailValue raw) (liveValue (raw+1) w) =
        terminal (tailValue raw) (ArithmeticCommandStep254.stepValue raw w-1) := by
      rw [run_add,hfirst]
      rfl
    have hstop : Stopped (run (1+tailValue raw) (liveValue (raw+1) w)) := by
      rw [hfinal]
      exact terminal_stopped _ _
    rw [if_neg hs,terminal_eq_run _ _ (1+tailValue raw) hstop,hfinal]

/-- One raw head then the represented shifted tail, with halt0 distinct from
successful zero working state1. The positive branch alone uses result-1. -/
theorem eval_succ (raw w : V) :
    evalValue (raw+1) w =
      if ArithmeticCommandStep254.stepValue raw w = 0 then 0
      else evalValue (tailValue raw) (ArithmeticCommandStep254.stepValue raw w-1) := by
  by_cases hs : ArithmeticCommandStep254.stepValue raw w = 0 <;>
    simp [evalValue,terminal_succ,hs]

/-- A bounded stopped-pair witness, or the two evaluators are still paired.
Every non-time parameter stays fixed during this Sigma1 induction. No least
stopping-time operator and no bounded universal search are required. -/
theorem paired_or_stopped (time left right w : V) :
    (∃ t ≤ time, Stopped (run t (liveValue left w)) ∧
      run t (liveValue (appendValue left right) w) =
        extendValue right (run t (liveValue left w))) ∨
    run time (liveValue (appendValue left right) w) =
      extendValue right (run time (liveValue left w)) := by
  induction time using ISigma1.sigma1_succ_induction
  · unfold Stopped
    definability
  case zero => right; simp
  case succ time ih =>
    rcases ih with ⟨t, ht, hs, hp⟩ | hp
    · left
      exact ⟨t, le_trans ht (by simp), hs, hp⟩
    · by_cases hs : Stopped (run time (liveValue left w))
      · left
        exact ⟨time, by simp, hs, hp⟩
      · right
        rw [run_succ, run_succ, hp, tick_extend_active right _ hs]

/-- Drain left to obtain some stopped pair before its own word-code bound.
The witness is sufficient; no minimality or external finiteness is assumed. -/
theorem stopped_pair (left right w : V) :
    ∃ t ≤ left, Stopped (run t (liveValue left w)) ∧
      run t (liveValue (appendValue left right) w) =
        extendValue right (terminal left w) := by
  rcases paired_or_stopped left left right w with ⟨t,ht,hs,hp⟩ | hp
  · exact ⟨t,ht,hs,by rw [terminal_eq_run left w t hs]; exact hp⟩
  · exact ⟨left,le_rfl,terminal_stopped left w,hp⟩

/-- Actual terminal execution of append: halt on the left is absorbing;
successful left completion starts the right word on its resulting state.
No lower bound on the numerical append code is needed. -/
theorem terminal_append (left right w : V) :
    terminal (appendValue left right) w =
      if terminal left w = 0 then 0 else terminal right (working (terminal left w)) := by
  obtain ⟨t,_,hs,hp⟩ := stopped_pair left right w
  by_cases h0 : terminal left w = 0
  · have hb : run t (liveValue (appendValue left right) w) = 0 := by
      simpa only [h0,extend_zero] using hp
    have hbstop : Stopped (run t (liveValue (appendValue left right) w)) := Or.inl hb
    rw [if_pos h0,terminal_eq_run _ _ t hbstop,hb]
  · have hw : remaining (terminal left w) = 0 := by
      rcases terminal_stopped left w with hh | hh
      · exact False.elim (h0 hh)
      · exact hh
    have hleft : liveValue 0 (working (terminal left w)) = terminal left w := by
      simpa only [hw] using live_decode (terminal left w) h0
    have hb : run t (liveValue (appendValue left right) w) =
        liveValue right (working (terminal left w)) := by
      rw [←hleft,extend_done] at hp
      exact hp
    have hfinal : run (t+right) (liveValue (appendValue left right) w) =
        terminal right (working (terminal left w)) := by
      rw [run_add,hb]
      rfl
    have hstop : Stopped (run (t+right) (liveValue (appendValue left right) w)) := by
      rw [hfinal]
      exact terminal_stopped _ _
    rw [if_neg h0,terminal_eq_run _ _ (t+right) hstop,hfinal]

/-- Encoded Option composition on every internal pair of shifted words.
The predecessor is used only in the positive successful-left branch. -/
theorem eval_append (left right w : V) :
    evalValue (appendValue left right) w =
      if evalValue left w = 0 then 0 else evalValue right (evalValue left w-1) := by
  by_cases h0 : terminal left w = 0 <;>
    simp [evalValue,terminal_append,h0]

/-- Halting either occurs during left, or during right after a positive left
result. Successful completion is not silently classified as halting. -/
theorem eval_append_eq_zero (left right w : V) :
    evalValue (appendValue left right) w = 0 ↔
      evalValue left w = 0 ∨
      (evalValue left w ≠ 0 ∧ evalValue right (evalValue left w-1) = 0) := by
  rw [eval_append]
  by_cases hl : evalValue left w = 0 <;> simp [hl]

end SetTheory.BusyBeaver.ZFC.ArithmeticCommandExecution254

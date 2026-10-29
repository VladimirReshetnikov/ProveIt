import DiophantineConsistency.ArithmeticCommandAppendPerm222
import DiophantineConsistency.ArithmeticCommandEvaluationPerm222

/-! Actual all-internal C222 append execution. A bounded stopped witness
retains coupling while the left word is active, then starts the right word
on positive success. Halt0 remains distinct. This is not a compiler contract
or consistency equivalence. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticCommandCompositionPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandWordPerm222 ArithmeticCommandReplacePerm222
open ArithmeticCommandAppendPerm222 ArithmeticCommandTickPerm222
open ArithmeticCommandRunPerm222 ArithmeticCommandEvaluationPerm222
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
  simp only [nextValue, step_replace, tail_replace]
  split <;> simp

/-- The local commuting law is needed only while the left evaluator is active.
After left completion, the appended continuation is allowed to progress. -/
theorem tick_extend_active (right config : V) (hc : ¬ Stopped config) :
    tickValue (extendValue right config) = extendValue right (tickValue config) := by
  simpa only [live_decode_active config hc] using
    tick_extend_succ right (remaining config-1) (working config)

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
  · have hw := (terminal_stopped left w).resolve_left h0
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

theorem eval_append_halt (left right w : V) (h : evalValue left w=0) :
    evalValue (appendValue left right) w=0 := by rw [eval_append,if_pos h]

theorem eval_append_success (left right w result : V)
    (h : evalValue left w=result+1) :
    evalValue (appendValue left right) w=evalValue right result := by
  rw [eval_append,h]
  simp

end DiophantineConsistency.ArithmeticCommandCompositionPerm222

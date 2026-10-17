import BusyBeaver.ZFC.ArithmeticEnumeratorStep254
import BusyBeaver.ZFC.ArithmeticCommandExecution254

/-!
Internal iteration and fair candidate reach for the literal Enum254 scheduler.
The time invariant freezes a bounded witness as soon as the paired word has
stopped: scheduler boundaries resume enumeration and are not absorbing.
All codes, times, candidate indices and working states range over an arbitrary
IΣ1 model. No external-list or standard-code assumption is used. No binary
simulation or PA consistency translation is asserted by this module.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254 ArithmeticCommandWord254
open ArithmeticEnumeratorStep254
open ArithmeticCommandTick254 (Stopped)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance live_definable : 𝚺₁-Function₃[V] liveValue := live_defined.to_definable

/-- A word-evaluator configuration is embedded with a fixed next candidate. -/
noncomputable def embedValue (np config : V) : V :=
  if config = 0 then 0 else liveValue (ArithmeticCommandTick254.remaining config) np
    (ArithmeticCommandTick254.working config)

def embedDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out np config. (config = 0 ∧ out = 0) ∨
    (config ≠ 0 ∧ ∃ word, !ArithmeticCommandTick254.remainingDef word config ∧
      ∃ w, !ArithmeticCommandTick254.workingDef w config ∧ !liveDef out word np w)”
instance embed_defined : 𝚺₁-Function₂[V] embedValue via embedDef := .mk fun e => by
  classical
  by_cases hc : e 2 = 0 <;> simp [embedDef, embedValue, hc]
instance embed_definable : 𝚺₁-Function₂[V] embedValue := embed_defined.to_definable

@[simp] lemma embed_zero (np : V) : embedValue np 0 = 0 := by simp [embedValue]
@[simp] lemma embed_live (np word w : V) :
    embedValue np (ArithmeticCommandTick254.liveValue word w) = liveValue word np w := by
  simp [embedValue]

lemma step_embed_succ (np raw w : V) :
    step (embedValue np (ArithmeticCommandTick254.liveValue (raw+1) w)) =
      embedValue np (ArithmeticCommandTick254.tickValue
        (ArithmeticCommandTick254.liveValue (raw+1) w)) := by
  rw [embed_live, step_active _ _ _ (by simp), ArithmeticCommandTick254.tick_live_succ]
  by_cases hs : stepValue raw w = 0
  · simp [advanceValue, ArithmeticCommandTick254.nextValue, hs]
  · simp [advanceValue, ArithmeticCommandTick254.nextValue, hs]

/-- Local conjugacy is asserted only while the word is active. -/
lemma step_embed_active (np config : V) (hc : ¬ Stopped config) :
    step (embedValue np config) =
      embedValue np (ArithmeticCommandTick254.tickValue config) := by
  have h0 : config ≠ 0 := fun h => hc (Or.inl h)
  have hw : ArithmeticCommandTick254.remaining config ≠ 0 := fun h => hc (Or.inr h)
  have he : ArithmeticCommandTick254.liveValue
      ((ArithmeticCommandTick254.remaining config-1)+1)
      (ArithmeticCommandTick254.working config) = config := by
    rw [ArithmeticCommandTick254.pred_add_one _ hw]
    exact ArithmeticCommandTick254.live_decode config h0
  simpa only [he] using step_embed_succ np
    (ArithmeticCommandTick254.remaining config-1) (ArithmeticCommandTick254.working config)

def zeroDef : 𝚺₁.Semisentence 2 := .mkSigma “out initial. out = initial”
def succDef : 𝚺₁.Semisentence 4 := .mkSigma
  “out previous index initial. !ArithmeticEnumeratorStep254.stepDef out previous”
def blueprint : PR.Blueprint 1 where
  zero := zeroDef
  succ := succDef
noncomputable def construction : PR.Construction V blueprint where
  zero parameters := parameters 0
  succ _ _ previous := step previous
  zero_defined := .mk fun e => by simp [blueprint, zeroDef]
  succ_defined := .mk fun e => by simp [blueprint, succDef]

noncomputable def run (time initial : V) : V := construction.result ![initial] time

def runDef : 𝚺₁.Semisentence 3 := blueprint.resultDef
def runDeltaDef : 𝚫₁.Semisentence 3 := blueprint.resultDeltaDef
instance run_defined : 𝚺₁-Function₂[V] run via runDef := .mk fun e => by
  have he : (fun i : Fin 1 => e i.succ.succ) = ![e 2] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have h := (construction (V := V)).result_defined.df e
  change blueprint.resultDef.val.Evalb e ↔
    e 0 = construction.result (fun i : Fin 1 => e i.succ.succ) (e 1) at h
  rw [he] at h
  change blueprint.resultDef.val.Evalb e ↔ e 0 = construction.result ![e 2] (e 1)
  exact h
instance run_defined_delta : 𝚫₁-Function₂[V] run via runDeltaDef := run_defined.graph_delta
instance run_definable : 𝚺₁-Function₂[V] run := run_defined.to_definable

@[simp] theorem run_zero (initial : V) : run 0 initial = initial := by
  simp [run, construction]
@[simp] theorem run_succ (time initial : V) : run (time+1) initial = step (run time initial) := by
  simp [run, PR.Construction.result_succ, construction]
@[simp] theorem run_halted (time : V) : run time 0 = 0 := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ time ih => rw [run_succ, ih, step_zero]

theorem run_add (first second initial : V) :
    run (first+second) initial = run second (run first initial) := by
  induction second using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ second ih => rw [←add_assoc, run_succ, run_succ, ih]

theorem run_one (initial : V) : run 1 initial = step initial := by
  simpa only [zero_add, run_zero] using run_succ (0 : V) initial

theorem run_total (time initial : V) : ∃! out, runDef.val.Evalb ![out,time,initial] := by simp

/-- After the first stopped word time, retain that bounded witness instead
of asserting that the scheduler remains paired at later times. -/
theorem paired_or_stopped (time word np w : V) :
    (∃ t ≤ time, Stopped (ArithmeticCommandRun254.run t
        (ArithmeticCommandTick254.liveValue word w)) ∧
      run t (liveValue word np w) = embedValue np (ArithmeticCommandRun254.run t
        (ArithmeticCommandTick254.liveValue word w))) ∨
    run time (liveValue word np w) = embedValue np (ArithmeticCommandRun254.run time
      (ArithmeticCommandTick254.liveValue word w)) := by
  induction time using ISigma1.sigma1_succ_induction
  · unfold Stopped
    definability
  case zero => right; simp
  case succ time ih =>
    rcases ih with ⟨t, ht, hs, hp⟩ | hp
    · left
      exact ⟨t, le_trans ht (by simp), hs, hp⟩
    · by_cases hs : Stopped (ArithmeticCommandRun254.run time
          (ArithmeticCommandTick254.liveValue word w))
      · left
        exact ⟨time, by simp, hs, hp⟩
      · right
        rw [run_succ, ArithmeticCommandRun254.run_succ, hp, step_embed_active np _ hs]

/-- Stop somewhere before the word bound; do not run the scheduler blindly
for that whole bound after it has already resumed at a boundary. -/
theorem drain_terminal (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w) = embedValue np (ArithmeticCommandRun254.terminal word w) := by
  rcases paired_or_stopped word word np w with ⟨t, ht, hs, hp⟩ | hp
  · exact ⟨t, ht, by rw [ArithmeticCommandExecution254.terminal_eq_run word w t hs]; exact hp⟩
  · exact ⟨word, le_rfl, hp⟩

lemma embed_terminal_eval (word np w : V) :
    embedValue np (ArithmeticCommandRun254.terminal word w) =
      if ArithmeticCommandRun254.evalValue word w = 0 then 0
      else liveValue 0 np (ArithmeticCommandRun254.evalValue word w-1) := by
  by_cases ht : ArithmeticCommandRun254.terminal word w = 0
  · simp [ArithmeticCommandRun254.evalValue, embedValue, ht]
  · have hw : ArithmeticCommandTick254.remaining (ArithmeticCommandRun254.terminal word w) = 0 := by
      rcases ArithmeticCommandRun254.terminal_stopped word w with h0 | hw
      · exact False.elim (ht h0)
      · exact hw
    simp [ArithmeticCommandRun254.evalValue, embedValue, ht, hw]

theorem drain (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w) =
      if ArithmeticCommandRun254.evalValue word w = 0 then 0
      else liveValue 0 np (ArithmeticCommandRun254.evalValue word w-1) := by
  obtain ⟨t, ht, he⟩ := drain_terminal word np w
  exact ⟨t, ht, (he.trans (embed_terminal_eval word np w))⟩

/-- Execute a whole raw candidate, counting its first fetched head once.
Raw candidate c corresponds to shifted command word c+1. -/
theorem drain_boundary (c w : V) : ∃ t ≤ c+1,
    run t (liveValue 0 c w) =
      if ArithmeticCommandRun254.evalValue (c+1) w = 0 then 0
      else liveValue 0 (c+1) (ArithmeticCommandRun254.evalValue (c+1) w-1) := by
  have hfirst : run 1 (liveValue 0 c w) = advanceValue c (c+1) w := by
    rw [run_one, step_boundary]
  by_cases hs : stepValue c w = 0
  · refine ⟨1, by simp, ?_⟩
    rw [hfirst]
    simp [advanceValue, ArithmeticCommandExecution254.eval_succ, hs]
  · have hf : run 1 (liveValue 0 c w) =
        liveValue (tailValue c) (c+1) (stepValue c w-1) := by
      simpa [advanceValue, hs] using hfirst
    obtain ⟨t, ht, he⟩ := drain (tailValue c) (c+1) (stepValue c w-1)
    refine ⟨1+t, ?_, ?_⟩
    · calc
        1+t ≤ 1+c := _root_.add_le_add le_rfl (le_trans ht (tailValue_le c))
        _ = c+1 := add_comm _ _
    · rw [run_add, hf, he, ArithmeticCommandExecution254.eval_succ]
      simp only [hs, if_false]

/-- Every internal candidate boundary is reached, unless the scheduler has
already halted. The changing time/state witnesses are existential Sigma1. -/
theorem reach (c initialWork : V) : ∃ time,
    run time (liveValue 0 0 initialWork) = 0 ∨
    ∃ w, run time (liveValue 0 0 initialWork) = liveValue 0 c w := by
  induction c using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, Or.inr ⟨initialWork, run_zero _⟩⟩
  case succ c ih =>
    obtain ⟨time, ih⟩ := ih
    rcases ih with hh | ⟨w, hw⟩
    · exact ⟨time, Or.inl hh⟩
    · obtain ⟨t, _, he⟩ := drain_boundary c w
      refine ⟨time+t, ?_⟩
      rw [run_add, hw, he]
      by_cases hv : ArithmeticCommandRun254.evalValue (c+1) w = 0
      · exact Or.inl (if_pos hv)
      · exact Or.inr ⟨ArithmeticCommandRun254.evalValue (c+1) w-1, if_neg hv⟩

/-- Any nonempty internal word halting from every working state is scheduled.
The target raw candidate is word-1, not word. -/
theorem halts_of_word (word initialWork : V) (hp : word ≠ 0)
    (hall : ∀ w, ArithmeticCommandRun254.evalValue word w = 0) :
    ∃ time, run time (liveValue 0 0 initialWork) = 0 := by
  obtain ⟨time, hh | ⟨w, hw⟩⟩ := reach (word-1) initialWork
  · exact ⟨time, hh⟩
  · obtain ⟨t, _, he⟩ := drain_boundary (word-1) w
    rw [ArithmeticCommandTick254.pred_add_one word hp, hall w, if_pos rfl] at he
    exact ⟨time+t, by rw [run_add, hw, he]⟩

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorRun254

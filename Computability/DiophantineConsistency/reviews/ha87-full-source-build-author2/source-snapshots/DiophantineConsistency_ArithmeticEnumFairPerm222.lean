import DiophantineConsistency.ArithmeticEnumRunPerm222
import DiophantineConsistency.ArithmeticCommandEvaluationPerm222

/-! Internal fair reach for actual permuted C222 enumeration, with an arbitrary
initial candidate (in particular4). A bounded stopped-time witness is frozen
before the scheduler resumes enumeration. All codes and times are internal.
This proves no compiler/proof-state invariant or exact215 simulation. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumFairPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandStepPerm222 ArithmeticCommandWordPerm222
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222
open ArithmeticCommandTickPerm222 (Stopped)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma enum_active (raw np w : V) :
    enumValue (liveValue (raw+1) np w)=execValue raw np w := by
  simp only [enum_live,ArithmeticCommandFetchPerm222.raw_continuation,
    ArithmeticCommandFetchPerm222.next_continuation]

lemma enum_boundary (np w : V) :
    enumValue (liveValue 0 np w)=execValue np (np+1) w := by
  simp only [enum_live,ArithmeticCommandFetchPerm222.raw_new,
    ArithmeticCommandFetchPerm222.next_new]

local instance live_definable : 𝚺₁-Function₃[V] liveValue := live_defined.to_definable

/-- A word-evaluator configuration is embedded with a fixed next candidate. -/
noncomputable def embedValue (np config : V) : V :=
  if config = 0 then 0 else liveValue (ArithmeticCommandTickPerm222.remaining config) np
    (ArithmeticCommandTickPerm222.working config)

def embedDef : 𝚺₁.Semisentence 3 := .mkSigma
  “out np config. (config = 0 ∧ out = 0) ∨
    (config ≠ 0 ∧ ∃ word, !ArithmeticCommandTickPerm222.remainingDef word config ∧
      ∃ w, !ArithmeticCommandTickPerm222.workingDef w config ∧ !liveDef out word np w)”
instance embed_defined : 𝚺₁-Function₂[V] embedValue via embedDef := .mk fun e => by
  classical
  by_cases hc : e 2 = 0 <;> simp [embedDef, embedValue, hc]
instance embed_definable : 𝚺₁-Function₂[V] embedValue := embed_defined.to_definable

@[simp] lemma embed_zero (np : V) : embedValue np 0 = 0 := by simp [embedValue]
@[simp] lemma embed_live (np word w : V) :
    embedValue np (ArithmeticCommandTickPerm222.liveValue word w) = liveValue word np w := by
  simp [embedValue]

lemma enum_embed_succ (np raw w : V) :
    enumValue (embedValue np (ArithmeticCommandTickPerm222.liveValue (raw+1) w)) =
      embedValue np (ArithmeticCommandTickPerm222.tickValue
        (ArithmeticCommandTickPerm222.liveValue (raw+1) w)) := by
  rw [embed_live, enum_active, ArithmeticCommandTickPerm222.tick_live_succ]
  by_cases hs : stepValue raw w = 0 <;>
    simp [execValue, ArithmeticCommandTickPerm222.nextValue, hs]

/-- Local conjugacy is asserted only while the word is active. -/
lemma enum_embed_active (np config : V) (hc : ¬ Stopped config) :
    enumValue (embedValue np config) =
      embedValue np (ArithmeticCommandTickPerm222.tickValue config) := by
  simpa only [ArithmeticCommandTickPerm222.live_decode_active config hc] using
    enum_embed_succ np (ArithmeticCommandTickPerm222.remaining config-1)
      (ArithmeticCommandTickPerm222.working config)

/-- After the first stopped word time, retain that bounded witness instead
of asserting that the scheduler remains paired at later times. -/
theorem paired_or_stopped (time word np w : V) :
    (∃ t ≤ time, Stopped (ArithmeticCommandRunPerm222.run t
        (ArithmeticCommandTickPerm222.liveValue word w)) ∧
      run t (liveValue word np w) = embedValue np (ArithmeticCommandRunPerm222.run t
        (ArithmeticCommandTickPerm222.liveValue word w))) ∨
    run time (liveValue word np w) = embedValue np (ArithmeticCommandRunPerm222.run time
      (ArithmeticCommandTickPerm222.liveValue word w)) := by
  induction time using ISigma1.sigma1_succ_induction
  · unfold Stopped
    definability
  case zero => right; simp
  case succ time ih =>
    rcases ih with ⟨t, ht, hs, hp⟩ | hp
    · left
      exact ⟨t, le_trans ht (by simp), hs, hp⟩
    · by_cases hs : Stopped (ArithmeticCommandRunPerm222.run time
          (ArithmeticCommandTickPerm222.liveValue word w))
      · left
        exact ⟨time, by simp, hs, hp⟩
      · right
        rw [run_succ, ArithmeticCommandRunPerm222.run_succ, hp, enum_embed_active np _ hs]

/-- Stop somewhere before the word bound; do not run the scheduler blindly
for that whole bound after it has already resumed at a boundary. -/
theorem drain_terminal (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w) = embedValue np (ArithmeticCommandRunPerm222.terminal word w) := by
  rcases paired_or_stopped word word np w with ⟨t, ht, hs, hp⟩ | hp
  · exact ⟨t, ht, by rw [ArithmeticCommandEvaluationPerm222.terminal_eq_run word w t hs]; exact hp⟩
  · exact ⟨word, le_rfl, hp⟩

lemma embed_terminal_eval (word np w : V) :
    embedValue np (ArithmeticCommandRunPerm222.terminal word w) =
      if ArithmeticCommandRunPerm222.evalValue word w = 0 then 0
      else liveValue 0 np (ArithmeticCommandRunPerm222.evalValue word w-1) := by
  by_cases ht : ArithmeticCommandRunPerm222.terminal word w = 0
  · simp [ArithmeticCommandRunPerm222.evalValue, embedValue, ht]
  · have hw := (ArithmeticCommandRunPerm222.terminal_stopped word w).resolve_left ht
    simp [ArithmeticCommandRunPerm222.evalValue, embedValue, ht, hw]

theorem drain (word np w : V) : ∃ t ≤ word,
    run t (liveValue word np w) =
      if ArithmeticCommandRunPerm222.evalValue word w = 0 then 0
      else liveValue 0 np (ArithmeticCommandRunPerm222.evalValue word w-1) := by
  obtain ⟨t, ht, he⟩ := drain_terminal word np w
  exact ⟨t, ht, (he.trans (embed_terminal_eval word np w))⟩

/-- Execute a whole raw candidate, counting its first fetched head once.
Raw candidate c corresponds to shifted command word c+1. -/
theorem drain_boundary (c w : V) : ∃ t ≤ c+1,
    run t (liveValue 0 c w) =
      if ArithmeticCommandRunPerm222.evalValue (c+1) w = 0 then 0
      else liveValue 0 (c+1) (ArithmeticCommandRunPerm222.evalValue (c+1) w-1) := by
  have hfirst : run 1 (liveValue 0 c w) = execValue c (c+1) w := by
    rw [run_one, enum_boundary]
  by_cases hs : stepValue c w = 0
  · refine ⟨1, by simp, ?_⟩
    rw [hfirst]
    simp [execValue, ArithmeticCommandEvaluationPerm222.eval_succ, hs]
  · have hf : run 1 (liveValue 0 c w) =
        liveValue (tailValue c) (c+1) (stepValue c w-1) := by
      simpa [execValue, hs] using hfirst
    obtain ⟨t, ht, he⟩ := drain (tailValue c) (c+1) (stepValue c w-1)
    refine ⟨1+t, ?_, ?_⟩
    · simpa only [add_comm] using _root_.add_le_add (le_refl (1 : V)) (le_trans ht (tail_le c))
    · rw [run_add, hf, he, ArithmeticCommandEvaluationPerm222.eval_succ]
      simp only [hs, if_false]

/-- `reach_offset` with the summed drain costs as an explicit bound. -/
theorem reach_offset_bounded (offset initialCandidate initialWork : V) :
    ∃ time ≤ offset * (initialCandidate + offset),
      run time (liveValue 0 initialCandidate initialWork) = 0 ∨
      ∃ w, run time (liveValue 0 initialCandidate initialWork) =
        liveValue 0 (initialCandidate+offset) w := by
  induction offset using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, by simp, .inr ⟨initialWork, by simp⟩⟩
  case succ offset ih =>
    obtain ⟨time, htime, hh | ⟨w, hw⟩⟩ := ih
    · refine ⟨time, le_trans htime ?_, .inl hh⟩
      exact mul_le_mul (le_self_add) (_root_.add_le_add le_rfl le_self_add)
        (Arithmetic.zero_le _) (Arithmetic.zero_le _)
    · obtain ⟨t, ht, he⟩ := drain_boundary (initialCandidate+offset) w
      have hb : time + t ≤ (offset+1) * (initialCandidate + (offset+1)) := by
        have h1 : offset * (initialCandidate + offset) ≤ offset * (initialCandidate + (offset+1)) :=
          mul_le_mul_of_nonneg_left (_root_.add_le_add le_rfl le_self_add) (Arithmetic.zero_le _)
        calc time + t ≤ offset * (initialCandidate + (offset+1)) + (initialCandidate + offset + 1) :=
              _root_.add_le_add (le_trans htime h1) ht
          _ = (offset+1) * (initialCandidate + (offset+1)) := by ring
      refine ⟨time+t, hb, ?_⟩
      rw [run_add, hw, he]
      by_cases hv : ArithmeticCommandRunPerm222.evalValue ((initialCandidate+offset)+1) w = 0
      · exact Or.inl (if_pos hv)
      · exact Or.inr ⟨ArithmeticCommandRunPerm222.evalValue ((initialCandidate+offset)+1) w-1,
          by rw [if_neg hv]; simp only [add_assoc]⟩

/-- `halts_of_word` with the explicit bound `word * word`. -/
theorem halts_of_word_bounded (word initialCandidate initialWork : V) (hp : word ≠ 0)
    (hindex : initialCandidate ≤ word-1)
    (hall : ∀ w, ArithmeticCommandRunPerm222.evalValue word w = 0) :
    ∃ time ≤ word * word, run time (liveValue 0 initialCandidate initialWork) = 0 := by
  obtain ⟨x, rfl⟩ : ∃ x, word = x + 1 :=
    ⟨word - 1, (ArithmeticCommandTickPerm222.pred_add_one word hp).symm⟩
  have hx : x + 1 - 1 = x := add_tsub_cancel_right x 1
  rw [hx] at hindex
  have he : x = initialCandidate + (x - initialCandidate) := Arithmetic.sub_spec_of_ge hindex
  have hoff : (x - initialCandidate) * (initialCandidate + (x - initialCandidate)) ≤ x * x := by
    rw [← he]
    exact mul_le_mul_of_nonneg_right tsub_le_self (Arithmetic.zero_le _)
  have hsq : x * x + (x + 1) ≤ (x + 1) * (x + 1) := by
    have hr : (x + 1) * (x + 1) = x * x + x + (x + 1) := by ring
    rw [hr]
    exact _root_.add_le_add le_self_add le_rfl
  obtain ⟨time, htime, hh | ⟨w, hw⟩⟩ :=
    reach_offset_bounded (x - initialCandidate) initialCandidate initialWork
  · exact ⟨time, le_trans htime (le_trans hoff (le_trans le_self_add hsq)), hh⟩
  · rw [← he] at hw
    obtain ⟨t, ht, hd⟩ := drain_boundary x w
    rw [hall w, if_pos rfl] at hd
    refine ⟨time+t, ?_, by rw [run_add, hw, hd]⟩
    exact le_trans (_root_.add_le_add (le_trans htime hoff) ht) hsq

/-- Every offset boundary is reached unless an earlier command halts.
The induction changes only the offset; its time/work witnesses are Sigma1. -/
theorem reach_offset (offset initialCandidate initialWork : V) : ∃ time,
    run time (liveValue 0 initialCandidate initialWork)=0 ∨
    ∃ w, run time (liveValue 0 initialCandidate initialWork)=
      liveValue 0 (initialCandidate+offset) w := by
  obtain ⟨time, _, h⟩ := reach_offset_bounded offset initialCandidate initialWork
  exact ⟨time, h⟩

/-- Candidate indices below the starting counter are deliberately excluded. -/
theorem reach_of_le (candidate initialCandidate initialWork : V)
    (h : initialCandidate ≤ candidate) : ∃ time,
    run time (liveValue 0 initialCandidate initialWork)=0 ∨
    ∃ w, run time (liveValue 0 initialCandidate initialWork)=liveValue 0 candidate w := by
  have he : candidate=initialCandidate+(candidate-initialCandidate) := Arithmetic.sub_spec_of_ge h
  simpa only [←he] using reach_offset (candidate-initialCandidate) initialCandidate initialWork

/-- The actual C222 scheduler starts at raw candidate4. -/
theorem reach_from_four (candidate initialWork : V) (h : 4 ≤ candidate) : ∃ time,
    run time (liveValue 0 4 initialWork)=0 ∨
    ∃ w, run time (liveValue 0 4 initialWork)=liveValue 0 candidate w :=
  reach_of_le candidate 4 initialWork h

/-- A universally halting word is scheduled only when its raw candidate is
at or above the initial counter. Word-1 is the candidate; word is shifted. -/
theorem halts_of_word (word initialCandidate initialWork : V) (hp : word≠0)
    (hindex : initialCandidate ≤ word-1)
    (hall : ∀ w,ArithmeticCommandRunPerm222.evalValue word w=0) :
    ∃ time,run time (liveValue 0 initialCandidate initialWork)=0 := by
  obtain ⟨time, _, h⟩ := halts_of_word_bounded word initialCandidate initialWork hp hindex hall
  exact ⟨time, h⟩

end DiophantineConsistency.ArithmeticEnumFairPerm222

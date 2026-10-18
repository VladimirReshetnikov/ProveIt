import BusyBeaver.ZFC.ArithmeticEnumeratorEquivalence254

set_option autoImplicit false
noncomputable section

/-!
The represented scheduler at NP=3 and working fields TW=WS=H=0,D=3.
Candidate reach is generalized to an arbitrary internal starting index. The
existing refutation word has raw code at least3, and the initial working state
is certified because its D field has no proof obligation. This is an internal
scheduler/validator equivalence, not a binary-machine or ZFC proof-code bridge.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticCommandStep254
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
open ArithmeticEnumeratorSoundness254 ArithmeticRefutationWord254
open ArithmeticStackCertificate254
open ArithmeticCommandBlockExecution254 (axWord)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance live_definable : 𝚺₁-Function₃[V] liveValue := live_defined.to_definable

/-- Every candidate at or above the initial base is reached or a prior halt
has already occurred. The induction invariant has only existential witnesses. -/
theorem reach_from (base offset initialWork : V) : ∃ time,
    run time (liveValue 0 base initialWork) = 0 ∨
    ∃ w, run time (liveValue 0 base initialWork) = liveValue 0 (base+offset) w := by
  induction offset using ISigma1.sigma1_succ_induction
  · definability
  case zero => exact ⟨0, Or.inr ⟨initialWork, by simp⟩⟩
  case succ offset ih =>
    obtain ⟨time, ih⟩ := ih
    rcases ih with hh | ⟨w, hw⟩
    · exact ⟨time, Or.inl hh⟩
    · obtain ⟨t, _, he⟩ := drain_boundary (base+offset) w
      refine ⟨time+t, ?_⟩
      rw [run_add, hw, he]
      by_cases hv : ArithmeticCommandRun254.evalValue (base+offset+1) w = 0
      · exact Or.inl (if_pos hv)
      · refine Or.inr ⟨ArithmeticCommandRun254.evalValue (base+offset+1) w-1, ?_⟩
        rw [if_neg hv]
        simp only [add_assoc]

/-- A uniformly halting word is scheduled when its raw candidate is no smaller
than the initial counter. No condition is imposed on the initial working code. -/
theorem halts_of_word_from (base word initialWork : V) (hp : word ≠ 0)
    (hb : base ≤ word-1)
    (hall : ∀ w, ArithmeticCommandRun254.evalValue word w = 0) :
    ∃ time, run time (liveValue 0 base initialWork) = 0 := by
  obtain ⟨time, hh | ⟨w, hw⟩⟩ := reach_from base (word-1-base) initialWork
  · exact ⟨time, hh⟩
  · rw [add_tsub_cancel_of_le hb] at hw
    obtain ⟨t, _, he⟩ := drain_boundary (word-1) w
    rw [ArithmeticCommandTick254.pred_add_one word hp, hall w, if_pos rfl] at he
    exact ⟨time+t, by rw [run_add, hw, he]⟩

/-- Its literal leading AX tag is3, independently of proof acceptance. -/
theorem refutationWord_raw_bound (code : V) : 3 ≤ refutationWord code-1 := by
  unfold refutationWord axWord
  simp only [zero_add, add_tsub_cancel_right]
  exact (components_le _ _).1

theorem halts_of_accepted_from_three (code initialWork : V)
    (hv : ArithmeticHistory254.value code = 2) :
    ∃ time, run time (liveValue 0 3 initialWork) = 0 :=
  halts_of_word_from 3 (refutationWord code) initialWork
    (refutationWord_ne_zero code) (refutationWord_raw_bound code)
    (fun w => eval_refutationWord code w hv)

/-- Arbitrary D is permitted: only top, stack and cache need proof witnesses. -/
theorem certified_seed_work (d : V) : CertifiedWorking (stateValue 0 0 d 0) := by
  refine ⟨1, ?_⟩
  rw [stateValue, working_fields]
  exact ⟨prov_truth le_rfl, prov_truth le_rfl, stack_zero le_rfl⟩

noncomputable def seedValue : V := liveValue 0 3 (stateValue 0 0 3 0)

/-- The two scheduler coordinates are exactly the reported seed coordinates. -/
theorem seed_projections : pointer (seedValue (V := V)) = 0 ∧
    candidate (seedValue (V := V)) = 3 ∧
    working (seedValue (V := V)) = stateValue 0 0 3 0 := by
  simp only [seedValue, pointer_live, candidate_live, working_live, and_self]

/-- All proof-code and time witnesses are internal arithmetic-model values. -/
theorem accepted_iff_seed_halts :
    (∃ code : V, ArithmeticHistory254.value code = 2) ↔
      (∃ time : V, run time (seedValue (V := V)) = 0) := by
  constructor
  · rintro ⟨code, hv⟩
    exact halts_of_accepted_from_three code (stateValue 0 0 3 0) hv
  · rintro ⟨time, ht⟩
    exact accepted_of_certified_run_zero time 0 3 (stateValue 0 0 3 0)
      (certified_seed_work 3) ht

/-- Fixed arithmetic graphs spell out the seed; no model-dependent syntax. -/
def equivalenceSentence : ArithmeticSentence :=
  “(∃ code, !ArithmeticHistory254.valueDef 2 code) ↔
    (∃ w, !ArithmeticCommandStep254.stateDef w 0 0 3 0 ∧
      ∃ initial, !ArithmeticEnumeratorStep254.liveDef initial 0 3 w ∧
        ∃ time, !ArithmeticEnumeratorRun254.runDef 0 time initial)”

theorem equivalenceSentence_true : equivalenceSentence.Evalb (M := V) ![] := by
  simp [equivalenceSentence]
  constructor
  · rintro ⟨code, hc⟩
    obtain ⟨time, ht⟩ := accepted_iff_seed_halts.mp ⟨code, hc.symm⟩
    exact ⟨time, ht.symm⟩
  · rintro ⟨time, ht⟩
    obtain ⟨code, hc⟩ := accepted_iff_seed_halts.mpr ⟨time, ht.symm⟩
    exact ⟨code, hc.symm⟩

theorem isigma1_proves_equivalence : 𝗜𝚺₁ ⊢ equivalenceSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (equivalenceSentence_true (V := M))

theorem peano_proves_equivalence : Peano ⊢ equivalenceSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_equivalence

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSeed246

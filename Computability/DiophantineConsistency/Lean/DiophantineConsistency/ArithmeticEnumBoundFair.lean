import DiophantineConsistency.ArithmeticProofWordEnumPerm222

/-! # Refutation ⇒ enumerator halt, with an explicit time bound in the word

`ArithmeticEnumFairPerm222.reach_offset` reaches every candidate boundary by
an unbounded Σ1 induction, although each candidate `c` is drained within
`c+1` steps (`drain_boundary`). Summing these costs gives the explicit bound
`offset * (initialCandidate + offset)` for reaching a boundary, and hence: a
universally halting command word `word` stops the scheduler started at
candidate 4 within `word * word` steps. For an accepted C222 refutation `code`
the word is `resetWord (refutationWord code)`. This module does not bound
`refutationWord` itself in terms of `code`. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumBoundFair
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222 ArithmeticEnumFairPerm222

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance live_definable : 𝚺₁-Function₃[V] liveValue := live_defined.to_definable

/-- `reach_offset` with the summed drain costs as an explicit bound. -/
theorem reach_offset_le (offset initialCandidate initialWork : V) :
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
theorem halts_of_word_le (word initialCandidate initialWork : V) (hp : word ≠ 0)
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
    reach_offset_le (x - initialCandidate) initialCandidate initialWork
  · exact ⟨time, le_trans htime (le_trans hoff (le_trans le_self_add hsq)), hh⟩
  · rw [← he] at hw
    obtain ⟨t, ht, hd⟩ := drain_boundary x w
    rw [hall w, if_pos rfl] at hd
    refine ⟨time+t, ?_, by rw [run_add, hw, hd]⟩
    exact le_trans (_root_.add_le_add (le_trans htime hoff) ht) hsq
end Model

section Correctness
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
open ArithmeticProofWordEnumPerm222 ArithmeticProofWordPerm222

/-- The halting word of a refutation code. -/
noncomputable def refutationResetWord (code : V) : V := resetWord (refutationWord code)

/-- **Refutation ⇒ enumerator halt, bounded by the compiled word.** -/
theorem enum_halts_le_of_refutation (code initialWork : V)
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1]) :
    ∃ time ≤ refutationResetWord code * refutationResetWord code,
      run time (liveValue 0 4 initialWork) = 0 :=
  halts_of_word_le (resetWord (refutationWord code)) 4 initialWork
    (resetWord_ne_zero _) (resetWord_candidate _)
    (resetWord_halts _ (refutationWord_halts code h))

end Correctness
end DiophantineConsistency.ArithmeticEnumBoundFair

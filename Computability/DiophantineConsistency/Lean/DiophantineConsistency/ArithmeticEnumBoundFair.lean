import DiophantineConsistency.ArithmeticProofWordEnumPerm222

/-! # Refutation ⇒ enumerator halt, with an explicit time bound in the word

`ArithmeticEnumFairPerm222.reach_offset_bounded` reaches each boundary or
records an earlier halt by Σ1 induction. Each candidate `c` drains within
`c+1` steps (`drain_boundary`), giving the bound
`offset * (initialCandidate + offset)`. A universally halting word `word`
with `4 ≤ word - 1` stops the scheduler started at candidate 4 within
`word * word` steps. For an accepted C222 refutation `code`, the word is
`resetWord (refutationWord code)`. This module does not bound `refutationWord`
itself in terms of `code`. -/
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
  exact ArithmeticEnumFairPerm222.reach_offset_bounded offset initialCandidate initialWork

/-- `halts_of_word` with the explicit bound `word * word`. -/
theorem halts_of_word_le (word initialCandidate initialWork : V) (hp : word ≠ 0)
    (hindex : initialCandidate ≤ word-1)
    (hall : ∀ w, ArithmeticCommandRunPerm222.evalValue word w = 0) :
    ∃ time ≤ word * word, run time (liveValue 0 initialCandidate initialWork) = 0 := by
  exact ArithmeticEnumFairPerm222.halts_of_word_bounded word initialCandidate initialWork hp hindex hall

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

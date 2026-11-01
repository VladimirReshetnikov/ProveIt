import DiophantineConsistency.ArithmeticProofWordPerm222
import DiophantineConsistency.ArithmeticEnumFairPerm222

/-! An actual accepted C222 refutation forces the actual enumerator to halt.
A single AX prefix resets both work counters from any encoded working state.
Its raw tag4 lies in the scheduler's range. Arithmetic completeness gives a
closed IΣ1/PA derivation, not an assumed source-calculus or machine calibration. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticProofWordEnumPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticCommandStepPerm222 ArithmeticCommandBlockPerm222 ArithmeticCommandRunPerm222
open ArithmeticProofWordPerm222

section Reset
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Tag4 is AX with c=1; x/y=0. Its old registers may be arbitrary. -/
noncomputable def resetWord (rest : V) : V := axWord 1 0 0 rest

theorem state_decode (w : V) :
    stateValue (first w) (first (second w)) (first (second (second w)))
      (second (second (second w)))=w := by
  simp only [stateValue,cantor_projections]

theorem resetWord_ne_zero (rest : V) : resetWord rest≠0 := by
  simp [resetWord,axWord]

/-- The scheduler enumerates raw candidate word-1, starting at4. -/
theorem resetWord_candidate (rest : V) : 4≤resetWord rest-1 := by
  have h4 : (1 : V)+3=4 := by rw [add_comm 1 3,three_add_one_eq_four]
  simpa [resetWord,axWord,h4] using
    (components_le ((1 : V)+3) (cantor 0 (cantor 0 rest))).1

/-- Reset does not require an initially zero cache, counter, top or stack. -/
theorem resetWord_halts (rest : V)
    (h : ∀ top S, evalValue rest (stateValue top S 0 0)=0) (w : V) :
    evalValue (resetWord rest) w=0 := by
  rw [←state_decode w,resetWord,eval_ax]
  exact h _ _
end Reset

section Correctness
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- No initial working-state premise and no separately supplied compiler
invariant occurs in this actual internal scheduler theorem. -/
theorem enum_halts_of_refutation (code initialWork : V)
    (h : ArithmeticHistory222.checkDef.val.Evalb ![code,1]) :
    ∃ time, ArithmeticEnumRunPerm222.run time
      (ArithmeticEnumStepPerm222.liveValue 0 4 initialWork)=0 :=
  ArithmeticEnumFairPerm222.halts_of_word (resetWord (refutationWord code)) 4 initialWork
    (resetWord_ne_zero _) (resetWord_candidate _)
    (resetWord_halts _ (refutationWord_halts code h))
end Correctness

/-- Only the actual checker and enumerator graphs occur in the closed
sentence; no program/circuit choice or new predicate symbol is a parameter. -/
def refutationHaltingSentence : ArithmeticSentence :=
  “∀ code, !ArithmeticHistory222.checkDef code 1 → ∀ work, ∃ initial,
    !ArithmeticEnumStepPerm222.liveDef initial 0 4 work ∧
    ∃ time, !ArithmeticEnumRunPerm222.runDef 0 time initial”

theorem refutationHaltingSentence_true {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : refutationHaltingSentence.Evalb (M := V) ![] := by
  simp [refutationHaltingSentence]
  intro code hc work
  obtain ⟨time,ht⟩ := enum_halts_of_refutation code work (by simpa using hc)
  exact ⟨time,ht.symm⟩

/-- Existence of a genuine closed arithmetic derivation, via completeness
for all Type0 IΣ1 models. No source equation equivalence is assumed. -/
theorem isigma1_proves_refutation_halting : 𝗜𝚺₁ ⊢ refutationHaltingSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (refutationHaltingSentence_true (V := M))

theorem peano_proves_refutation_halting : Peano ⊢ refutationHaltingSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_refutation_halting

end DiophantineConsistency.ArithmeticProofWordEnumPerm222

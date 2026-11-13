module
public import PA196.Arithmetic.Machine.Exact.SentenceCorrectness
public import PA196.Nonhalting
@[expose] public section

/-! The completed standard-model direction for the exact 196-state sentence.
These results do not assert that PA cannot prove the nonhalting sentence.
That direction requires the separate internal refutation-to-machine transport. -/
namespace PA196.Arithmetic
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

abbrev haltingSentence := Machine.Exact.PA.HaltingFormula.traceSentence
abbrev nonhaltingSentence := Machine.Exact.PA.HaltingFormula.nonhaltingSentence

theorem nonhalting_true : Nat ⊧/![] nonhaltingSentence :=
  Machine.Exact.PA.sentence_iff_literal_nonhalting.mpr PA196.machine_nonhalting

/-- PA cannot prove the positive exact blank-halting sentence. -/
theorem halting_unprovable : Machine.Exact.PA.theory ⊬ haltingSentence := by
  intro hp
  have ht := consequence_iff.mp (Theory.Proof.sound hp) Nat inferInstance
  have hf : ¬ (Nat ⊧/![] haltingSentence) := by
    simpa [nonhaltingSentence,Machine.Exact.PA.HaltingFormula.nonhaltingSentence,
      haltingSentence,models_iff,Semiformula.Realize,Semiformula.Evalb] using nonhalting_true
  exact hf (by simpa [models_iff,Semiformula.Realize,Semiformula.Evalb] using ht)

/-- The exact nonhalting sentence is irrefutable in PA. -/
theorem nonhalting_irrefutable : Machine.Exact.PA.theory ⊬ ∼nonhaltingSentence := by
  intro hp
  have ht := consequence_iff.mp (Theory.Proof.sound hp) Nat inferInstance
  have hf : ¬ (Nat ⊧/![] nonhaltingSentence) := by
    simpa [models_iff,Semiformula.Realize,Semiformula.Evalb] using ht
  exact hf nonhalting_true

#print axioms nonhalting_true
#print axioms halting_unprovable
#print axioms nonhalting_irrefutable
end PA196.Arithmetic

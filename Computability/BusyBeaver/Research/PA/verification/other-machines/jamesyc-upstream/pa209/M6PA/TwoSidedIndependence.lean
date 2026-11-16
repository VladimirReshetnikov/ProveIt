module
public import M6PA.FinalEndpoint
@[expose] public section

/-! Two-sided independence target for the exact M6/rho6 209-state machine.
The standard-model argument follows jamesyc/BusyBeaver commit
51935df72b1fdf9206d3b32e3a92f901bb8b85cb. Foundation supplies Nat's PA-model
and consistency instances in Lean's metatheory. These are not PA proofs of
its own soundness, nor a generic inference from consistency to soundness. -/
namespace M6.Arithmetic.PA.Independence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

/-- PA cannot prove the negation of the exact nonhalting sentence, by
standard-model soundness and the checked physical nonhalting theorem. -/
theorem nonhalting_irrefutable (hcons : M6.PA.Consistent) :
    theory ⊬ ∼ExactHaltingFormula.nonhaltingSentence := by
  intro hp
  have ht := consequence_iff.mp (Theory.Proof.sound hp) Nat inferInstance
  have hn := FinalEndpoint.nonhalting_true hcons
  have hf : ¬ (Nat ⊧/![] ExactHaltingFormula.nonhaltingSentence) := by
    simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using ht
  exact hf hn

/-- PA cannot prove the exact positive halting-trace sentence either. -/
theorem halting_unprovable : theory ⊬ ExactHaltingFormula.traceSentence := by
  intro hp
  have ht := consequence_iff.mp (Theory.Proof.sound hp) Nat inferInstance
  have hn := FinalEndpoint.nonhalting_true (inferInstance : M6.PA.Consistent)
  have hf : ¬ (Nat ⊧/![] ExactHaltingFormula.traceSentence) := by
    simpa [ExactHaltingFormula.nonhaltingSentence, models_iff,
      Semiformula.Realize, Semiformula.Evalb] using hn
  exact hf (by simpa [models_iff, Semiformula.Realize, Semiformula.Evalb] using ht)

/-- Both nonprovability directions, with Foundation's proved standard-model
consistency instance discharging the explicit consistency hypothesis. -/
theorem two_sided_independence :
    (theory ⊬ ExactHaltingFormula.nonhaltingSentence) ∧
    (theory ⊬ ∼ExactHaltingFormula.nonhaltingSentence) :=
  ⟨FinalEndpoint.nonhalting_unprovable inferInstance,
    nonhalting_irrefutable inferInstance⟩

theorem machine_nonhalting :
    ¬ M6.Zip.Halts M6.Literal.machine M6.Startup.blank :=
  M6.PA.literal_nonhalting inferInstance

#print axioms halting_unprovable
#print axioms nonhalting_irrefutable
#print axioms two_sided_independence
#print axioms machine_nonhalting
end M6.Arithmetic.PA.Independence

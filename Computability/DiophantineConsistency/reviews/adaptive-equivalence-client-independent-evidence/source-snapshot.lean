import DiophantineConsistency.ArithmeticAdaptiveHaltReduced2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionRunDraft2011

/-! Conditional model-theoretic equivalence for the maintained 87-gate output. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveEquivalence2011
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPackingCells
open ArithmeticCantor (first)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Given local normalization, the maintained equation has no zero exactly
    when the represented machine has no halting time in the model. -/
theorem no_zero_iff_no_run_halt (hL : LocalNormalization) :
    (∀ v : Fin 13 → V,
      ¬ InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 v) ↔
    (∀ t : V, first (ArithmeticMachineRun215.run t) ≠ 0) := by
  constructor
  · intro h t ht
    obtain ⟨v, hv⟩ := ArithmeticAdaptiveConstructionRunDraft2011.reduced_zero_of_run hL t ht
    exact h v hv
  · intro h v hv
    obtain ⟨_, t, _, ht⟩ := ArithmeticAdaptiveHaltReduced2011.reduced_zero_halts v hv
    exact h t ht

end DiophantineConsistency.ArithmeticAdaptiveEquivalence2011

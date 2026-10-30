import DiophantineConsistency.ArithmeticAdaptiveEquivalence2011
import DiophantineConsistency.ArithmeticLocalNormalization

/-! Discharge the finite normalization hypothesis in the model equivalence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveEquivalenceUnconditional2011
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
open ArithmeticCantor (first)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The maintained equation has no zero exactly when the represented run
    has no halting time in the model. -/
theorem no_zero_iff_no_run_halt :
    (∀ v : Fin 13 → V,
      ¬ InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 v) ↔
    (∀ t : V, first (ArithmeticMachineRun215.run t) ≠ 0) :=
  ArithmeticAdaptiveEquivalence2011.no_zero_iff_no_run_halt
    ArithmeticLocalNormalization.localNormalization

end DiophantineConsistency.ArithmeticAdaptiveEquivalenceUnconditional2011

import DiophantineConsistency.ArithmeticAdaptiveHalt2011
import DiophantineConsistency.AdaptiveFirstRootFactor87Literal

/-! The 87-gate adaptive equation inherits the actual zero-to-halt direction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveHaltReduced2011
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
open ArithmeticCantor (first)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A zero of the maintained 87-gate output yields a bounded machine halt. -/
theorem reduced_zero_halts (v : Fin 13 → V)
    (hz : InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 v) :
    ∃ N t : V, t < N ∧ first (ArithmeticMachineRun215.run t) = 0 :=
  ArithmeticAdaptiveHalt2011.natural_zero_halts v
    ((AdaptiveFirstRootFactor87Literal.current_natural_zero_iff v).mpr hz)

end DiophantineConsistency.ArithmeticAdaptiveHaltReduced2011

import DiophantineConsistency.ArithmeticAdaptiveWindow2011
import DiophantineConsistency.ArithmeticCellWindow

/-! A zero of the actual 13-variable natural expression supplies a halting
    time for the represented decimal215 machine, uniformly in models of IΣ₁. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveHalt2011
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
open ArithmeticCantor (first)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every natural-expression zero gives a represented halting time and bound. -/
theorem natural_zero_halts (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    ∃ N t : V, t < N ∧ first (ArithmeticMachineRun215.run t) = 0 := by
  obtain ⟨N, W, C, F, h⟩ := ArithmeticAdaptiveWindow2011.current_natural_window v hz
  obtain ⟨t, ht, hh⟩ := ArithmeticCellWindow.window_halts h
  exact ⟨N, t, ht, hh⟩

end DiophantineConsistency.ArithmeticAdaptiveHalt2011

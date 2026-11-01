import DiophantineConsistency.AdaptiveDirectOrdinate86FixedEquivalence
import DiophantineConsistency.ArithmeticAdaptiveEquivalenceUnconditional2011

/-! Fixed-port 86 no-zero equivalence with represented machine nonhalting. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Machine
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
open ArithmeticCantor (first)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem no_zero_iff_no_run_halt :
    (∀ v : Fin 13 → V, ¬InternalZero AdaptiveDirectOrdinate86Literal.naturalExpression86 v) ↔
    (∀ t : V, first (ArithmeticMachineRun215.run t) ≠ 0) :=
  AdaptiveDirectOrdinate86FixedEquivalence.current_no_zero_iff.trans
    ArithmeticAdaptiveEquivalenceUnconditional2011.no_zero_iff_no_run_halt
end DiophantineConsistency.AdaptiveDirectOrdinate86Machine

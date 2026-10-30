import DiophantineConsistency.ArithmeticConstructionAssembly
import DiophantineConsistency.ArithmeticAdaptiveConstructionReduced2011

/-! Draft direct link from the strengthened Assembly to the 87-gate zero.
This source is intentionally uncompiled until the current-source Assembly
closure has been rebuilt and independently authenticated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionRunDraft2011
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor (first)
open ArithmeticPackingCells ArithmeticConstructionBound
  ArithmeticAdaptiveConstructionReduced2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Draft: the run and local-normalization premises supply an 87-gate zero. -/
theorem reduced_zero_of_run (hL : LocalNormalization) (T : V)
    (hT : first (ArithmeticMachineRun215.run T)=0) :
    ∃ x : Fin 13 → V,
      AdaptiveEquationSyntax2011.InternalZero AdaptiveFirstRootFactor87Literal.naturalExpression87 x := by
  exact reduced_zero_of_enriched_assembly (zeroBound T)
    (construction_below_seed_phase_hL hL T hT)
end DiophantineConsistency.ArithmeticAdaptiveConstructionRunDraft2011

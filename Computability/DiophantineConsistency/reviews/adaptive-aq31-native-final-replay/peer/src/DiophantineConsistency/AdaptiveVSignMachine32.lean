import DiophantineConsistency.ArithmeticAdaptivePositiveAuxPair2011
import DiophantineConsistency.AdaptiveVSignFrom87

/-! A halting run supplies an oriented positive 32-coordinate witness. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveVSignMachine32
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC ArithmeticCantor
open AdaptiveEquationSyntax2011 AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem from_run (T : V) (hT : first (ArithmeticMachineRun215.run T)=0) :
    ∃ v : Fin 32 → V, (∀ i, 0 < v i) ∧ v 24 < v 23 ∧
      InternalZero (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports) v := by
  obtain ⟨w,hw,hzero,hsign⟩ := ArithmeticAdaptivePositiveAuxPair2011.oriented_pair_witness_of_run T hT
  have h87 : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) w := by
    change (splitEval (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) w).1 =
      (splitEval (AdaptiveFirstRootFactor87Literal.expressionAt87 CurrentWindowCarry2011.ports) w).2
    change (splitEval (expressionAt CurrentWindowCarry2011.ports) w).1 =
      (splitEval (expressionAt CurrentWindowCarry2011.ports) w).2 at hzero
    rw [← AdaptiveFirstRootFactor87Literal.split_expression_eq]
    exact hzero
  obtain ⟨v,hv,hz,hs⟩ := AdaptiveVSignFrom87.from87_to32 w hw h87 hsign
  exact ⟨v,hv,hs,hz⟩
#print axioms from_run
end DiophantineConsistency.AdaptiveVSignMachine32

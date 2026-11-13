import CompactSymbolicModelIff
import CompactSymbolicPortProjections

/-! Discharge the four symbolic model-port casts in the conditional model iff. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicModelUnconditionalIff
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open CompactSymbolicModelIff
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
attribute [local irreducible] rho paramKernel CompactFixedBeta.betaNat lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Every model of IΣ₁ satisfies the fixed-symbolic graph/halt equivalence. -/
theorem model_iff :
    (∃ v : Fin 12 → V, (∀ j, 0<v j) ∧ InternalZero (literal p) v) ↔
      (∃ T : V, ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0) := by
  apply CompactSymbolicModelIff.model_iff
  · intro T
    exact CompactSymbolicPortProjections.beta (paramKernel rho) _
  · exact CompactSymbolicPortProjections.kernel (paramKernel rho)
  · exact CompactSymbolicPortProjections.low (paramKernel rho)
  · exact CompactSymbolicPortProjections.high (paramKernel rho)

#print axioms CompactSymbolicModelUnconditionalIff.model_iff
end CompactSymbolicModelUnconditionalIff

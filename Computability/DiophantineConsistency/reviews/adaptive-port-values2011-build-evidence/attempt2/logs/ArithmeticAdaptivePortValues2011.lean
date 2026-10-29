import DiophantineConsistency.ArithmeticAdaptiveTransportRestoration2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePortValues2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveScaledNorms2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem port1_cast : (currentPorts 1:V)=(CurrentKernel2011.K:V) := by
  apply congrArg (fun n : ℕ => (n:V))
  simp only [currentPorts,Matrix.cons_val_one,Matrix.vecHead,Matrix.vecTail]
end DiophantineConsistency.ArithmeticAdaptivePortValues2011

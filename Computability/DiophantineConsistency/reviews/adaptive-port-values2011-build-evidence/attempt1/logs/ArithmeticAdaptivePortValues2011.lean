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
  change (CurrentKernel2011.K:V)=(CurrentKernel2011.K:V)
  rfl
end DiophantineConsistency.ArithmeticAdaptivePortValues2011

import DiophantineConsistency.ArithmeticAdaptivePortValues2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePortValues2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptivePortValues2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example : (DiophantineConsistency.ArithmeticAdaptiveScaledNorms2011.currentPorts 1:V)=
    (CurrentKernel2011.K:V) := port1_cast
#print axioms port0_nat
#print axioms port1_nat
#print axioms port2_nat
#print axioms port3_nat
#print axioms port1_cast
end DiophantineConsistency.ArithmeticAdaptivePortValues2011Checks

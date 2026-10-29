import DiophantineConsistency.ArithmeticAdaptiveFactorThree2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveFactorThree2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveFactorThree2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (q Y X t : V) (hq : 0<q) (hY : q^3∣Y)
    (hd : q^5∣(3+4*Y*(X+1))*t) : q^4∣t :=
  cancel_factor_three q Y X t hq hY hd
#print axioms cancel_unit_power
#print axioms one_plus_unit
#print axioms cancel_factor_three
end DiophantineConsistency.ArithmeticAdaptiveFactorThree2011Checks

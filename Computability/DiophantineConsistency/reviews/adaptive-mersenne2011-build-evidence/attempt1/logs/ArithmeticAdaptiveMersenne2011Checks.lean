import DiophantineConsistency.ArithmeticAdaptiveMersenne2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMersenne2011Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveMersenne2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (d R q J : V) (hd : 4≤d) (hq : q=(Exp.exp d-1)*J+1)
    (hdiv : q∣3*Exp.exp R) : q∣Exp.exp R := cancel_three d R q J hd hq hdiv
#print axioms three_power_not_one
#print axioms not_three_dvd
#print axioms cancel_three
end DiophantineConsistency.ArithmeticAdaptiveMersenne2011Checks

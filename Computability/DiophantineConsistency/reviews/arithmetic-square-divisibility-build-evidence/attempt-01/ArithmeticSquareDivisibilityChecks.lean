import DiophantineConsistency.ArithmeticSquareDivisibility
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSquareDivisibilityChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSquareDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (m z : V) (hm : 0<m) (h : m*m∣z*z) : m∣z := dvd_of_square_dvd m z hm h
example (m : V) (hm : 0<m) : m∣(0:V) := dvd_of_square_dvd m 0 hm (by simp)
#print axioms dvd_of_square_dvd
end DiophantineConsistency.ArithmeticSquareDivisibilityChecks

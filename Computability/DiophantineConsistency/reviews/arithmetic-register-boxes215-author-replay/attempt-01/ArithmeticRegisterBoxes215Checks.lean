import DiophantineConsistency.ArithmeticRegisterBoxes215
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticRegisterBoxes215Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticRegisterBoxes215
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (z : V) : repeat3 6 0 z=z := repeat3_zero 6 z
example (n z : V) : repeat3 6 (n+1) z=6+8*repeat3 6 n z := repeat3_succ 6 n z
#print axioms scan_right
#print axioms scan_left
#print axioms repeat3_defined
end DiophantineConsistency.ArithmeticRegisterBoxes215Checks

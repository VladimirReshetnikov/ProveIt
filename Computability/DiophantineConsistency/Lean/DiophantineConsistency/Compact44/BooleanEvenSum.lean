import DiophantineConsistency.Compact44.FixedGraphUniformDecoder
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BooleanEvenSum
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem eq_of_even (x y : V) (hx : x≤1) (hy : y≤1) (hp : (x+y)%2=0) : x=y := by
  rcases le_one_iff_eq_zero_or_one.mp hx with rfl | rfl <;>
    rcases le_one_iff_eq_zero_or_one.mp hy with rfl | rfl <;> norm_num at *
#print axioms BooleanEvenSum.eq_of_even
end BooleanEvenSum

import DiophantineConsistency.CompactSymbolicKernelCast
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelGeneric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernelCast
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cast_kernel_generic {ι κ : Type*} [Fintype ι] [Fintype κ]
    (r a b c d u v L S : ℕ) (e₁ c₁ : ι → ℕ) (e₂ c₂ : κ → ℕ) :
    (((r^a+r^b+r^c+r^d +
      (∑ i, c₁ i*(r^(u-e₁ i)+r^(v-e₁ i))) +
      (∑ j, c₂ j*(r^(u-e₂ j)+r^(v-e₂ j))) + r^L*r^S):ℕ):V) =
      ((r:V)^a+(r:V)^b+(r:V)^c+(r:V)^d) +
      (∑ i, (c₁ i:V)*((r:V)^(u-e₁ i)+(r:V)^(v-e₁ i))) +
      (∑ j, (c₂ j:V)*((r:V)^(u-e₂ j)+(r:V)^(v-e₂ j))) + (r:V)^L*(r:V)^S := by
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  rw [cast_reflected_sum (V:=V), cast_reflected_sum (V:=V)]
#print axioms CompactSymbolicKernelGeneric.cast_kernel_generic
end CompactSymbolicKernelGeneric

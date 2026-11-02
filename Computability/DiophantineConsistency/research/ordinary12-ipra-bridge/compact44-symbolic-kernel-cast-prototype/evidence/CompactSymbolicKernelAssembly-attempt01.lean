import DiophantineConsistency.CompactSymbolicKernelCast
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernel CompactSymbolicKernelCast
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem cast_kernel :
    ((kernelNat:ℕ):V) =
      ((rho:V)^30+(rho:V)^62+(rho:V)^1100+(rho:V)^2201)
      + (∑ i : Fin 943,
          (CompactCoefficientMass.selector (Compact943Data.row i):V)*
            ((rho:V)^(4393-i.val)+(rho:V)^(5495-i.val)))
      + (∑ i : Fin 41,
          ((2^(10+i.val):ℕ):V)*((rho:V)^(4393-position i)+(rho:V)^(5495-position i)))
      + (rho:V)^8807*(rho:V)^42 := by
  simp only [kernelNat,bareTerms,selectorTerms,copyTerms,reflected,block,
    Nat.cast_add,Nat.cast_mul,Nat.cast_pow]
  rw [cast_reflected_sum (V:=V), cast_reflected_sum (V:=V)]
#print axioms CompactSymbolicKernelAssembly.cast_kernel
end CompactSymbolicKernelAssembly

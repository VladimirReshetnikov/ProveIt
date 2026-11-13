import DiophantineConsistency.CompactSymbolicKernelGeneric
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicKernelOpaque
open LO LO.FirstOrder LO.FirstOrder.Arithmetic CompactSymbolicKernel CompactSymbolicKernelGeneric
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def paramKernel (r : ℕ) : ℕ :=
  r^30+r^62+r^1100+r^2201 +
  (∑ i : Fin 943, CompactCoefficientMass.selector (Compact943Data.row i) *
     (r^(4393-i.val)+r^(5495-i.val))) +
  (∑ i : Fin 41, (2^(10+i.val):ℕ) * (r^(4393-position i)+r^(5495-position i))) +
  r^8807*r^42

theorem cast_paramKernel (r : ℕ) :
    ((paramKernel r:ℕ):V) =
      ((r:V)^30+(r:V)^62+(r:V)^1100+(r:V)^2201)
      + (∑ i : Fin 943,
          (CompactCoefficientMass.selector (Compact943Data.row i):V)*
            ((r:V)^(4393-i.val)+(r:V)^(5495-i.val)))
      + (∑ i : Fin 41,
          ((2^(10+i.val):ℕ):V)*((r:V)^(4393-position i)+(r:V)^(5495-position i)))
      + (r:V)^8807*(r:V)^42 := by
  exact cast_kernel_generic r 30 62 1100 2201 4393 5495 8807 42
    (fun i : Fin 943 => i.val) (fun i => CompactCoefficientMass.selector (Compact943Data.row i))
    (fun i : Fin 41 => position i) (fun i => 2^(10+i.val))

theorem kernel_eq_param : kernelNat = paramKernel rho := by rfl
#print axioms CompactSymbolicKernelOpaque.cast_paramKernel
#print axioms CompactSymbolicKernelOpaque.kernel_eq_param
end CompactSymbolicKernelOpaque

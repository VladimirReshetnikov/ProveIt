import DiophantineConsistency.Compact44.KCast
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace SymbolicKBandDraft
open DiophantineConsistency CompactSymbolicKernel CompactSymbolicKernelOpaque
open CompactPartialBandRotation KCast
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local irreducible] rho paramKernel

theorem symbolic_kernel_band_cast :
    ((paramKernel rho : ℕ) : V) =
      kernelBand (V := V) position 4393 + kernelBand (V := V) position 5495 +
      TwoBand.bareKernel (V := V) := by
  have hspatial : ((rho : ℕ) : V)^8807 * ((rho : ℕ) : V)^42 =
      Exp.exp ((67 : V) * (8849 : V)) := by
    rw [← pow_add]
    exact cast_rho_pow (V := V) 8849
  rw [cast_paramKernel (V := V) rho, hspatial, bare_formula]
  simp only [cast_rho_pow, kernelBand, selectorCoeff, copyCoeff,
    selectorOffset, copyOffset]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf
#print axioms SymbolicKBandDraft.symbolic_kernel_band_cast
end SymbolicKBandDraft

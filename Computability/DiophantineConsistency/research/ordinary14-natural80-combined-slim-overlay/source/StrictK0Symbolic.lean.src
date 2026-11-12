import DiophantineConsistency.Compact44.CompactKernelSplit
import DiophantineConsistency.Compact44.CompactSymbolicModelIff
import DiophantineConsistency.ModelDifferenceRing

/-! Source-only proposed positivity of the symbolic K0 port. This file is
unelaborated and does not bind symbolic values to external bytes. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.StrictK0SymbolicDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
open ModelDifferenceRing
attribute [local irreducible] paramKernel rho

/-- The isolated top term gives positivity without evaluating the kernel. -/
theorem kernel_nat_pos : 0 < paramKernel rho := by
  rw [CompactKernelSplit.kernel_split_generic]
  have hr : 0 < rho := by simp [rho]
  exact add_pos_of_pos_of_nonneg (pow_pos hr _) (Nat.zero_le _)

/-- Standard natural casts preserve this positivity in the model. -/
theorem kernel_model_pos {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : 0 < (paramKernel rho : V) := by
  exact (Nat.cast_pos (α:=V)).mpr kernel_nat_pos

/-- Port slot 1 is represented by that cast in the difference ring. -/
theorem port_one_representation {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    (CompactSymbolicModelIff.p 1 : DiffRing V) = ι (paramKernel rho : V) := by
  change ((paramKernel rho : ℤ) : DiffRing V) = ι (paramKernel rho : V)
  simp only [Int.cast_natCast, map_natCast]

theorem port_one_pos {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : 0 < (CompactSymbolicModelIff.p 1 : DiffRing V) := by
  rw [port_one_representation]
  simpa only [map_zero] using (ι_lt_ι.mpr (kernel_model_pos (V:=V)))

end DiophantineConsistency.StrictK0SymbolicDraft

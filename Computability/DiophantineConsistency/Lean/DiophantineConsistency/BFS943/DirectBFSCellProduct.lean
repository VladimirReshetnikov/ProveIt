import DiophantineConsistency.BFS943.DirectBFSKernelBound
import DiophantineConsistency.BFS943.DirectBFSCellSizeBound
import DiophantineConsistency.BFS943.DirectBFSPackedCell
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DirectBFSCellProduct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticMaskConstants ArithmeticWindowDigits
open DirectBFSCellSizeBound DirectBFSPackedCell DirectBFSUniformPackedCell
attribute [local irreducible] DirectBFSSymbolicKernel.paramKernel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_kernel_lt :
    ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho:ℕ):V)<Exp.exp (592950:V) := by
  have h : DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho < 2^592950 := by
    have hk := DirectBFSKernelBound.kernel_lt CompactSymbolicKernel.rho (by simp only [CompactSymbolicKernel.rho]; exact le_rfl)
    have he : CompactSymbolicKernel.rho^8850=2^592950 := by
      rw [CompactSymbolicKernel.rho, ←pow_mul]
    rw [he] at hk
    exact hk
  change ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho:ℕ):V)<Exp.exp ((592950:ℕ):V)
  rw [cast_exp 592950]
  exact_mod_cast h

theorem product_lt (x : V) (hx : x<Exp.exp (67*3297:V)) :
    ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho:ℕ):V)*x <
      Exp.exp 590069*Exp.exp 590069 := by
  calc
    _ ≤ Exp.exp 592950*x := mul_le_mul_of_nonneg_right symbolic_kernel_lt.le (Arithmetic.zero_le x)
    _ < Exp.exp 592950*Exp.exp (67*3297:V) := mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp (592950+67*3297:V) := (exp_add _ _).symm
    _ ≤ Exp.exp (590069+590069:V) := exp_monotone_le.mpr (by norm_num)
    _ = Exp.exp 590069*Exp.exp 590069 := exp_add _ _

theorem normalized_cell_product_lt (a d : V) (ha : a≠1) :
    ((DirectBFSSymbolicKernel.paramKernel CompactSymbolicKernel.rho:ℕ):V)*normalizedCell a d <
      Exp.exp 590069*Exp.exp 590069 := by
  apply product_lt
  exact packedCell_lt_support a (d%2) ha (lt_two_iff_le_one.mp (mod_lt d (by norm_num)))
#print axioms DirectBFSCellProduct.symbolic_kernel_lt
#print axioms DirectBFSCellProduct.product_lt
#print axioms DirectBFSCellProduct.normalized_cell_product_lt
end DirectBFSCellProduct

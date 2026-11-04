import DiophantineConsistency.Compact44.CompactCellSizeBound
import DiophantineConsistency.Compact44.TopDigitClean

/-! Concrete symbolic-kernel product bounds for actual compact cells and
their single dummy pulses. No full packing assertion is made. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactCellProductBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticMaskConstants ArithmeticWindowDigits
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactPackedCell CompactCellSizeBound
attribute [local irreducible] paramKernel rho
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem symbolic_kernel_lt : (paramKernel rho : V) < Exp.exp (592884 : V) := by
  change (paramKernel rho : V) < Exp.exp ((592884 : ℕ) : V)
  rw [cast_exp 592884]
  exact_mod_cast TopDigit.kernel_bounds.2

theorem cell_pulse_lt (a : V) (ha : a ≠ 1) :
    packedCell a 0 + Exp.exp (67*1063) < Exp.exp (67*3297+1 : V) := by
  have hc := packedCell_lt_support a 0 ha (by simp)
  have hp : Exp.exp (67*1063 : V) < Exp.exp (67*3297 : V) :=
    exp_monotone.mpr (by norm_num)
  calc
    packedCell a 0 + Exp.exp (67*1063) < Exp.exp (67*3297 : V) + Exp.exp (67*3297) := add_lt_add hc hp
    _ = Exp.exp (67*3297+1 : V) := by rw [exp_succ]; ring

/-- Both an actual Boolean-dummy cell and a single pulse added to a
zero-dummy cell are small enough for the `hi_lt` packing field. -/
theorem product_lt (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    (paramKernel rho : V) * x < Exp.exp 590069 * Exp.exp 590069 := by
  calc
    (paramKernel rho : V) * x ≤ Exp.exp 592884 * x :=
      mul_le_mul_of_nonneg_right symbolic_kernel_lt.le (Arithmetic.zero_le x)
    _ < Exp.exp 592884 * Exp.exp (67*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp (592884+(67*3297+1) : V) := (exp_add _ _).symm
    _ ≤ Exp.exp (590069+590069 : V) := exp_monotone_le.mpr (by norm_num)
    _ = Exp.exp 590069 * Exp.exp 590069 := exp_add _ _

theorem packed_cell_product_lt (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    (paramKernel rho : V) * packedCell a d < Exp.exp 590069 * Exp.exp 590069 := by
  apply product_lt
  exact lt_of_lt_of_le (packedCell_lt_support a d ha hd)
    (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))

theorem packed_pulse_product_lt (a : V) (ha : a ≠ 1) :
    (paramKernel rho : V) * (packedCell a 0 + Exp.exp (67*1063)) <
      Exp.exp 590069 * Exp.exp 590069 :=
  product_lt _ (cell_pulse_lt a ha)

#print axioms CompactCellProductBound.symbolic_kernel_lt
#print axioms CompactCellProductBound.cell_pulse_lt
#print axioms CompactCellProductBound.product_lt
#print axioms CompactCellProductBound.packed_cell_product_lt
#print axioms CompactCellProductBound.packed_pulse_product_lt
end CompactCellProductBound

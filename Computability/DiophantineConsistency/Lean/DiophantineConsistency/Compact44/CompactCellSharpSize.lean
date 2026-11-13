import DiophantineConsistency.Compact44.CompactCellSizeBound

/-! A Boolean highest subdigit yields one fewer full radix digit of slack. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactCellSharpSize
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits
open CompactCellDigit CompactPackedCell CompactCellSizeBound
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The highest possible nonzero digit is Boolean, and all higher ones
vanish. This applies to either Boolean dummy value. -/
theorem packedCell_lt_twice_top (a d : V) (ha : a ≠ 1) (hd : d ≤ 1) :
    packedCell a d < 2 * Exp.exp (67*3296 : V) := by
  let x : V := packedCell a d
  let B : V := Exp.exp (67*3296)
  have hsize : x < Exp.exp (67*3297 : V) := packedCell_lt_support a d ha hd
  have hexp : Exp.exp (67*3297 : V) = B * Exp.exp 67 := by
    unfold B
    rw [← exp_add]
    apply congrArg Exp.exp
    norm_num
  have hquot : x / B < Exp.exp 67 := by
    apply div_lt_of_lt_mul
    rw [mul_comm, ← hexp]
    exact hsize
  have hdigit : dig 67 x 3296 ≤ 1 := by
    rw [packedCell_digit a d 3296 hd (by norm_num)]
    exact cellDigit_le_one a d 3296 hd
  have hq1 : x / B ≤ 1 := by
    unfold dig at hdigit
    change (x / B) % Exp.exp 67 ≤ 1 at hdigit
    rwa [mod_eq_self_of_lt hquot] at hdigit
  have hrem : x % B < B := mod_lt _ (exp_pos _)
  calc
    packedCell a d = B * (x / B) + x % B := (div_add_mod x B).symm
    _ < B * 1 + B := add_lt_add_of_le_of_lt
      (mul_le_mul_of_nonneg_left hq1 (Arithmetic.zero_le B)) hrem
    _ = 2 * Exp.exp (67*3296 : V) := by unfold B; ring

#print axioms CompactCellSharpSize.packedCell_lt_twice_top
end CompactCellSharpSize

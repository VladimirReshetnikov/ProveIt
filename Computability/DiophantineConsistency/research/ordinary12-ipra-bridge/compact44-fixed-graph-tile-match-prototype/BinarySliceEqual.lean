import DiophantineConsistency.FiniteBinaryWord
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace BinarySliceEqual
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticPackingBlocks
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def slice (X a m : V) : V := (X/Exp.exp a)%Exp.exp m

theorem bit_slice (X a m u : V) (hu : u<m) : fbit (slice X a m) u=fbit X (a+u) := by
  have he : slice X a m=dig m (X/Exp.exp a) 0 := by simp [slice,dig]
  rw [he,fbit_dig m (X/Exp.exp a) 0 u hu]
  simpa using fbit_div_exp X a u

theorem equal (X Y a b m : V) (h : ∀ u<m, fbit X (a+u)=fbit Y (b+u)) :
    slice X a m=slice Y b m := by
  let f : V → V := fun u => fbit X (a+u)
  have hblocksX : Blocks 1 f m (slice X a m) := by
    constructor
    · simpa only [one_mul,slice] using mod_lt (X/Exp.exp a) (exp_pos m)
    · intro u hu
      have hd : dig 1 (slice X a m) u≤1 := by
        have hh := dig_lt 1 (slice X a m) u
        rw [exp_one] at hh
        exact lt_two_iff_le_one.mp hh
      have he := dig_eq_fbit 1 (slice X a m) u (by norm_num) hd
      simpa only [one_mul,f,bit_slice X a m u hu] using he
  have hblocksY : Blocks 1 f m (slice Y b m) := by
    constructor
    · simpa only [one_mul,slice] using mod_lt (Y/Exp.exp b) (exp_pos m)
    · intro u hu
      have hd : dig 1 (slice Y b m) u≤1 := by
        have hh := dig_lt 1 (slice Y b m) u
        rw [exp_one] at hh
        exact lt_two_iff_le_one.mp hh
      have he := dig_eq_fbit 1 (slice Y b m) u (by norm_num) hd
      simpa only [one_mul,f,bit_slice Y b m u hu,←h u hu] using he
  exact blocks_unique hblocksX hblocksY
#print axioms BinarySliceEqual.equal
end BinarySliceEqual

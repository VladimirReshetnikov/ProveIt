import CompactKernelSplit
import CompactCellProductBound

/-! Isolate the low half of the exact symbolic kernel product. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactKernelLowProduct
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticMaskConstants ArithmeticWindowDigits
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactKernelSplit CompactCellProductBound
attribute [local irreducible] paramKernel rho lowerKernelAt
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rho_pow_cast (n : ℕ) : ((rho ^ n : ℕ) : V) = Exp.exp ((67*n : ℕ) : V) := by
  have he : rho ^ n = 2 ^ (67*n) := by unfold rho; rw [← pow_mul]
  rw [he, ← cast_exp]

theorem kernel_split_model :
    (paramKernel rho : V) = Exp.exp (67*8849 : V) + ((lowerKernelAt rho : ℕ) : V) := by
  have he := congrArg (fun n : ℕ => (n : V)) (kernel_split_generic rho)
  rw [Nat.cast_add, rho_pow_cast] at he
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using he

theorem lower_bound_model :
    ((lowerKernelAt rho : ℕ) : V) < Exp.exp (67*5496 : V) := by
  have h : ((lowerKernelAt rho : ℕ) : V) < ((rho ^ 5496 : ℕ) : V) := by
    exact_mod_cast lower_lt
  rw [rho_pow_cast] at h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- Under the already-proved cell/pulse size bound, the low component has
at least fourteen unused radix digits before the `2^590069` boundary. -/
theorem low_product_lt (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp (67*8793+1 : V) := by
  calc
    ((lowerKernelAt rho : ℕ) : V) * x ≤ Exp.exp (67*5496 : V) * x :=
      mul_le_mul_of_nonneg_right lower_bound_model.le (Arithmetic.zero_le x)
    _ < Exp.exp (67*5496 : V) * Exp.exp (67*3297+1 : V) :=
      mul_lt_mul_of_pos_left hx (exp_pos _)
    _ = Exp.exp ((67*5496)+(67*3297+1) : V) := (exp_add _ _).symm
    _ = Exp.exp (67*8793+1 : V) := by
      apply congrArg Exp.exp
      norm_num

/-- The upper kernel digit is a multiple of the physical cell base, so the
product's low half is exactly the low-component product, with no remainder. -/
theorem low_product_remainder (x : V) (hx : x < Exp.exp (67*3297+1 : V)) :
    ((paramKernel rho : V) * x) % Exp.exp 590069 =
      ((lowerKernelAt rho : ℕ) : V) * x := by
  have hlo := low_product_lt x hx
  have hbase : ((lowerKernelAt rho : ℕ) : V) * x < Exp.exp 590069 :=
    lt_of_lt_of_le hlo (exp_monotone_le.mpr (by norm_num : (67*8793+1 : V) ≤ 590069))
  have htop : Exp.exp (67*8849 : V) = Exp.exp 590069 * Exp.exp (67*42 : V) := by
    rw [← exp_add]
    congr 1
    norm_num
  rw [kernel_split_model, htop]
  have hm : (Exp.exp 590069 * Exp.exp (67*42) + ((lowerKernelAt rho : ℕ) : V)) * x =
      ((lowerKernelAt rho : ℕ) : V) * x + Exp.exp 590069 * (Exp.exp (67*42) * x) := by ring
  rw [hm, mod_add_mul' _ _ (exp_pos (590069:V)), mod_eq_self_of_lt hbase]

#print axioms CompactKernelLowProduct.rho_pow_cast
#print axioms CompactKernelLowProduct.kernel_split_model
#print axioms CompactKernelLowProduct.lower_bound_model
#print axioms CompactKernelLowProduct.low_product_lt
#print axioms CompactKernelLowProduct.low_product_remainder
end CompactKernelLowProduct

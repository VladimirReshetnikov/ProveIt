import DiophantineConsistency.Source34.Source34Masks
import DiophantineConsistency.Mixed121.Mixed121Increment

/-! # The native-cell decoder of the source34 low mask

`Mixed121Increment` at the source34 tuple. The width-121 decoder
(`Mixed121Increment.forbidden_zero`, `ordinary_le_one`, `dummy_le_three`,
`decode_mixed_increment`) and the mask-class lemmas for an arbitrary
`CompactListMask.digits (2^121) len special S` (`model_mask_class`,
`model_mask_lt`, `model_mask_origin`) are generic and used from
`Mixed121Increment`. Only the three statements about the concrete low mask
change: `low_class`, `low_origin` and `recipe_digits` now refer to
`Source34Ports.lowNat`, built from the source34 support. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Source34Increment
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits ArithmeticMaskConstants
open CompactListMask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The source34 low mask -/

theorem low_class (j : V) (hj : j < 8801) :
    dig 121 ((Source34Ports.lowNat : ℕ) : V) j = Exp.exp 121-1 ∨
      dig 121 ((Source34Ports.lowNat : ℕ) : V) j = Exp.exp 121-2 ∨
      dig 121 ((Source34Ports.lowNat : ℕ) : V) j = Exp.exp 121-4 := by
  have h := Mixed121Increment.model_mask_class 8801 1063 Source34Ports.maskSupport j
    (by simpa using hj)
  simpa only [Source34Ports.lowNat, Source34Ports.radix] using h

theorem low_origin : dig 121 ((Source34Ports.lowNat : ℕ) : V) 0 = Exp.exp 121-2 := by
  have h := Mixed121Increment.model_mask_origin (V:=V) 8801 1063 Source34Ports.maskSupport
    (by norm_num) (by norm_num) Source34Ports.zero_mem_support
  simpa only [Source34Ports.lowNat, Source34Ports.radix] using h

/-- The native cells of `C` from the low-mask no-carry condition. -/
theorem recipe_digits (N C : V) (hN : 0 < N) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (((Source34Ports.lowNat : ℕ) : V) * rep (121*8801) N + 1)) :
    dig 121 C 0 = 1 ∧ ∀ k < 8801*N, dig 121 C k ≤ 3 :=
  Mixed121Increment.decode_mixed_increment 8801 N C ((Source34Ports.lowNat : ℕ) : V)
    (by norm_num) hN Source34Masks.model_low_lt (fun j hj => low_class j hj) low_origin hC hnc
end Source34Increment
#print axioms Source34Increment.low_class
#print axioms Source34Increment.low_origin
#print axioms Source34Increment.recipe_digits

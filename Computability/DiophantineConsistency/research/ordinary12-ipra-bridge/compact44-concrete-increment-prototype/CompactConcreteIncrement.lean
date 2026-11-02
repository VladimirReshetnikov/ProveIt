import DiophantineConsistency.CompactConcreteMask
import DiophantineConsistency.CompactMixedIncrement
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactConcreteIncrement
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open ArithmeticBinaryCarry ArithmeticRepunit ArithmeticWindowDigits
open CompactListMask CompactConcreteMask
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The explicit finite-list recipe, still not identified with a graph port. -/
def mask : V := (Nat.ofDigits (2^67) (digits (2^67) 8807 1063 support) : ℕ)

theorem recipe_digits (N C : V) (hN : 0 < N) (hC : 1 ≤ C)
    (hnc : NoCarry (C-1) (mask * rep (67*8807) N + 1)) :
    dig 67 C 0 = 1 ∧ ∀ k < 8807*N, dig 67 C k ≤ 3 := by
  exact CompactMixedIncrement.decode_mixed_increment 8807 N C mask (by norm_num) hN
    model_lt (fun j hj => model_class j hj) model_origin hC hnc

/-- Explicit non-expanded natural recipe for the model mask. -/
theorem mask_eq_bit_recipe : mask (V:=V) =
    ((2^590069 - 1 - (∑ j ∈ support, 2^(67*j)) - 2*2^(67*1063) : ℕ):V) := by
  unfold mask
  rw [concrete_bit_recipe]
end CompactConcreteIncrement
#print axioms CompactConcreteIncrement.recipe_digits
#print axioms CompactConcreteIncrement.mask_eq_bit_recipe

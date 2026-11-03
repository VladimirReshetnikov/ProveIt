import DiophantineConsistency.CompactSymbolicPorts
import DiophantineConsistency.CompactConcreteMask
import Mathlib.Data.Nat.Digits.Defs

/-! Compact sparse-complement recipe for the MC low mask. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace RetainedMCSparseBytes
open scoped BigOperators
open CompactConcreteMask

/-- The sparse-defect natural uses the actual checked symbolic support. -/
def sparseValue : ℕ :=
  2^590069 - 1 - (∑ j ∈ support, 2^(67*j)) - 2*2^(67*1063)

/-- Canonical little-endian base-256 digits, specified without a byte literal. -/
def sparseBytes : List ℕ := Nat.digits 256 sparseValue

attribute [local irreducible] sparseValue sparseBytes CompactSymbolicPorts.lowNat support

/-- The sparse byte recipe decodes to the symbolic low port. -/
theorem decode_sparseBytes :
    Nat.ofDigits 256 sparseBytes = CompactSymbolicPorts.lowNat := by
  have h : sparseValue = CompactSymbolicPorts.lowNat := by
    unfold sparseValue CompactSymbolicPorts.lowNat
    exact concrete_bit_recipe.symm
  calc
    Nat.ofDigits 256 sparseBytes = sparseValue := by
      unfold sparseBytes
      exact Nat.ofDigits_digits 256 sparseValue
    _ = CompactSymbolicPorts.lowNat := h

theorem sparseBytes_valid : ∀ x ∈ sparseBytes, x < 256 := by
  intro x hx
  unfold sparseBytes at hx
  exact Nat.digits_lt_base (by decide) hx

#print axioms RetainedMCSparseBytes.decode_sparseBytes
#print axioms RetainedMCSparseBytes.sparseBytes_valid
end RetainedMCSparseBytes

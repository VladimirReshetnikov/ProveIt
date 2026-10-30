import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! The exact sparse-mask data, separated from its arithmetic coding proofs. -/
set_option Elab.async false
namespace DiophantineConsistency.LowMaskCoding
open scoped BigOperators

def supportValue (B : ℕ) (S : Finset ℕ) : ℕ := ∑ j ∈ S, B ^ j

def mask (B b len : ℕ) (S : Finset ℕ) : ℕ :=
  B ^ len - 1 - (b-1) * supportValue B S

end DiophantineConsistency.LowMaskCoding

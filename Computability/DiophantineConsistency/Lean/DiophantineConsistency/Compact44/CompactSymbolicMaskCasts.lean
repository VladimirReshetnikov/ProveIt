import DiophantineConsistency.Compact44.CompactSymbolicPorts
import DiophantineConsistency.Compact44.CompactConstructedRank

/-! Model casts of the symbolic finite-list masks used in compact rank. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactSymbolicMaskCasts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open CompactSymbolicPorts CompactConstructedRank
attribute [local irreducible] Nat.ofDigits CompactListMask.digits
  CompactConcreteMask.support CompactHighPopulation.highDigits
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem low_cast : (lowNat:V)=(low:V) := by rfl
theorem high_cast : (highNat:V)=(high:V) := by rfl

#print axioms CompactSymbolicMaskCasts.low_cast
#print axioms CompactSymbolicMaskCasts.high_cast
end CompactSymbolicMaskCasts

import Trace74CoverBindHigh
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74SymbolicCoverModel
open CompactFixedBeta CompactSymbolicPorts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Cast the checked natural symbolic-port cover into the indicated model. -/
theorem cover_model : (betaNat:V)+1 ≤ (lowNat:V)+(highNat:V) := by
  have h := (Nat.cast_le.mpr Trace74CoverBindHigh.cover_nat :
    ((betaNat+1:ℕ):V) ≤ ((lowNat+highNat:ℕ):V))
  simpa only [Nat.cast_add,Nat.cast_one] using h

#print axioms Trace74SymbolicCoverModel.cover_model
end Trace74SymbolicCoverModel

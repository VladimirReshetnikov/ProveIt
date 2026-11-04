import DiophantineConsistency.Compact44.CompactSymbolicMaskData
import DiophantineConsistency.Compact44.CompactPackingMaskAlgebra

/-! Uncompiled exact symbolic mask fields, factored through abstract algebra. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CompactSymbolicMaskFields
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open CompactSymbolicPorts CompactSymbolicMaskData CompactPackingMaskAlgebra
attribute [local irreducible] lowNat highNat CompactFixedBeta.betaNat

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem masks : (lowNat:V)+1 < Exp.exp 590069 ∧
    1 ≤ (highNat:V) ∧ (highNat:V) < Exp.exp 590069 := by
  have h := data (V:=V)
  exact fields_of_beta (CompactFixedBeta.betaNat:V) (lowNat:V) (highNat:V)
    (Exp.exp 590069) h.2.2.2 h.1 h.2.1 h.2.2.1

#print axioms masks
end CompactSymbolicMaskFields

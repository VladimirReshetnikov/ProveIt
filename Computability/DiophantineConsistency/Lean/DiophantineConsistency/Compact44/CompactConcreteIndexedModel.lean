import DiophantineConsistency.Compact44.CompactConcreteIndexedMass
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Compact943Data.rows
attribute [local irreducible] CompactConcreteIndexedMass.selectors CompactConcreteIndexedMass.copies
noncomputable section
namespace CompactConcreteIndexedModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open CompactGenericAlignedMass CompactConcreteIndexedMass

theorem concrete_family_mass_b1 {V : Type*} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] :
    ((∑ x : Aligned (Fin 943) (Fin 41), ((alignedCoeff selectors copies x : ℕ) : V) * 3) +
      (Exp.exp 67 - 1)) + 1 ≤ ((1 : V) + 1) * (Exp.exp 67 - 1) := by
  exact CompactIndexedMass.family_mass_b1 selectors copies selectors_mass copies_mass

#print axioms CompactConcreteIndexedModel.concrete_family_mass_b1
end CompactConcreteIndexedModel

import DiophantineConsistency.Compact44.CompactFinIndexedMass
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Compact943Data.rows
noncomputable section
namespace CompactConcreteIndexedMass
open scoped BigOperators
open CompactGenericAlignedMass

def selectors (i : Fin 943) : ℕ := CompactCoefficientMass.selector (Compact943Data.row i)
def copies (j : Fin 41) : ℕ := 2^(10+j.val)

theorem selectors_mass : (∑ i, selectors i) = CompactCoefficientMass.selectorMass := by
  exact CompactSelectorMassBridge.selector_fin_mass

theorem copies_mass : (∑ j, copies j) = CompactCoefficientMass.copyMass := by
  exact CompactSelectorMassBridge.copy_fin_mass

attribute [local irreducible] selectors copies

theorem concrete_mass :
    (∑ x : Aligned (Fin 943) (Fin 41), alignedCoeff selectors copies x)+1 =
      CompactCoefficientMass.stencilMass := by
  exact CompactFinIndexedMass.fin_mass_abstract selectors copies selectors_mass copies_mass

#print axioms CompactConcreteIndexedMass.concrete_mass
end CompactConcreteIndexedMass

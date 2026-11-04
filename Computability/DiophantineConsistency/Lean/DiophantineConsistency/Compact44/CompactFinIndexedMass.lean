import DiophantineConsistency.Compact44.CompactIndexedMass
import DiophantineConsistency.Compact44.CompactSelectorMassBridge
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Compact943Data.rows
noncomputable section
namespace CompactFinIndexedMass
open scoped BigOperators
open CompactGenericAlignedMass

theorem fin_mass_abstract (s : Fin 943 → ℕ) (c : Fin 41 → ℕ)
    (hs : (∑ i, s i) = CompactCoefficientMass.selectorMass)
    (hc : (∑ j, c j) = CompactCoefficientMass.copyMass) :
    (∑ x : Aligned (Fin 943) (Fin 41), alignedCoeff s c x)+1 =
      CompactCoefficientMass.stencilMass := by
  exact CompactIndexedMass.sum_from_masses s c hs hc

#print axioms CompactFinIndexedMass.fin_mass_abstract
end CompactFinIndexedMass

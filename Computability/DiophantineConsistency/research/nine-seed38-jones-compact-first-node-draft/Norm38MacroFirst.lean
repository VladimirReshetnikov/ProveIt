import DiophantineConsistency.Norm38MacroRecipe

/-! Candidate first-node evaluation; no full recipe equality is asserted. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroFirst
open Norm38MacroLanguage ExecutableJones

theorem first_node {R : Type*} [CommRing R] (a : Fin 9 → R) :
    Norm38MacroRecipe.recipe.values a ⟨0, by decide⟩ =
      ((indexY Norm38MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩ := by
  rfl

#print axioms first_node
end DiophantineConsistency.Norm38MacroFirst

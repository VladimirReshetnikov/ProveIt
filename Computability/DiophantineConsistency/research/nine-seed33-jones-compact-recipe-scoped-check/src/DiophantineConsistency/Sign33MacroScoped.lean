import DiophantineConsistency.Sign33MacroRecipe

/-! Candidate boolean scope proof only; no semantic equality is asserted. -/
set_option autoImplicit false
namespace DiophantineConsistency.Sign33MacroScoped

theorem recipe_well_scoped : Sign33MacroRecipe.WellScopedTarget := by
  change Sign33MacroRecipe.recipe.scoped = true
  decide

#print axioms recipe_well_scoped
end DiophantineConsistency.Sign33MacroScoped

import DiophantineConsistency.Norm38MacroRecipe

/-! Candidate boolean scope proof only; no semantic equality is asserted. -/
set_option autoImplicit false
namespace DiophantineConsistency.Norm38MacroScoped

theorem recipe_well_scoped : Norm38MacroRecipe.WellScopedTarget := by
  decide

#print axioms recipe_well_scoped
end DiophantineConsistency.Norm38MacroScoped

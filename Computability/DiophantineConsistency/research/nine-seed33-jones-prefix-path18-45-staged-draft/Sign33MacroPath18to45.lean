import DiophantineConsistency.Sign33MacroPath18to41

/-! Candidate shared path from d18 through the concrete full recipe. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroPath18to45
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding Sign33MacroPath18to41

theorem path18_45 : PrefixPath d18 d45 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d18 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d41 _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step path18_41 _) _) _) _)

theorem lookup18_45 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 18) :
    d45.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d18.values a i := by
  exact lookup path18_45 a i

theorem lookup_recipe18 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 18) :
    Sign33MacroRecipe.recipe.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d18.values a i := by
  rw [recipe_eq_named]
  exact lookup18_45 a i

#print axioms path18_45
#print axioms lookup18_45
#print axioms lookup_recipe18
end DiophantineConsistency.Sign33MacroPath18to45

import DiophantineConsistency.Sign33MacroPrefixFirst

/-! Source-only candidate chain: no semantic theorem is claimed yet. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33FirstPreservation
open Sign33MacroLanguage Sign33MacroPrefixes ExecutableJones

theorem d45_first_eq_d1 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d45.values a ⟨0, by decide⟩ = d1.values a ⟨0, by decide⟩ := by
  calc
    d45.values a ⟨0, by decide⟩ = d44.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d44 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d44 _ ⟨0, by decide⟩
    _ = d43.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d43 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d43 _ ⟨0, by decide⟩
    _ = d42.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d42 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d42 _ ⟨0, by decide⟩
    _ = d41.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d41 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d41 _ ⟨0, by decide⟩
    _ = d40.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d40 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d40 _ ⟨0, by decide⟩
    _ = d39.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d39 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d39 _ ⟨0, by decide⟩
    _ = d38.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d38 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d38 _ ⟨0, by decide⟩
    _ = d37.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d37 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d37 _ ⟨0, by decide⟩
    _ = d36.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d36 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d36 _ ⟨0, by decide⟩
    _ = d35.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d35 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d35 _ ⟨0, by decide⟩
    _ = d34.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d34 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d34 _ ⟨0, by decide⟩
    _ = d33.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d33 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d33 _ ⟨0, by decide⟩
    _ = d32.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d32 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d32 _ ⟨0, by decide⟩
    _ = d31.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d31 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d31 _ ⟨0, by decide⟩
    _ = d30.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ ⟨0, by decide⟩
    _ = d29.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ ⟨0, by decide⟩
    _ = d28.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d28 _ ⟨0, by decide⟩
    _ = d27.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d27 _ ⟨0, by decide⟩
    _ = d26.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d26 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d26 _ ⟨0, by decide⟩
    _ = d25.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d25 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d25 _ ⟨0, by decide⟩
    _ = d24.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d24 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d24 _ ⟨0, by decide⟩
    _ = d23.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d23 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d23 _ ⟨0, by decide⟩
    _ = d22.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d22 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d22 _ ⟨0, by decide⟩
    _ = d21.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d21 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d21 _ ⟨0, by decide⟩
    _ = d20.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d20 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d20 _ ⟨0, by decide⟩
    _ = d19.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d19 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d19 _ ⟨0, by decide⟩
    _ = d18.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d18 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d18 _ ⟨0, by decide⟩
    _ = d17.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d17 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d17 _ ⟨0, by decide⟩
    _ = d16.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d16 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d16 _ ⟨0, by decide⟩
    _ = d15.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d15 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d15 _ ⟨0, by decide⟩
    _ = d14.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d14 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d14 _ ⟨0, by decide⟩
    _ = d13.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d13 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d13 _ ⟨0, by decide⟩
    _ = d12.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d12 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d12 _ ⟨0, by decide⟩
    _ = d11.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d11 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d11 _ ⟨0, by decide⟩
    _ = d10.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d10 _ ⟨0, by decide⟩
    _ = d9.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ⟨0, by decide⟩
    _ = d8.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d8 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d8 _ ⟨0, by decide⟩
    _ = d7.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d7 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d7 _ ⟨0, by decide⟩
    _ = d6.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d6 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d6 _ ⟨0, by decide⟩
    _ = d5.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d5 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d5 _ ⟨0, by decide⟩
    _ = d4.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d4 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d4 _ ⟨0, by decide⟩
    _ = d3.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d3 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d3 _ ⟨0, by decide⟩
    _ = d2.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d2 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d2 _ ⟨0, by decide⟩
    _ = d1.values a ⟨0, by decide⟩ := by
      change (Dag.snoc d1 _).values a (Fin.castSucc ⟨0, by decide⟩) = _
      exact Sign33MacroCuts.snoc_previous a d1 _ ⟨0, by decide⟩

theorem recipe_first_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    Sign33MacroRecipe.recipe.values a ⟨0, by decide⟩ =
      ((indexY Sign33MacroLanguage.seed 0 : Nat) : R) + ((1 : Int) : R) + a ⟨0, by decide⟩ := by
  rw [Sign33MacroPrefixes.recipe_eq_named, d45_first_eq_d1]
  exact Sign33MacroPrefixFirst.first_prefix_value a

#print axioms d45_first_eq_d1
#print axioms recipe_first_value
end DiophantineConsistency.Sign33FirstPreservation

import DiophantineConsistency.Norm38MacroTerminalT

/-! Candidate terminal output composed with T; earlier node values remain cuts. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroTerminalCut
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroDependent08

theorem d45_output_cut {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d45.values a (Fin.last 44) = terminalOutput
      (terminalT (d41.values a ⟨39, by decide⟩) (d41.values a ⟨40, by decide⟩)
        (d43.values a (Fin.last 42)) (d41.values a ⟨37, by decide⟩)
        (d41.values a ⟨38, by decide⟩) (a ⟨8, by decide⟩))
      (d43.values a (Fin.last 42)) (d41.values a ⟨35, by decide⟩)
      (d41.values a ⟨36, by decide⟩) (d41.values a ⟨37, by decide⟩) := by
  rw [prefix_output]
  have h35 : d44.values a ⟨35, by decide⟩ = d41.values a ⟨35, by decide⟩ := by
    have hi : ((⟨35, by decide⟩ : Fin 41).castSucc.castSucc.castSucc) = (⟨35, by decide⟩ : Fin 44) := by decide
    simpa only [hi] using lookup41_44 a ⟨35, by decide⟩
  have h36 : d44.values a ⟨36, by decide⟩ = d41.values a ⟨36, by decide⟩ := by
    have hi : ((⟨36, by decide⟩ : Fin 41).castSucc.castSucc.castSucc) = (⟨36, by decide⟩ : Fin 44) := by decide
    simpa only [hi] using lookup41_44 a ⟨36, by decide⟩
  have h37 : d44.values a ⟨37, by decide⟩ = d41.values a ⟨37, by decide⟩ := by
    have hi : ((⟨37, by decide⟩ : Fin 41).castSucc.castSucc.castSucc) = (⟨37, by decide⟩ : Fin 44) := by decide
    simpa only [hi] using lookup41_44 a ⟨37, by decide⟩
  have hik : (⟨42, by decide⟩ : Fin 44) = ((Fin.last 42).castSucc) := by decide
  have hit : (⟨43, by decide⟩ : Fin 44) = Fin.last 43 := by decide
  have hk : d44.values a ((Fin.last 42).castSucc) = d43.values a (Fin.last 42) := by
    change (Dag.snoc d43 _).values a (Fin.castSucc (Fin.last 42)) = _
    exact Norm38MacroCuts.snoc_previous a d43 _ (Fin.last 42)
  rw [hik, hit, hk, h35, h36, h37, d44_T_cut]
  rfl

theorem recipe_output_cut {R : Type*} [CommRing R] (a : Fin 9 → R) :
    Norm38MacroRecipe.recipe.values a (Fin.last 44) = terminalOutput
      (terminalT (d41.values a ⟨39, by decide⟩) (d41.values a ⟨40, by decide⟩)
        (d43.values a (Fin.last 42)) (d41.values a ⟨37, by decide⟩)
        (d41.values a ⟨38, by decide⟩) (a ⟨8, by decide⟩))
      (d43.values a (Fin.last 42)) (d41.values a ⟨35, by decide⟩)
      (d41.values a ⟨36, by decide⟩) (d41.values a ⟨37, by decide⟩) := by
  rw [recipe_eq_named]
  exact d45_output_cut a

#print axioms d45_output_cut
#print axioms recipe_output_cut
end DiophantineConsistency.Norm38MacroTerminalCut

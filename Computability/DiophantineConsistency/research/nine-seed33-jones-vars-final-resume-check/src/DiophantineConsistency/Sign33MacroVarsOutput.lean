import DiophantineConsistency.Sign33MacroVarsKc

/-! Candidate recipe-output composition through the checked RingVars cuts. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroVarsOutput
open Sign33MacroLanguage Sign33MacroTerminalCut Sign33MacroVarsBd Sign33MacroVarsCd
  Sign33MacroVarsRad Sign33MacroVarsWt Sign33MacroVarsKc

theorem recipe_eq_refined {R : Type*} [CommRing R] (a : Fin 9 → R) :
    Sign33MacroRecipe.recipe.values a (Fin.last 44) =
      RefinedPair.value ((vars a).rad 0) ((vars a).rad 1) ((vars a).wt 0) ((vars a).wt 1)
        (a ⟨8, by decide⟩) (vars a).dvsr (vars a).dvnd (vars a).marg := by
  rw [recipe_output_cut, d41_Bd_eq_dvsr, d41_Cd_eq_dvnd, d43_Kc_eq,
    d41_V0_eq_wt0, d41_V1_eq_wt1, d41_A0_eq_rad0, d41_A1_eq_rad1]
  simp only [terminalOutput, terminalT, RefinedPair.value, Int.cast_ofNat, Int.cast_one]

#print axioms recipe_eq_refined
end DiophantineConsistency.Sign33MacroVarsOutput

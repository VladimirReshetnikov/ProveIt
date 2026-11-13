import DiophantineConsistency.Sign33MacroVarsRad1

/-! Candidate V0 cut using the checked A0 radicand binding. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroVarsWt
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroCheckpointBdCd
  Sign33MacroCheckpointA0 Sign33MacroDependent07 Sign33MacroVarsBd Sign33MacroVarsRad NinePolynomial

theorem d41_V0_eq_wt0 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨37, by decide⟩ = (vars a).wt 0 := by
  have hiV : (((Fin.last 37).castSucc).castSucc.castSucc) = (⟨37, by decide⟩ : Fin 41) := by decide
  have hV : d41.values a ⟨37, by decide⟩ = d38.values a (Fin.last 37) := by
    rw [← hiV, lookup39_41]
    change (Dag.snoc d38 _).values a (Fin.castSucc (Fin.last 37)) = _
    exact Sign33MacroCuts.snoc_previous a d38 _ (Fin.last 37)
  have hiA : (⟨35, by decide⟩ : Fin 37) = ((Fin.last 35).castSucc) := by decide
  have hi35 : ((Fin.last 35).castSucc.castSucc.castSucc.castSucc.castSucc) = (⟨35, by decide⟩ : Fin 41) := by decide
  rw [hV, prefix_V0, hiA, d37_A0_carry, ← lookup36_41 a (Fin.last 35), hi35, d41_A0_eq_rad0]
  simp only [RingVars.wt, Int.cast_ofNat]

#print axioms d41_V0_eq_wt0
end DiophantineConsistency.Sign33MacroVarsWt

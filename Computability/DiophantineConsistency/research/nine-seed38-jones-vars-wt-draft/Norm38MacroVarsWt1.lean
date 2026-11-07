import DiophantineConsistency.Norm38MacroVarsWt0

/-! Candidate V1 cut using the checked A1 radicand binding. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroVarsWt
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroCheckpointBdCd
  Norm38MacroCheckpointA1 Norm38MacroDependent07 Norm38MacroVarsBd Norm38MacroVarsRad NinePolynomial

theorem d41_V1_eq_wt1 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨38, by decide⟩ = (vars a).wt 1 := by
  have hiV : ((Fin.last 38).castSucc.castSucc) = (⟨38, by decide⟩ : Fin 41) := by decide
  have hV : d41.values a ⟨38, by decide⟩ = d39.values a (Fin.last 38) := by
    rw [← hiV, lookup39_41]
  have hiA : (⟨36, by decide⟩ : Fin 38) = ((Fin.last 36).castSucc) := by decide
  have hi36 : ((Fin.last 36).castSucc.castSucc.castSucc.castSucc) = (⟨36, by decide⟩ : Fin 41) := by decide
  rw [hV, prefix_V1, hiA, d38_A1_carry, ← lookup37_41 a (Fin.last 36), hi36, d41_A1_eq_rad1]
  simp only [RingVars.wt, Int.cast_ofNat]

#print axioms d41_V1_eq_wt1
end DiophantineConsistency.Norm38MacroVarsWt

import DiophantineConsistency.Norm38MacroVarsCd

/-! Candidate A0 cut for the symbolic ring variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroVarsRad
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointA0 Norm38MacroVarsBd NinePolynomial

theorem d41_A0_eq_rad0 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨35, by decide⟩ = (vars a).rad 0 := by
  change d41.values a ⟨35, by decide⟩ = ((vars a).P ^ 2 - 1) * (vars a).K ^ 2 + 1
  have hi : (⟨35, by decide⟩ : Fin 41) = ((Fin.last 35).castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hi, d41_A0_value]
  simp only [vars, RingVars.P, RingVars.K, RingVars.M, RingVars.Y, RingVars.U,
    Int.cast_ofNat, Int.cast_one]

#print axioms d41_A0_eq_rad0
end DiophantineConsistency.Norm38MacroVarsRad

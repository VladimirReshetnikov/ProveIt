import DiophantineConsistency.Sign33MacroVarsCd

/-! Candidate A0 cut for the symbolic ring variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroVarsRad
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointA0 Sign33MacroVarsBd NinePolynomial

theorem d41_A0_eq_rad0 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨35, by decide⟩ = (vars a).rad 0 := by
  change d41.values a ⟨35, by decide⟩ = ((vars a).P ^ 2 - 1) * (vars a).K ^ 2 + 1
  have hi : (⟨35, by decide⟩ : Fin 41) = ((Fin.last 35).castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hi, d41_A0_value]
  simp only [vars, RingVars.P, RingVars.K, RingVars.M, RingVars.Y, RingVars.U,
    Int.cast_ofNat, Int.cast_one]

#print axioms d41_A0_eq_rad0
end DiophantineConsistency.Sign33MacroVarsRad

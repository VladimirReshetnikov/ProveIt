import DiophantineConsistency.Sign33MacroVarsBd

/-! Candidate Cd cut for the symbolic ring variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroVarsCd
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointBdCd Sign33MacroVarsBd NinePolynomial

theorem d41_Cd_eq_dvnd {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨40, by decide⟩ = (vars a).dvnd := by
  have hi : (⟨40, by decide⟩ : Fin 41) = Fin.last 40 := by decide
  rw [hi, d41_Cd_value]
  simp only [vars, RingVars.dvnd, RingVars.Q, RingVars.H, RingVars.J, RingVars.F,
    RingVars.E, RingVars.D, RingVars.C, RingVars.B', RingVars.W, RingVars.A,
    RingVars.M, RingVars.Y, RingVars.U, Int.cast_ofNat, Int.cast_one]

#print axioms d41_Cd_eq_dvnd
end DiophantineConsistency.Sign33MacroVarsCd

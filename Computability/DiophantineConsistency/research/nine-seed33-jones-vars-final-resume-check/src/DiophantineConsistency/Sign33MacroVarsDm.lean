import DiophantineConsistency.Sign33MacroVarsWt1

/-! Candidate Dm cut for the symbolic ring variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroVarsKc
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointDm Sign33MacroVarsBd NinePolynomial

theorem d42_Dm_eq_marg {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d42.values a (Fin.last 41) = (vars a).marg := by
  rw [d42_Dm_value]
  simp only [vars, RingVars.marg, RingVars.K, RingVars.P, RingVars.M, RingVars.Y,
    RingVars.U, RingVars.C, RingVars.B', RingVars.W, Int.cast_ofNat, Int.cast_one]

#print axioms d42_Dm_eq_marg
end DiophantineConsistency.Sign33MacroVarsKc

import DiophantineConsistency.Norm38MacroVarsWt1

/-! Candidate Dm cut for the symbolic ring variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroVarsKc
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointDm Norm38MacroVarsBd NinePolynomial

theorem d42_Dm_eq_marg {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d42.values a (Fin.last 41) = (vars a).marg := by
  rw [d42_Dm_value]
  simp only [vars, RingVars.marg, RingVars.K, RingVars.P, RingVars.M, RingVars.Y,
    RingVars.U, RingVars.C, RingVars.B', RingVars.W, Int.cast_ofNat, Int.cast_one]

#print axioms d42_Dm_eq_marg
end DiophantineConsistency.Norm38MacroVarsKc

import DiophantineConsistency.Norm38MacroVarsRad0

/-! Candidate A1 cut for the symbolic ring variables. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroVarsRad
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointA1 Norm38MacroVarsBd NinePolynomial

theorem d41_A1_eq_rad1 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨36, by decide⟩ = (vars a).rad 1 := by
  change d41.values a ⟨36, by decide⟩ = (vars a).D * (vars a).F * (vars a).I
  have hi : (⟨36, by decide⟩ : Fin 41) = ((Fin.last 36).castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hi, d41_A1_value]
  simp only [vars, RingVars.D, RingVars.F, RingVars.I, RingVars.Gp, RingVars.H,
    RingVars.E, RingVars.J, RingVars.C, RingVars.B', RingVars.W, RingVars.A,
    RingVars.M, RingVars.Y, RingVars.U, Int.cast_ofNat, Int.cast_one]

#print axioms d41_A1_eq_rad1
end DiophantineConsistency.Norm38MacroVarsRad

import DiophantineConsistency.Norm38MacroTerminalOutput

/-! Candidate symbolic ring variables and their Bd cut. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroVarsBd
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointBdCd NinePolynomial

def vars {R : Type*} [CommRing R] (a : Fin 9 → R) : RingVars R :=
  ⟨d11.values a (Fin.last 10),
   ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat),
   base a, a ⟨1, by decide⟩ + ((1 : Int) : R),
   ((32 : Int) : R) * base a * (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat),
   a ⟨2, by decide⟩ + ((1 : Int) : R),
   a ⟨3, by decide⟩ + ((1 : Int) : R),
   a ⟨4, by decide⟩ + ((1 : Int) : R),
   a ⟨5, by decide⟩, a ⟨6, by decide⟩ + ((1 : Int) : R),
   a ⟨7, by decide⟩ + ((1 : Int) : R)⟩

theorem d41_Bd_eq_dvsr {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ⟨39, by decide⟩ = (vars a).dvsr := by
  have hi : ((Fin.last 39).castSucc) = (⟨39, by decide⟩ : Fin 41) := by decide
  have hb : d41.values a ⟨39, by decide⟩ = d40.values a (Fin.last 39) := by
    simpa only [hi] using lookup40_41 a (Fin.last 39)
  rw [hb, d40_Bd_value]
  rfl

#print axioms d41_Bd_eq_dvsr
end DiophantineConsistency.Norm38MacroVarsBd

import DiophantineConsistency.Norm38MacroCBW
import DiophantineConsistency.Norm38MacroDependentC

/-! Candidate d27 C value with opaque rank. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointC
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroDependent03

theorem d27_C_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a (Fin.last 26) = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩ := by
  rw [prefix_C]
  have hiB : (⟨24, by decide⟩ : Fin 26) = ((Fin.last 24).castSucc) := by decide
  have hiW : (⟨25, by decide⟩ : Fin 26) = Fin.last 25 := by decide
  have hiphi : (⟨14, by decide⟩ : Fin 26) = ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hiB, hiW, hiphi, d26_Bprime_value, d26_W_value, d26_phi_carry, d18_phi_value]

#print axioms d27_C_value
end DiophantineConsistency.Norm38MacroCheckpointC

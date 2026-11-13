import DiophantineConsistency.Sign33MacroGprimePath
import DiophantineConsistency.Sign33MacroDependentH
import DiophantineConsistency.Sign33MacroLive18Group04
import DiophantineConsistency.Sign33MacroPrefixInputsB

/-! Candidate d34 H value from symbolic Bprime, j and C. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointH
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointC Sign33MacroDependent06 Sign33MacroLive18

theorem d33_j_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d33.values a ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨7, by decide⟩ + ((1 : Int) : R) := by
  rw [d33_j_carry, d25_j_carry, d18_j_carry, Sign33MacroPrefixGroup04.prefix_j]

theorem d33_Bprime_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d33.values a ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R) := by
  rw [d33_Bprime_carry]
  exact (Sign33MacroCuts.snoc_previous a d25 _ (Fin.last 24)).symm.trans (d26_Bprime_value a)

theorem d34_H_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d34.values a (Fin.last 33) = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) := by
  rw [prefix_H]
  have hiB : (⟨24, by decide⟩ : Fin 33) = ((Fin.last 24).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hij : (⟨16, by decide⟩ : Fin 33) = ((Fin.last 16).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiC : (⟨26, by decide⟩ : Fin 33) = ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hiB, hij, hiC, d33_Bprime_value, d33_j_value, d33_C_carry, d27_C_value]

#print axioms d33_j_value
#print axioms d33_Bprime_value
#print axioms d34_H_value
end DiophantineConsistency.Sign33MacroCheckpointH

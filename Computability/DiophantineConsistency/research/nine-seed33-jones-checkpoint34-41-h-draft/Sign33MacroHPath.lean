import DiophantineConsistency.Sign33MacroHValue
import DiophantineConsistency.Sign33MacroCheckpoint34to41

/-! Candidate symbolic d41 H value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointH
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 Sign33MacroCheckpoint34to41

theorem d41_H_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 33).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) := by
  calc
    d41.values a ((Fin.last 33).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a (Fin.last 33) := lookup34_41 a (Fin.last 33)
    _ = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) := d34_H_value a

#print axioms d41_H_value
end DiophantineConsistency.Sign33MacroCheckpointH

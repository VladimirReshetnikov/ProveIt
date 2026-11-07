import DiophantineConsistency.Norm38MacroCValue
import DiophantineConsistency.Norm38MacroDependentQ

/-! Candidate d29 Q value using symbolic rank and W/C. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointQ
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointC Norm38MacroDependent04

theorem d29_Q_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d29.values a (Fin.last 28) = ((3 : Int) : R) * (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) - ((2 : Int) : R) * ((base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) := by
  rw [prefix_Q]
  have hiW : (⟨25, by decide⟩ : Fin 28) = ((Fin.last 25).castSucc.castSucc) := by decide
  have hiC : (⟨26, by decide⟩ : Fin 28) = ((Fin.last 26).castSucc) := by decide
  rw [hiW, hiC, d28_W_carry, d28_C_carry, d26_W_value, d27_C_value]

#print axioms d29_Q_value
end DiophantineConsistency.Norm38MacroCheckpointQ

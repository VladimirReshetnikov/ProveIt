import DiophantineConsistency.Sign33MacroPValue
import DiophantineConsistency.Sign33MacroDependentK
import DiophantineConsistency.Sign33MacroLive18Group02
import DiophantineConsistency.Sign33MacroPrefixInputsA

/-! Candidate symbolic K from checked P, rank and input h. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointPK
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroDependent02 Sign33MacroLive18

theorem d23_K_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d23.values a (Fin.last 22) = d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R)) := by
  rw [prefix_K]
  have hiR : (⟨10, by decide⟩ : Fin 22) = ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hih : (⟨11, by decide⟩ : Fin 22) = ((Fin.last 11).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiP : (⟨21, by decide⟩ : Fin 22) = Fin.last 21 := by decide
  rw [hiR, hih, hiP, d22_R_carry, d18_R_carry, d22_h_carry, d18_h_carry, Sign33MacroPrefixGroup04.prefix_h, d22_P_value]

#print axioms d23_K_value
end DiophantineConsistency.Sign33MacroCheckpointPK

import DiophantineConsistency.Norm38MacroHPath
import DiophantineConsistency.Norm38MacroDependentI

/-! Candidate d35 I value from symbolic Gprime and H. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointI
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointGprime Norm38MacroCheckpointH Norm38MacroDependent07

theorem d35_I_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d35.values a (Fin.last 34) = ((((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) + ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R)) * (((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) + ((1 : Int) : R) - ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩)) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [prefix_I]
  have hiG : (⟨32, by decide⟩ : Fin 34) = ((Fin.last 32).castSucc) := by decide
  have hiH : (⟨33, by decide⟩ : Fin 34) = Fin.last 33 := by decide
  rw [hiG, hiH, d34_Gprime_carry, d33_Gprime_value, d34_H_value]

#print axioms d35_I_value
end DiophantineConsistency.Norm38MacroCheckpointI

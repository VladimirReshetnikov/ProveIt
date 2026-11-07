import DiophantineConsistency.Norm38MacroDPath
import DiophantineConsistency.Norm38MacroDependentE
import DiophantineConsistency.Norm38MacroLive18Group04
import DiophantineConsistency.Norm38MacroPrefixInputsB
import DiophantineConsistency.Norm38MacroJValue

/-! Candidate d31 E value from symbolic input i and J/D/C. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointE
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointC Norm38MacroCheckpointD Norm38MacroCheckpointJ
  Norm38MacroDependent05 Norm38MacroLive18

theorem d30_i_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d30.values a ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨6, by decide⟩ + ((1 : Int) : R) := by
  rw [d30_i_carry, d24_i_carry, d18_i_carry, prefix_i]

theorem d31_E_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d31.values a (Fin.last 30) = (a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat) := by
  rw [prefix_E]
  have hii : (⟨15, by decide⟩ : Fin 30) = ((Fin.last 15).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiJ : (⟨27, by decide⟩ : Fin 30) = ((Fin.last 27).castSucc.castSucc) := by decide
  have hiD : (⟨29, by decide⟩ : Fin 30) = Fin.last 29 := by decide
  have hiC : (⟨26, by decide⟩ : Fin 30) = ((Fin.last 26).castSucc.castSucc.castSucc) := by decide
  rw [hii, hiJ, hiD, hiC, d30_i_value, d30_J_carry, d30_C_carry, d28_J_value, d30_D_value, d27_C_value]

#print axioms d30_i_value
#print axioms d31_E_value
end DiophantineConsistency.Norm38MacroCheckpointE

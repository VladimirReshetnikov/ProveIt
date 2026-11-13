import DiophantineConsistency.Norm38MacroDmInputs
import DiophantineConsistency.Norm38MacroDependentDmKc

/-! Candidate symbolic Dm at d42. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointDm
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointBdCd Norm38MacroCheckpoint41to45 Norm38MacroDependent08

theorem d42_Dm_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d42.values a (Fin.last 41) = (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) ^ (2 : Nat) * (((32 : Int) : R) * base a * (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat)) - ((4 : Int) : R) * (((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) - (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * (((32 : Int) : R) * base a * (base a ^ (5 : Nat)) ^ (5 ^ 38 : Nat)) - ((8 : Int) : R) * (a ⟨1, by decide⟩ + ((1 : Int) : R)) * (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) ^ (2 : Nat) := by
  rw [prefix_Dm]
  have hiK : (⟨22, by decide⟩ : Fin 41) = ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiG : (⟨9, by decide⟩ : Fin 41) = ((Fin.last 9).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiC : (⟨26, by decide⟩ : Fin 41) = ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiY : (⟨19, by decide⟩ : Fin 41) = ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hig : (⟨7, by decide⟩ : Fin 41) = ((Fin.last 7).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hiK, hiG, hiC, hiY, hig, d41_K_value, d41_G_value, d41_C_value, d41_Y_value, d41_g_value]

#print axioms d42_Dm_value
end DiophantineConsistency.Norm38MacroCheckpointDm

import DiophantineConsistency.Norm38MacroBdValue

/-! Candidate symbolic Cd from Q, F, J, H and C. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointBdCd
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointBdCd Norm38MacroCheckpointJ Norm38MacroCheckpointQ
  Norm38MacroCheckpointF Norm38MacroCheckpointH Norm38MacroDependent08

theorem d41_Cd_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a (Fin.last 40) = ((((3 : Int) : R) * (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) - ((2 : Int) : R) * ((base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R))) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R)) + (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * (((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩)) - ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩))) ^ (2 : Nat) := by
  rw [prefix_Cd]
  have h28 : d40.values a ⟨28, by decide⟩ = ((3 : Int) : R) * (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) - ((2 : Int) : R) * ((base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) := by
    have hi : ((⟨28, by decide⟩ : Fin 40).castSucc) = ((Fin.last 28).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
    calc
      d40.values a ⟨28, by decide⟩ = d41.values a ((Fin.last 28).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [← hi, lookup40_41]
      _ = ((3 : Int) : R) * (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) - ((2 : Int) : R) * ((base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) := d41_Q_value a
  have h31 : d40.values a ⟨31, by decide⟩ = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R) := by
    have hi : ((⟨31, by decide⟩ : Fin 40).castSucc) = ((Fin.last 31).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
    calc
      d40.values a ⟨31, by decide⟩ = d41.values a ((Fin.last 31).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [← hi, lookup40_41]
      _ = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R) := d41_F_value a
  have h27 : d40.values a ⟨27, by decide⟩ = ((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R) := by
    have hi : ((⟨27, by decide⟩ : Fin 40).castSucc) = ((Fin.last 27).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
    calc
      d40.values a ⟨27, by decide⟩ = d41.values a ((Fin.last 27).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [← hi, lookup40_41]
      _ = ((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R) := d41_J_value a
  have h33 : d40.values a ⟨33, by decide⟩ = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) := by
    have hi : ((⟨33, by decide⟩ : Fin 40).castSucc) = ((Fin.last 33).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
    calc
      d40.values a ⟨33, by decide⟩ = d41.values a ((Fin.last 33).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [← hi, lookup40_41]
      _ = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (a ⟨7, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) := d41_H_value a
  have h26 : d40.values a ⟨26, by decide⟩ = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩ := by
    have hi : ((⟨26, by decide⟩ : Fin 40).castSucc) = ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
    calc
      d40.values a ⟨26, by decide⟩ = d41.values a ((Fin.last 26).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [← hi, lookup40_41]
      _ = (((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩ := d41_C_value a
  rw [h28, h31, h27, h33, h26]

#print axioms d41_Cd_value
end DiophantineConsistency.Norm38MacroCheckpointBdCd

import DiophantineConsistency.Norm38MacroPKPaths
import DiophantineConsistency.Norm38MacroDependentA0

/-! Candidate symbolic A0 value from checked P and K. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointA0
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointPK Norm38MacroDependent07

theorem d35_P_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d35.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) := by
  rw [d35_P_carry]
  calc
    d28.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d27.values a ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc) := Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d22.values a (Fin.last 21) := lookup22_27 a (Fin.last 21)
    _ = ((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) := d22_P_value a

theorem d35_K_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d35.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R)) := by
  rw [d35_K_carry]
  calc
    d29.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d28.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc) := Norm38MacroCuts.snoc_previous a d28 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc) := Norm38MacroCuts.snoc_previous a d27 _ ((Fin.last 22).castSucc.castSucc.castSucc.castSucc)
    _ = d23.values a (Fin.last 22) := lookup23_27 a (Fin.last 22)
    _ = d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R)) := d23_K_value a

theorem d36_A0_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d36.values a (Fin.last 35) = ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) - ((1 : Int) : R)) * (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [prefix_A0]
  have hiP : (⟨21, by decide⟩ : Fin 35) = ((Fin.last 21).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiK : (⟨22, by decide⟩ : Fin 35) = ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hiP, hiK, d35_P_value, d35_K_value]

#print axioms d35_P_value
#print axioms d35_K_value
#print axioms d36_A0_value
end DiophantineConsistency.Norm38MacroCheckpointA0

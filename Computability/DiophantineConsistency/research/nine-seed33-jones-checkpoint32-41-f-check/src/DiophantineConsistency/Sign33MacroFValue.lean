import DiophantineConsistency.Sign33MacroEPath
import DiophantineConsistency.Sign33MacroDependentF

/-! Candidate d32 F value with symbolic rank and E. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointF
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointA Sign33MacroCheckpointD Sign33MacroCheckpointE Sign33MacroDependent05

theorem d31_A_from_d29 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d31.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) := by
  calc
    d31.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d30.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d30 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d30 _ _
    _ = d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d29 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d29 _ _

theorem d32_F_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d32.values a (Fin.last 31) = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [prefix_F]
  have hiA : (⟨23, by decide⟩ : Fin 31) = ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiE : (⟨30, by decide⟩ : Fin 31) = Fin.last 30 := by decide
  rw [hiA, hiE, d31_A_from_d29, d29_A_from_d27, d27_A_value, d31_E_value]

#print axioms d31_A_from_d29
#print axioms d32_F_value
end DiophantineConsistency.Sign33MacroCheckpointF

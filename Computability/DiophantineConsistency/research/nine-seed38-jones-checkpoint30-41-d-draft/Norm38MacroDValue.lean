import DiophantineConsistency.Norm38MacroQPath
import DiophantineConsistency.Norm38MacroAValue
import DiophantineConsistency.Norm38MacroDependentD

/-! Candidate d30 D value using symbolic rank, A and C. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointD
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointA Norm38MacroCheckpointC Norm38MacroDependent04

theorem d29_A_from_d27 {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) = d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) := by
  calc
    d29.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) = d28.values a ((Fin.last 23).castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d28 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d28 _ _
    _ = d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) := by
      change (Dag.snoc d27 _).values a (Fin.castSucc ((Fin.last 23).castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d27 _ _

theorem d30_D_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d30.values a (Fin.last 29) = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := by
  rw [prefix_D]
  have hiA : (⟨23, by decide⟩ : Fin 29) = ((Fin.last 23).castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiC : (⟨26, by decide⟩ : Fin 29) = ((Fin.last 26).castSucc.castSucc) := by decide
  rw [hiA, hiC, d29_A_from_d27, d29_C_carry, d27_A_value, d27_C_value]

#print axioms d29_A_from_d27
#print axioms d30_D_value
end DiophantineConsistency.Norm38MacroCheckpointD

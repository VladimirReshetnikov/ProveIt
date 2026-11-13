import DiophantineConsistency.Norm38MacroAValue
import DiophantineConsistency.Norm38MacroDependentJ

/-! Candidate d28 J value using symbolic A. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointJ
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointA Norm38MacroDependent04

theorem d28_J_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d28.values a (Fin.last 27) = ((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R) := by
  rw [prefix_J]
  have hi : (⟨23, by decide⟩ : Fin 27) = ((Fin.last 23).castSucc.castSucc.castSucc) := by decide
  rw [hi, d27_A_value]

#print axioms d28_J_value
end DiophantineConsistency.Norm38MacroCheckpointJ

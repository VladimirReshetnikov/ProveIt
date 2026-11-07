import DiophantineConsistency.Norm38MacroA1Path
import DiophantineConsistency.Norm38MacroDependentV

/-! Candidate symbolic V0 at its birth prefix. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointV
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointA0 Norm38MacroCheckpointA1 Norm38MacroDependent07

theorem d38_V0_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d38.values a (Fin.last 37) = (((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) - ((1 : Int) : R)) * (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) ^ (2 : Nat) + ((1 : Int) : R)) ^ (2 : Nat) + ((2 : Int) : R) := by
  rw [prefix_V0]
  have hi : (⟨35, by decide⟩ : Fin 37) = ((Fin.last 35).castSucc) := by decide
  rw [hi, d37_A0_carry, d36_A0_value]

#print axioms d38_V0_value
end DiophantineConsistency.Norm38MacroCheckpointV

import DiophantineConsistency.Sign33MacroFValue
import DiophantineConsistency.Sign33MacroCheckpoint34to41

/-! Candidate shared F checkpoint and symbolic d41 value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointF
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPrefixGroup01 Sign33MacroCheckpoint34to41

theorem path32_34 : PrefixPath d32 d34 (fun i => i.castSucc.castSucc) := by
  change PrefixPath d32 (Dag.snoc (Dag.snoc d32 _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.base d32) _) _)

theorem lookup32_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 32) :
    d34.values a i.castSucc.castSucc = d32.values a i := by
  exact lookup path32_34 a i

theorem d41_F_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 31).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R) := by
  calc
    d41.values a ((Fin.last 31).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 31).castSucc.castSucc) := lookup34_41 a ((Fin.last 31).castSucc.castSucc)
    _ = d32.values a (Fin.last 31) := lookup32_34 a (Fin.last 31)
    _ = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat)) ^ (2 : Nat) + ((1 : Int) : R) := d32_F_value a

#print axioms path32_34
#print axioms lookup32_34
#print axioms d41_F_value
end DiophantineConsistency.Sign33MacroCheckpointF

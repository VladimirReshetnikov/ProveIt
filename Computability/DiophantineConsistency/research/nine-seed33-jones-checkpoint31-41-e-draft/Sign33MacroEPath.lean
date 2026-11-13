import DiophantineConsistency.Sign33MacroEValue
import DiophantineConsistency.Sign33MacroCheckpoint34to41

/-! Candidate shared E checkpoint and symbolic d41 value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointE
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPrefixGroup01 Sign33MacroCheckpoint34to41

theorem path31_34 : PrefixPath d31 d34 (fun i => i.castSucc.castSucc.castSucc) := by
  change PrefixPath d31 (Dag.snoc (Dag.snoc (Dag.snoc d31 _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d31) _) _) _)

theorem lookup31_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 31) :
    d34.values a i.castSucc.castSucc.castSucc = d31.values a i := by
  exact lookup path31_34 a i

theorem d41_E_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 30).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat) := by
  calc
    d41.values a ((Fin.last 30).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 30).castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 30).castSucc.castSucc.castSucc)
    _ = d31.values a (Fin.last 30) := lookup31_34 a (Fin.last 30)
    _ = (a ⟨6, by decide⟩ + ((1 : Int) : R)) * (((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R)) * ((((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) +
      base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) + a ⟨5, by decide⟩) ^ (2 : Nat) := d31_E_value a

#print axioms path31_34
#print axioms lookup31_34
#print axioms d41_E_value
end DiophantineConsistency.Sign33MacroCheckpointE

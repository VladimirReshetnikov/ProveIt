import DiophantineConsistency.Sign33MacroDValue
import DiophantineConsistency.Sign33MacroCheckpoint34to41

/-! Candidate shared D checkpoint and symbolic d41 value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointD
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPrefixGroup01 Sign33MacroCheckpoint34to41

theorem path30_34 : PrefixPath d30 d34 (fun i => i.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d30 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d30 _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d30) _) _) _) _)

theorem lookup30_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 30) :
    d34.values a i.castSucc.castSucc.castSucc.castSucc = d30.values a i := by
  exact lookup path30_34 a i

theorem d41_D_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := by
  calc
    d41.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 29).castSucc.castSucc.castSucc.castSucc)
    _ = d30.values a (Fin.last 29) := lookup30_34 a (Fin.last 29)
    _ = (((d11.values a (Fin.last 10) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * ((((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat)) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) ^ (2 : Nat) + ((1 : Int) : R) := d30_D_value a

#print axioms path30_34
#print axioms lookup30_34
#print axioms d41_D_value
end DiophantineConsistency.Sign33MacroCheckpointD

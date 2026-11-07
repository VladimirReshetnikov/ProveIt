import DiophantineConsistency.Sign33MacroA0Value

/-! Candidate shared d36-to-d41 checkpoint and symbolic A0. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointA0
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding Sign33MacroPrefixGroup01

theorem path36_41 : PrefixPath d36 d41 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d36 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d36 _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d36) _) _) _) _) _)

theorem lookup36_41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 36) :
    d41.values a i.castSucc.castSucc.castSucc.castSucc.castSucc = d36.values a i := lookup path36_41 a i

theorem d41_A0_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 35).castSucc.castSucc.castSucc.castSucc.castSucc) = ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) - ((1 : Int) : R)) * (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) ^ (2 : Nat) + ((1 : Int) : R) := by
  calc
    d41.values a ((Fin.last 35).castSucc.castSucc.castSucc.castSucc.castSucc) = d36.values a (Fin.last 35) := lookup36_41 a (Fin.last 35)
    _ = ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) - ((1 : Int) : R)) * (d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R))) ^ (2 : Nat) + ((1 : Int) : R) := d36_A0_value a

#print axioms path36_41
#print axioms lookup36_41
#print axioms d41_A0_value
end DiophantineConsistency.Sign33MacroCheckpointA0

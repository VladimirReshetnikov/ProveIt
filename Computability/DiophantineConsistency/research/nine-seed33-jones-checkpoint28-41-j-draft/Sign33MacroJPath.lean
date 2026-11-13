import DiophantineConsistency.Sign33MacroJValue
import DiophantineConsistency.Sign33MacroCheckpoint34to41

/-! Candidate shared J checkpoint and symbolic d41 value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointJ
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPrefixGroup01 Sign33MacroCheckpoint34to41

theorem path28_34 : PrefixPath d28 d34 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d28 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d28 _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d28) _) _) _) _) _) _)

theorem lookup28_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 28) :
    d34.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d28.values a i := by
  exact lookup path28_34 a i

theorem d41_J_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 27).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R) := by
  calc
    d41.values a ((Fin.last 27).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 27).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 27).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d28.values a (Fin.last 27) := lookup28_34 a (Fin.last 27)
    _ = ((4 : Int) : R) * ((d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R))) - ((5 : Int) : R) := d28_J_value a

#print axioms path28_34
#print axioms lookup28_34
#print axioms d41_J_value
end DiophantineConsistency.Sign33MacroCheckpointJ

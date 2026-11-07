import DiophantineConsistency.Sign33MacroQValue
import DiophantineConsistency.Sign33MacroCheckpoint34to41

/-! Candidate shared Q checkpoint and symbolic d41 value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointQ
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPrefixGroup01 Sign33MacroCheckpoint34to41

theorem path29_34 : PrefixPath d29 d34 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d29 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d29 _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d29) _) _) _) _) _)

theorem lookup29_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 29) :
    d34.values a i.castSucc.castSucc.castSucc.castSucc.castSucc = d29.values a i := by
  exact lookup path29_34 a i

theorem d41_Q_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 28).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((3 : Int) : R) * (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) - ((2 : Int) : R) * ((base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) := by
  calc
    d41.values a ((Fin.last 28).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 28).castSucc.castSucc.castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 28).castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d29.values a (Fin.last 28) := lookup29_34 a (Fin.last 28)
    _ = ((3 : Int) : R) * (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) * ((((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R)) + (base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + a ⟨5, by decide⟩) - ((2 : Int) : R) * ((base a * (a ⟨4, by decide⟩ + ((1 : Int) : R))) ^ (2 : Nat) - ((1 : Int) : R)) := d29_Q_value a

#print axioms path29_34
#print axioms lookup29_34
#print axioms d41_Q_value
end DiophantineConsistency.Sign33MacroCheckpointQ

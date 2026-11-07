import DiophantineConsistency.Sign33MacroPath18to45
import DiophantineConsistency.Sign33MacroLive18Group03
import DiophantineConsistency.Sign33MacroPrefixInputsB

/-! Candidate later checkpoint path and one concrete phi value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpoint27to34
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPath18to34 Sign33MacroLive18 Sign33MacroPrefixGroup04

theorem path27_34 : PrefixPath d27 d34 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d27 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d27 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d27) _) _) _) _) _) _) _)

theorem lookup27_34 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 27) :
    d34.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d27.values a i := by
  exact lookup path27_34 a i

theorem d34_phi_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d34.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨5, by decide⟩ := by
  calc
    d34.values a ((Fin.last 14).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) := lookup18_34 a ((Fin.last 14).castSucc.castSucc.castSucc)
    _ = d15.values a (Fin.last 14) := d18_phi_carry a
    _ = a ⟨5, by decide⟩ := prefix_phi a

#print axioms path27_34
#print axioms lookup27_34
#print axioms d34_phi_value
end DiophantineConsistency.Sign33MacroCheckpoint27to34

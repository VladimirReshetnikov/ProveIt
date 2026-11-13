import DiophantineConsistency.Norm38MacroPath18to45
import DiophantineConsistency.Norm38MacroLive18Group03
import DiophantineConsistency.Norm38MacroPrefixInputsB

/-! Candidate later checkpoint path and one concrete phi value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpoint27to34
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding
  Norm38MacroPath18to34 Norm38MacroLive18 Norm38MacroPrefixGroup04

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
end DiophantineConsistency.Norm38MacroCheckpoint27to34

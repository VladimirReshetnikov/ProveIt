import DiophantineConsistency.Norm38MacroCheckpoint27to34
import DiophantineConsistency.Norm38MacroLive18Group01
import DiophantineConsistency.Norm38MacroPrefixQNCarry

/-! Candidate later checkpoint path and one symbolic N value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpoint34to41
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixEmbedding
  Norm38MacroPath18to41 Norm38MacroLive18 Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup05

theorem path34_41 : PrefixPath d34 d41 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d34 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d34 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d34) _) _) _) _) _) _) _)

theorem lookup34_41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 34) :
    d41.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d34.values a i := by
  exact lookup path34_41 a i

theorem d41_N_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat) := by
  calc
    d41.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup18_41 a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := d18_N_carry a
    _ = d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d10 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat) := d10_N a

#print axioms path34_41
#print axioms lookup34_41
#print axioms d41_N_value
end DiophantineConsistency.Norm38MacroCheckpoint34to41

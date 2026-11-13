import DiophantineConsistency.Sign33MacroCheckpoint27to34
import DiophantineConsistency.Sign33MacroLive18Group01
import DiophantineConsistency.Sign33MacroPrefixQNCarry

/-! Candidate later checkpoint path and one symbolic N value. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpoint34to41
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixEmbedding
  Sign33MacroPath18to41 Sign33MacroLive18 Sign33MacroPrefixGroup01 Sign33MacroPrefixGroup05

theorem path34_41 : PrefixPath d34 d41 (fun i => i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
  change PrefixPath d34 (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc (Dag.snoc d34 _) _) _) _) _) _) _) _
  exact (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.step (PrefixPath.base d34) _) _) _) _) _) _) _)

theorem lookup34_41 {R : Type*} [CommRing R] (a : Fin 9 → R) (i : Fin 34) :
    d41.values a i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc = d34.values a i := by
  exact lookup path34_41 a i

theorem d41_N_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := by
  calc
    d41.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup18_41 a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d11.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := d18_N_carry a
    _ = d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d10 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := d10_N a

#print axioms path34_41
#print axioms lookup34_41
#print axioms d41_N_value
end DiophantineConsistency.Sign33MacroCheckpoint34to41

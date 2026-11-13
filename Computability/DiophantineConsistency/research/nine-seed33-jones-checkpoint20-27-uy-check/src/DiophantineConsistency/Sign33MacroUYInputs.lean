import DiophantineConsistency.Sign33MacroCheckpoint41to45
import DiophantineConsistency.Sign33MacroLive18Group01
import DiophantineConsistency.Sign33MacroLive18Group03
import DiophantineConsistency.Sign33MacroPrefixInputsA
import DiophantineConsistency.Sign33MacroPrefixQNCarry

/-! Candidate d18 input values; giant powers remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointUY
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroPrefixGroup04 Sign33MacroPrefixGroup05 Sign33MacroLive18

theorem d18_N_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := by
  calc
    d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := d18_N_carry a
    _ = d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d10 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = ((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat) := d10_N a

theorem d18_s_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨3, by decide⟩ + ((1 : Int) : R) :=
  (d18_s_carry a).trans (prefix_s a)

theorem d18_w_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) = a ⟨4, by decide⟩ + ((1 : Int) : R) :=
  (d18_w_carry a).trans (prefix_w a)

#print axioms d18_N_value
#print axioms d18_s_value
#print axioms d18_w_value
end DiophantineConsistency.Sign33MacroCheckpointUY

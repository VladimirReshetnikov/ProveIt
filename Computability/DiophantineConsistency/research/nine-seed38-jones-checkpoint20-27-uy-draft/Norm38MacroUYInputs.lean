import DiophantineConsistency.Norm38MacroCheckpoint41to45
import DiophantineConsistency.Norm38MacroLive18Group01
import DiophantineConsistency.Norm38MacroLive18Group03
import DiophantineConsistency.Norm38MacroPrefixInputsA
import DiophantineConsistency.Norm38MacroPrefixQNCarry

/-! Candidate d18 input values; giant powers remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointUY
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroPrefixGroup04 Norm38MacroPrefixGroup05 Norm38MacroLive18

theorem d18_N_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat) := by
  calc
    d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := d18_N_carry a
    _ = d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d10 _ ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat) := d10_N a

theorem d18_s_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) = a ⟨3, by decide⟩ + ((1 : Int) : R) :=
  (d18_s_carry a).trans (prefix_s a)

theorem d18_w_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) = a ⟨4, by decide⟩ + ((1 : Int) : R) :=
  (d18_w_carry a).trans (prefix_w a)

#print axioms d18_N_value
#print axioms d18_s_value
#print axioms d18_w_value
end DiophantineConsistency.Norm38MacroCheckpointUY

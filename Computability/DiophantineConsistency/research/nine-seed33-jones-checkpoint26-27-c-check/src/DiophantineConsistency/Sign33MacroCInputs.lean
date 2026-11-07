import DiophantineConsistency.Sign33MacroJPath
import DiophantineConsistency.Sign33MacroLive18Group01
import DiophantineConsistency.Sign33MacroLive18Group03
import DiophantineConsistency.Sign33MacroPrefixInputsB
import DiophantineConsistency.Sign33MacroPrefixGlarge

/-! Candidate symbolic d18 b/phi values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointC
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroPrefixGroup03 Sign33MacroPrefixGroup04 Sign33MacroLive18

theorem d18_b_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = base a := by
  calc
    d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := d18_b_carry a
    _ = d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d10 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Sign33MacroCuts.snoc_previous a d9 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = base a := d9_b a

theorem d18_phi_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) = a ⟨5, by decide⟩ :=
  (d18_phi_carry a).trans (prefix_phi a)

#print axioms d18_b_value
#print axioms d18_phi_value
end DiophantineConsistency.Sign33MacroCheckpointC

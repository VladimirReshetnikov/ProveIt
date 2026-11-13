import DiophantineConsistency.Norm38MacroJPath
import DiophantineConsistency.Norm38MacroLive18Group01
import DiophantineConsistency.Norm38MacroLive18Group03
import DiophantineConsistency.Norm38MacroPrefixInputsB
import DiophantineConsistency.Norm38MacroPrefixGlarge

/-! Candidate symbolic d18 b/phi values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointC
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroPrefixGroup03 Norm38MacroPrefixGroup04 Norm38MacroLive18

theorem d18_b_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = base a := by
  calc
    d18.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := d18_b_carry a
    _ = d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d10 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d10 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
      change (Dag.snoc d9 _).values a (Fin.castSucc ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) = _
      exact Norm38MacroCuts.snoc_previous a d9 _ ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = base a := d9_b a

theorem d18_phi_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d18.values a ((Fin.last 14).castSucc.castSucc.castSucc) = a ⟨5, by decide⟩ :=
  (d18_phi_carry a).trans (prefix_phi a)

#print axioms d18_b_value
#print axioms d18_phi_value
end DiophantineConsistency.Norm38MacroCheckpointC

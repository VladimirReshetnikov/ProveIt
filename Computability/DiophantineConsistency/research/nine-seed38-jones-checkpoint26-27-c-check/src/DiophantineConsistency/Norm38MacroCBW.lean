import DiophantineConsistency.Norm38MacroCInputs
import DiophantineConsistency.Norm38MacroDependentW
import DiophantineConsistency.Norm38MacroLive18Group02
import DiophantineConsistency.Norm38MacroUYInputs

/-! Candidate d26 Bprime/W values with opaque rank. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointC
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointUY Norm38MacroDependent03 Norm38MacroLive18

theorem d26_Bprime_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d26.values a ((Fin.last 24).castSucc) = ((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R) := by
  calc
    d26.values a ((Fin.last 24).castSucc) = d25.values a (Fin.last 24) := by
      change (Dag.snoc d25 _).values a (Fin.castSucc (Fin.last 24)) = _
      exact Norm38MacroCuts.snoc_previous a d25 _ (Fin.last 24)
    _ = ((2 : Int) : R) * d24.values a ⟨10, by decide⟩ + ((1 : Int) : R) := prefix_Bprime a
    _ = ((2 : Int) : R) * d11.values a (Fin.last 10) + ((1 : Int) : R) := by
      have hi : (⟨10, by decide⟩ : Fin 24) = ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
      rw [hi, d24_R_carry, d18_R_carry]

theorem d26_W_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d26.values a (Fin.last 25) = base a * (a ⟨4, by decide⟩ + ((1 : Int) : R)) := by
  rw [prefix_W]
  have hib : (⟨0, by decide⟩ : Fin 25) = ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  have hiw : (⟨13, by decide⟩ : Fin 25) = ((Fin.last 13).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
  rw [hib, hiw, d25_b_carry, d25_w_carry, d18_b_value, d18_w_value]

#print axioms d26_Bprime_value
#print axioms d26_W_value
end DiophantineConsistency.Norm38MacroCheckpointC

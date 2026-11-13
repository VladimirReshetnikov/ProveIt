import DiophantineConsistency.Sign33MacroMPath
import DiophantineConsistency.Sign33MacroDependentM
import DiophantineConsistency.Sign33MacroLive18Group02

/-! Candidate d27 M value using symbolic Y and opaque rank. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointM
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointUY Sign33MacroDependent02 Sign33MacroLive18

theorem d27_M_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a ((Fin.last 20).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R))) := by
  calc
    d27.values a ((Fin.last 20).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d21.values a (Fin.last 20) := lookup21_27 a (Fin.last 20)
    _ = d20.values a ⟨10, by decide⟩ * d20.values a ⟨19, by decide⟩ := prefix_M a
    _ = d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R))) := by
      have hiR : (⟨10, by decide⟩ : Fin 20) = ((Fin.last 10).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by decide
      have hiY : (⟨19, by decide⟩ : Fin 20) = Fin.last 19 := by decide
      have hR : d20.values a ⟨10, by decide⟩ = d11.values a (Fin.last 10) := by
        rw [hiR, d20_R_carry, d18_R_carry]
      have hY : d20.values a ⟨19, by decide⟩ = (((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)) := by
        rw [hiY]
        exact (lookup20_27 a (Fin.last 19)).symm.trans (d27_Y_value a)
      rw [hR, hY]

#print axioms d27_M_value
end DiophantineConsistency.Sign33MacroCheckpointM

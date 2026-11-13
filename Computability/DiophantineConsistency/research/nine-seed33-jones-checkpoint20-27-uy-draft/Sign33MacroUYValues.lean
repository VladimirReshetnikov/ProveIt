import DiophantineConsistency.Sign33MacroUYPath
import DiophantineConsistency.Sign33MacroDependentY

/-! Candidate concrete d27 U/Y values, with all powers symbolic. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointUY
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01 Sign33MacroDependent01

theorem d27_U_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a ((Fin.last 18).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)) := by
  calc
    d27.values a ((Fin.last 18).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d20.values a ((Fin.last 18).castSucc) := lookup20_27 a ((Fin.last 18).castSucc)
    _ = d19.values a (Fin.last 18) := by
      change (Dag.snoc d19 _).values a (Fin.castSucc (Fin.last 18)) = _
      exact Sign33MacroCuts.snoc_previous a d19 _ (Fin.last 18)
    _ = (d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (2 : Nat) * d18.values a ((Fin.last 13).castSucc.castSucc.castSucc.castSucc) := prefix_U a
    _ = (((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)) := by
      rw [d18_N_value, d18_w_value]

theorem d27_Y_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)) := by
  calc
    d27.values a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d20.values a (Fin.last 19) := lookup20_27 a (Fin.last 19)
    _ = (d18.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)) ^ (2 : Nat) * d18.values a ((Fin.last 12).castSucc.castSucc.castSucc.castSucc.castSucc) := prefix_Y a
    _ = (((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)) := by
      rw [d18_N_value, d18_s_value]

#print axioms d27_U_value
#print axioms d27_Y_value
end DiophantineConsistency.Sign33MacroCheckpointUY

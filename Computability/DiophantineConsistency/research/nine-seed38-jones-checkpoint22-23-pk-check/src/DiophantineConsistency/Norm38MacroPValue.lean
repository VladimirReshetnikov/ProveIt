import DiophantineConsistency.Norm38MacroIPath
import DiophantineConsistency.Norm38MacroDependentP

/-! Candidate symbolic P from checked M and U values. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointPK
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointM Norm38MacroCheckpointUY Norm38MacroDependent02

theorem d22_P_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d22.values a (Fin.last 21) = ((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) := by
  rw [prefix_P]
  have hiM : (⟨20, by decide⟩ : Fin 21) = Fin.last 20 := by decide
  have hiU : (⟨18, by decide⟩ : Fin 21) = ((Fin.last 18).castSucc.castSucc) := by decide
  have hM : d21.values a (Fin.last 20) = d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R))) :=
    (lookup21_27 a (Fin.last 20)).symm.trans (d27_M_value a)
  have hU : d21.values a ((Fin.last 18).castSucc.castSucc) = (((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)) := by
    rw [d21_U_carry]
    exact (Norm38MacroCuts.snoc_previous a d19 _ (Fin.last 18)).symm.trans
      ((lookup20_27 a ((Fin.last 18).castSucc)).symm.trans (d27_U_value a))
  rw [hiM, hiU, hM, hU]

#print axioms d22_P_value
end DiophantineConsistency.Norm38MacroCheckpointPK

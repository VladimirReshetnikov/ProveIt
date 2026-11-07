import DiophantineConsistency.Sign33MacroAPath
import DiophantineConsistency.Sign33MacroDependentA

/-! Candidate d27 A value using symbolic M and U. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign33MacroCheckpointA
open Sign33MacroLanguage Sign33MacroPrefixes Sign33MacroPrefixGroup01
  Sign33MacroCheckpointUY Sign33MacroCheckpointM Sign33MacroDependent03

theorem d27_A_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) =
      (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R)) := by
  calc
    d27.values a ((Fin.last 23).castSucc.castSucc.castSucc) = d24.values a (Fin.last 23) := lookup24_27 a (Fin.last 23)
    _ = d23.values a ⟨20, by decide⟩ * (d23.values a ⟨18, by decide⟩ + ((1 : Int) : R)) := prefix_A a
    _ = (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) * (((((base a ^ (5 : Nat)) ^ (5 ^ 34 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R))) + ((1 : Int) : R)) := by
      have hiM : (⟨20, by decide⟩ : Fin 23) = ((Fin.last 20).castSucc.castSucc) := by decide
      have hiU : (⟨18, by decide⟩ : Fin 23) = ((Fin.last 18).castSucc.castSucc.castSucc.castSucc) := by decide
      have hM : d23.values a ⟨20, by decide⟩ = d27.values a ((Fin.last 20).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [hiM, d23_M_carry]
        exact (lookup21_27 a (Fin.last 20)).symm
      have hU : d23.values a ⟨18, by decide⟩ = d27.values a ((Fin.last 18).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := by
        rw [hiU, d23_U_carry]
        exact (Sign33MacroCuts.snoc_previous a d19 _ (Fin.last 18)).symm.trans
          ((lookup20_27 a ((Fin.last 18).castSucc)).symm)
      rw [hM, hU, d27_M_value, d27_U_value]

#print axioms d27_A_value
end DiophantineConsistency.Sign33MacroCheckpointA

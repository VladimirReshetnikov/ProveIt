import DiophantineConsistency.Norm38MacroCdValue
import DiophantineConsistency.Norm38MacroCheckpoint41to45

/-! Candidate symbolic K/Y at d41 using checked shared paths. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroCheckpointDm
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroCheckpointPK Norm38MacroCheckpointA0 Norm38MacroCheckpointUY
  Norm38MacroCheckpoint27to34 Norm38MacroCheckpoint34to41

theorem d41_K_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R)) := by
  calc
    d41.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc) := lookup27_34 a ((Fin.last 22).castSucc.castSucc.castSucc.castSucc)
    _ = d23.values a (Fin.last 22) := lookup23_27 a (Fin.last 22)
    _ = d11.values a (Fin.last 10) + ((1 : Int) : R) + (a ⟨2, by decide⟩ + ((1 : Int) : R)) * ((((2 : Int) : R) * (d11.values a (Fin.last 10) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)))) ^ (2 : Nat) * ((((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨4, by decide⟩ + ((1 : Int) : R)))) - ((1 : Int) : R)) := d23_K_value a

theorem d41_Y_value {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d41.values a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = (((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)) := by
  calc
    d41.values a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) = d34.values a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup34_41 a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = d27.values a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc) := lookup27_34 a ((Fin.last 19).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
    _ = (((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat)) ^ (2 : Nat) * (a ⟨3, by decide⟩ + ((1 : Int) : R)) := d27_Y_value a

#print axioms d41_K_value
#print axioms d41_Y_value
end DiophantineConsistency.Norm38MacroCheckpointDm

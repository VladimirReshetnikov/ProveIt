import OAI.Combinatorics.Progressions.Geometry.FiniteChoiceLeafCoordinates
import OAI.Combinatorics.Progressions.Geometry.MixedReplicatedCoordinates

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def mixedChoiceAssignmentEquiv (s n : ℕ) :
    (Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) ≃ (Fin s → Fin (n + 1)) where
  toFun v j := v (Fin.cast (mixedRepeatedCoordinates_length s).symm j)
  invFun v j := v (Fin.cast (mixedRepeatedCoordinates_length s) j)
  left_inv v := by funext j; rfl
  right_inv v := by funext j; rfl

def mixedChoiceSample {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (j : Fin (n + 1) × MixedReplicatedIndex s) : ℤ :=
  correlationInput h (y j.1) j.2.1

theorem mixedChoiceSample_head {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ) (a : Fin (n + 1)) :
    mixedChoiceSample h y (a, mixedHead s) = h := rfl

theorem mixedChoiceSample_replica {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (a : Fin (n + 1)) (j : Fin s) : mixedChoiceSample h y (a, mixedReplica j) = y a := rfl

theorem mixedChoiceSample_sum {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ) :
    finiteChoiceCoordinateInput (mixedRepeatedCoordinates s) (mixedChoiceSample h y) =
      mixedReplicatedInput h (fun _ : Fin s => ∑ a, y a) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head]
    simp [finiteChoiceCoordinateInput, mem_mixedRepeatedCoordinates, mixedHead,
      mixedChoiceSample, correlationInput]
  · rw [mixedReplicatedInput_replica]
    have hi : mixedReplica i ∈ mixedRepeatedCoordinates s :=
      (mem_mixedRepeatedCoordinates s _).mpr rfl
    simp only [finiteChoiceCoordinateInput, hi, ite_true, mixedChoiceSample_replica]

theorem mixedChoiceSample_leaf {s n : ℕ} (h : ℤ) (y : Fin (n + 1) → ℤ)
    (v : Fin (mixedRepeatedCoordinates s).length → Fin (n + 1)) :
    finiteChoiceLeafInput (mixedRepeatedCoordinates s) v (mixedChoiceSample h y) =
      mixedReplicatedInput h (fun j => y (mixedChoiceAssignmentEquiv s n v j)) := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rw [mixedReplicatedInput_head]
    have hnot : mixedHead s ∉ mixedRepeatedCoordinates s := by
      simp [mem_mixedRepeatedCoordinates, mixedHead]
    rw [finiteChoiceLeafInput_of_not_mem _ v _ _ hnot]
    rfl
  · rw [mixedReplicatedInput_replica]
    let k : Fin (mixedRepeatedCoordinates s).length := Fin.cast (mixedRepeatedCoordinates_length s).symm i
    have H := finiteChoiceLeafInput_get (mixedRepeatedCoordinates s)
      (mixedRepeatedCoordinates_nodup s) v (mixedChoiceSample h y) k
    rw [mixedRepeatedCoordinates_get] at H
    have hk : Fin.cast (mixedRepeatedCoordinates_length s) k = i := rfl
    rw [hk, mixedChoiceSample_replica] at H
    exact H

end Erdos3

end

end OAI

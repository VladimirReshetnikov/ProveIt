import Mathlib.Data.List.OfFn
import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments

namespace OAI

section

namespace Erdos3

abbrev MixedReplicatedIndex (s : ℕ) := ReplicatedIndex (mixedCorrelationDegree s)

def mixedHead (s : ℕ) : MixedReplicatedIndex s := ⟨0, ⟨0, by change 0 < 1; omega⟩⟩

def mixedReplica {s : ℕ} (j : Fin s) : MixedReplicatedIndex s := ⟨1, ⟨j.val, j.isLt⟩⟩

theorem mixedReplica_injective (s : ℕ) : Function.Injective (mixedReplica (s := s)) := by
  intro i j h
  exact Fin.ext (congrArg (fun a : MixedReplicatedIndex s => a.2.val) h)

theorem mixedReplicated_cases {s : ℕ} (j : MixedReplicatedIndex s) :
    j = mixedHead s ∨ ∃ i : Fin s, j = mixedReplica i := by
  rcases j with ⟨b, j⟩
  fin_cases b
  · left
    change Fin 1 at j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    rfl
  · exact Or.inr ⟨⟨j.val, j.isLt⟩, rfl⟩

def mixedRepeatedCoordinates (s : ℕ) : List (MixedReplicatedIndex s) :=
  List.ofFn (mixedReplica (s := s))

theorem mixedRepeatedCoordinates_length (s : ℕ) : (mixedRepeatedCoordinates s).length = s := by
  simp only [mixedRepeatedCoordinates, List.length_ofFn]

theorem mixedRepeatedCoordinates_nodup (s : ℕ) : (mixedRepeatedCoordinates s).Nodup :=
  List.nodup_ofFn.mpr (mixedReplica_injective s)

theorem mixedRepeatedCoordinates_get (s : ℕ) (j : Fin (mixedRepeatedCoordinates s).length) :
    (mixedRepeatedCoordinates s).get j = mixedReplica (Fin.cast (mixedRepeatedCoordinates_length s) j) := by
  exact List.get_ofFn (mixedReplica (s := s)) j

theorem mem_mixedRepeatedCoordinates (s : ℕ) (j : MixedReplicatedIndex s) :
    j ∈ mixedRepeatedCoordinates s ↔ j.1 = 1 := by
  change j ∈ List.ofFn (mixedReplica (s := s)) ↔ j.1 = 1
  constructor
  · intro h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
    rfl
  · intro h
    rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
    · norm_num [mixedHead] at h
    · exact List.mem_ofFn.mpr ⟨i, rfl⟩

def mixedReplicatedInput {s : ℕ} {α : Type*} (h : α) (v : Fin s → α)
    (j : MixedReplicatedIndex s) : α :=
  if hj : j.1 = 1 then v ⟨j.2.val, by
    have hs : mixedCorrelationDegree s j.1 = s := by rw [hj]; rfl
    simpa only [hs] using j.2.isLt⟩
  else h

theorem mixedReplicatedInput_head {s : ℕ} {α : Type*} (h : α) (v : Fin s → α) :
    mixedReplicatedInput h v (mixedHead s) = h := rfl

theorem mixedReplicatedInput_replica {s : ℕ} {α : Type*} (h : α) (v : Fin s → α) (j : Fin s) :
    mixedReplicatedInput h v (mixedReplica j) = v j := rfl

theorem mixedReplicatedInput_diagonal {s : ℕ} {α : Type*} (h n : α) :
    mixedReplicatedInput h (fun _ : Fin s => n) =
      fun j : MixedReplicatedIndex s => correlationInput h n j.1 := by
  funext j
  rcases mixedReplicated_cases j with rfl | ⟨i, rfl⟩
  · rfl
  · rfl

end Erdos3

end

end OAI

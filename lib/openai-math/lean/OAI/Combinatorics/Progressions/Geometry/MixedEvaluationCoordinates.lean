import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments

namespace OAI

section

namespace Erdos3

def mixedEvaluationEmbedding (s : ℕ) : Fin s ↪ ReplicatedIndex (mixedCorrelationDegree s) where
  toFun k := ⟨1, k⟩
  inj' := by
    intro i j hij
    exact Fin.ext (congrArg (fun z : ReplicatedIndex (mixedCorrelationDegree s) => z.2.val) hij)

def mixedEvaluationCoordinates (s : ℕ) : Finset (ReplicatedIndex (mixedCorrelationDegree s)) :=
  Finset.univ.map (mixedEvaluationEmbedding s)

@[simp] theorem mem_mixedEvaluationCoordinates (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s)) :
    j ∈ mixedEvaluationCoordinates s ↔ j.1 = 1 := by
  constructor
  · intro hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_map.mp hj
    rfl
  · intro hj
    rcases j with ⟨j, k⟩
    dsimp only at hj
    subst j
    exact Finset.mem_map.mpr ⟨k, Finset.mem_univ _, rfl⟩

@[simp] theorem mixedEvaluationCoordinates_card (s : ℕ) :
    (mixedEvaluationCoordinates s).card = s := by
  simp only [mixedEvaluationCoordinates, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem mixedEvaluationCoordinates_erase_card (s : ℕ)
    (i : ReplicatedIndex (mixedCorrelationDegree s)) (hi : i.1 = 1) :
    ((mixedEvaluationCoordinates s).erase i).card = s - 1 := by
  rw [Finset.card_erase_of_mem ((mem_mixedEvaluationCoordinates s i).mpr hi),
    mixedEvaluationCoordinates_card]

end Erdos3

end

end OAI

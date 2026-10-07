import OAI.Combinatorics.Progressions.Estimates.NativeBinaryAssignments

namespace OAI

section

namespace Erdos3

def mixedShiftCoordinate (s : ℕ) : ReplicatedIndex (mixedCorrelationDegree s) :=
  ⟨0, ⟨0, by change 0 < 1; omega⟩⟩

theorem mixedShiftCoordinate_unique (s : ℕ) (j : ReplicatedIndex (mixedCorrelationDegree s))
    (hj : j.1 = 0) : j = mixedShiftCoordinate s := by
  rcases j with ⟨j, k⟩
  dsimp only at hj
  subst j
  dsimp only [mixedShiftCoordinate]
  apply congrArg (fun t : Fin (mixedCorrelationDegree s 0) =>
    (⟨0, t⟩ : ReplicatedIndex (mixedCorrelationDegree s)))
  apply Fin.ext
  have hk := k.isLt
  change k.val < 1 at hk
  change k.val = 0
  omega

theorem mixed_input_eq_coordinateConstant (s : ℕ) (h n : ℤ) :
    (fun j : ReplicatedIndex (mixedCorrelationDegree s) => correlationInput h n j.1) =
      coordinateConstantInput (mixedShiftCoordinate s) h n := by
  funext j
  by_cases hj : j = mixedShiftCoordinate s
  · subst j
    simp [coordinateConstantInput, mixedShiftCoordinate, correlationInput]
  · have hj₀ : j.1 ≠ 0 := fun h => hj (mixedShiftCoordinate_unique s j h)
    have hj₁ : j.1 = 1 := by
      apply Fin.ext
      have hlt := j.1.isLt
      have hne : j.1.val ≠ 0 := fun h => hj₀ (Fin.ext h)
      change j.1.val = 1
      omega
    rw [hj₁, coordinateConstantInput, Function.update_of_ne hj]
    rfl

end Erdos3

end

end OAI

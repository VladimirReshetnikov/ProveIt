/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.LowTaggedCoordinateRestriction

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedCoordinates (d : ℕ) (x : ∀ j, J j → ℝ) :
    Fin (Fintype.card (LowTaggedIndex J d)) → ℝ :=
  fun i => x (lowTaggedIndex J d i).1 (lowTaggedIndex J d i).2

@[simp] theorem lowTaggedCoordinates_apply_slot (d : ℕ) (x : ∀ j, J j → ℝ)
    (j : Fin m) (hj : j.val + 1 ≤ d) (k : J j) :
    lowTaggedCoordinates J d x (lowTaggedSlot J d j hj k) = x j k := by
  unfold lowTaggedCoordinates
  rw [lowTaggedIndex_slot]

theorem lowTaggedCoordinates_projection (d : ℕ) (x : ∀ j, J j → ℝ)
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (j.val + 1)
        (lowTaggedCoordinates J d x) =
      lowTaggedEmbedding J d j hj (x j) := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, hk⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    subst i
    simp [lowTaggedWeight]
  · have hweight : lowTaggedWeight J d i ≠ j.val + 1 := by
      intro he
      apply hi
      apply Fin.ext
      unfold lowTaggedWeight at he
      omega
    rw [ite_eq_right hweight, lowTaggedEmbedding_apply_of_ne J d j hj _ i hi]

theorem lowTaggedCoordinates_projection_eq_zero (d : ℕ) (x : ∀ j, J j → ℝ)
    (h : ℕ) (hm : m ≤ h) :
    basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (h + 1)
      (lowTaggedCoordinates J d x) = 0 := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  have hweight : lowTaggedWeight J d i ≠ h + 1 := by
    have hi := (lowTaggedIndex J d i).1.isLt
    unfold lowTaggedWeight
    omega
  simp only [hweight, ite_false, Pi.zero_apply]

end Erdos3.VectorPolynomial

end

end OAI

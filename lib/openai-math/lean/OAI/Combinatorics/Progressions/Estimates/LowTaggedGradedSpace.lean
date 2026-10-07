/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Linear.LowTaggedCoordinateProjection
import OAI.Combinatorics.Progressions.Sampling.LowTaggedSamplingRank

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedSubspaceFamily (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) : Submodule ℝ (J j → ℝ) :=
  if hj : j.val + 1 ≤ d then K.comap (lowTaggedEmbedding J d j hj) else ⊤

theorem mem_lowTaggedSubspaceFamily_iff (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) (hj : j.val + 1 ≤ d) (x : J j → ℝ) :
    x ∈ lowTaggedSubspaceFamily J d K j ↔ lowTaggedEmbedding J d j hj x ∈ K := by
  simp only [lowTaggedSubspaceFamily, dite_eq_left hj, Submodule.mem_comap]

theorem lowTaggedSubspaceFamily_of_high (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (j : Fin m) (hj : d < j.val + 1) : lowTaggedSubspaceFamily J d K j = ⊤ := by
  simp only [lowTaggedSubspaceFamily, dite_eq_right (not_le_of_gt hj)]

theorem le_lowTaggedSubspaceFamily (d : ℕ)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hUK : ∀ h : Fin d, lowTaggedRetained J d U h ≤ K) (j : Fin m) :
    U j ≤ lowTaggedSubspaceFamily J d K j := by
  intro x hx
  by_cases hj : j.val + 1 ≤ d
  · rw [mem_lowTaggedSubspaceFamily_iff J d K j hj]
    let h : Fin d := ⟨j.val, by omega⟩
    apply hUK h
    have heq : lowTaggedRetained J d U h =
        (U j).map (lowTaggedEmbedding J d j hj) := by
      simp only [lowTaggedRetained, h, dite_eq_left j.isLt]
    rw [heq]
    exact Submodule.mem_map.mpr ⟨x, hx, rfl⟩
  · simp only [lowTaggedSubspaceFamily, dite_eq_right hj, Submodule.mem_top]

theorem lowTaggedCoordinates_mem_iff (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ K ↔ ∀ j, x j ∈ lowTaggedSubspaceFamily J d K j := by
  constructor
  · intro hx j
    by_cases hj : j.val + 1 ≤ d
    · rw [mem_lowTaggedSubspaceFamily_iff J d K j hj]
      rw [← lowTaggedCoordinates_projection J d x j hj]
      exact hK (j.val + 1) _ hx
    · simp only [lowTaggedSubspaceFamily, dite_eq_right hj, Submodule.mem_top]
  · intro hx
    rw [← sum_positive_coordinate_grades (lowTaggedWeight J d) d
      (lowTaggedWeight_pos J d) (lowTaggedWeight_le J d) (lowTaggedCoordinates J d x)]
    apply Submodule.sum_mem
    intro h _
    by_cases hm : h.val < m
    · let j : Fin m := ⟨h.val, hm⟩
      have hj : j.val + 1 ≤ d := by exact Nat.succ_le_of_lt h.isLt
      have hjmem := (mem_lowTaggedSubspaceFamily_iff J d K j hj (x j)).mp (hx j)
      rw [lowTaggedCoordinates_projection J d x j hj]
      exact hjmem
    · rw [lowTaggedCoordinates_projection_eq_zero J d x h.val (Nat.le_of_not_gt hm)]
      exact K.zero_mem

theorem lowTaggedCoordinates_mem_iff_low (d : ℕ)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K)
    (x : ∀ j, J j → ℝ) :
    lowTaggedCoordinates J d x ∈ K ↔
      ∀ j, j.val + 1 ≤ d → x j ∈ lowTaggedSubspaceFamily J d K j := by
  rw [lowTaggedCoordinates_mem_iff J d K hK x]
  constructor
  · exact fun hx j _ => hx j
  · intro hx j
    by_cases hj : j.val + 1 ≤ d
    · exact hx j hj
    · simp only [lowTaggedSubspaceFamily, dite_eq_right hj, Submodule.mem_top]

theorem lowTaggedSubspaceFamily_span {A : Type*} (d : ℕ)
    (g : A → Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (hg : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
      (Submodule.span ℝ (Set.range g)))
    (j : Fin m) (hj : j.val + 1 ≤ d) :
    lowTaggedSubspaceFamily J d (Submodule.span ℝ (Set.range g)) j =
      Submodule.span ℝ (Set.range (fun a k => g a (lowTaggedSlot J d j hj k))) := by
  rw [lowTaggedSubspaceFamily, dite_eq_left hj]
  exact lowTagged_comap_span_eq J d j hj g hg

end Erdos3.VectorPolynomial

end

end OAI

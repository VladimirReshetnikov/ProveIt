import OAI.Combinatorics.Progressions.Geometry.AllocatedOneCubeCoordinates

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))

noncomputable def allocatedNormalizedMixedSiteValue
    (w : ∀ j : Fin m, (I j → ℝ) × (Fin (n j) → ℤ)) : LayerSamplerAxis I n → ℝ
  | ⟨j, .inl i⟩ => if grid ⟨j, .inl i⟩ then 0 else (w j).1 i / R j
  | ⟨j, .inr i⟩ => if grid ⟨j, .inr i⟩ then 0 else ((w j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j

theorem allocatedIdealSiteCoordinates_mixed_value
    (z : ∀ j : Fin m, (I j → jets j → ℝ) × (Fin (n j) → jets j → ℤ))
    (s : Finset α) :
    allocatedIdealSiteCoordinates B U b S ((coefficientJetAxisSplit jets I n grid z).2) s =
      allocatedNormalizedMixedSiteValue B U b S (mixedBooleanSiteValue z s) := by
  funext a
  rcases a with ⟨j, i | i⟩
  · change realBoundedSiteReconstruction (j.val + 1)
      (fun r => if _h : ¬grid ⟨j, Sum.inl i⟩ then (z j).1 i r / R j else 0) s =
      (if grid ⟨j, Sum.inl i⟩ then 0 else (mixedBooleanSiteValue z s j).1 i / R j)
    by_cases hg : grid ⟨j, Sum.inl i⟩
    · simp only [hg, not_true_eq_false, dite_false, ite_true, realBoundedSiteReconstruction,
        zero_mul, Finset.sum_const_zero]
    · simp only [hg, not_false_eq_true, dite_true, ite_false,
        realBoundedSiteReconstruction_div, mixedBooleanSiteValue_real]
  · change realBoundedSiteReconstruction (j.val + 1)
      (fun r => if _h : ¬grid ⟨j, Sum.inr i⟩ then
        ((z j).2 i r : ℝ) / (basisAxisScale (b j) i : ℝ) / R j else 0) s =
      (if grid ⟨j, Sum.inr i⟩ then 0 else
        ((mixedBooleanSiteValue z s j).2 i : ℝ) / (basisAxisScale (b j) i : ℝ) / R j)
    by_cases hg : grid ⟨j, Sum.inr i⟩
    · simp only [hg, not_true_eq_false, dite_false, ite_true, realBoundedSiteReconstruction,
        zero_mul, Finset.sum_const_zero]
    · simp only [hg, not_false_eq_true, dite_true, ite_false,
        realBoundedSiteReconstruction_div, mixedBooleanSiteValue_integer]

end Erdos3.VectorPolynomial

end

end OAI

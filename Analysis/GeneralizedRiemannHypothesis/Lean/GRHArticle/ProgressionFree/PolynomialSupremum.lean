import GRHArticle.ProgressionFree.PolynomialBlockAttainment

/-!
# Attainment of the polynomial progression-free upper density

Choose progression-free sets with upper densities approaching the supremum,
then sample at sufficiently separated degree cutoffs. The loss from retaining
the top degree layers tends to zero.
-/

namespace GRHArticle.ProgressionFree

open Polynomial Filter Topology

/-- Separated degree blocks preserve the polynomial-ratio condition. -/
theorem polynomialRatioThreeGPFree_blockUnion {F : Type*} [Field F]
    {N : ℕ → ℕ} (hgap : ∀ ⦃i j⦄, i < j → 2 * N i + 2 * j < N j)
    {E : ℕ → Set (Polynomial F)} (hE : ∀ j, PolynomialRatioThreeGPFree (E j)) :
    PolynomialRatioThreeGPFree (polynomialBlockUnion N E) := by
  intro f r hf hr ⟨h₀, h₁, h₂⟩
  have hr₀ : r ≠ 0 := by rintro rfl; simp at hr
  let E₀ (j : ℕ) := E j \ {0}
  have hE₀ (j : ℕ) : (0 : Polynomial F) ∉ E₀ j := fun h ↦ h.2 rfl
  have hfree (j : ℕ) (g s : Polynomial F) (hs : 0 < s.natDegree) :
      ¬ (g ∈ E₀ j ∧ g * s ∈ E₀ j ∧ g * s * s ∈ E₀ j) := by
    rintro ⟨hg, hgs, hgss⟩
    exact hE j g s hg.2 hs ⟨hg.1, hgs.1, hgss.1⟩
  have hmem {g : Polynomial F} (hg : g ≠ 0) (h : g ∈ polynomialBlockUnion N E) :
      g ∈ polynomialBlockUnion N E₀ := by
    obtain ⟨j, hj, h₁, h₂⟩ := h
    exact ⟨j, ⟨hj, hg⟩, h₁, h₂⟩
  exact polynomialBlockUnion_no_ratio_progression hgap E₀ hE₀ hfree f r hr
    ⟨hmem hf h₀, hmem (mul_ne_zero hf hr₀) h₁, hmem (mul_ne_zero (mul_ne_zero hf hr₀) hr₀) h₂⟩

/-- One progression-free set attains `β_q` in upper degree-ball density. -/
theorem polynomialRatioDensitySupremum_attained (F : Type*) [Field F] [Fintype F] :
    ∃ E : Set (Polynomial F), 0 ∉ E ∧ PolynomialRatioThreeGPFree E ∧
      limsup (polynomialBallProportion E) atTop = polynomialRatioDensitySupremum F :=
  polynomialBlockDensitySupremum_attained PolynomialRatioThreeGPFree
    (by simp [PolynomialRatioThreeGPFree]) (by intro N hgap E hfree; exact polynomialRatioThreeGPFree_blockUnion hgap hfree)

end GRHArticle.ProgressionFree

import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped BigOperators

noncomputable def absorbedSiteTests {A S X : Type*} [Fintype A]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) : S → X → ℂ :=
  fun s x => (∏ a, χ a s x) * test s x

theorem absorbedSiteTests_norm {A S X : Type*} [Fintype A]
    (χ : A → S → X → ℂ) (hχ : ∀ a s x, ‖χ a s x‖ = 1)
    (test : S → X → ℂ) (s : S) (x : X) :
    ‖absorbedSiteTests χ test s x‖ = ‖test s x‖ := by
  simp only [absorbedSiteTests, norm_mul, norm_prod, hχ, Finset.prod_const_one, one_mul]

theorem absorbedSiteTests_product {A S X : Type*} [Fintype A] [Fintype S]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) (value : S → X) :
    (∏ a, ∏ s, χ a s (value s)) * (∏ s, test s (value s)) =
      ∏ s, absorbedSiteTests χ test s (value s) := by
  rw [Finset.prod_comm]
  exact (Finset.prod_mul_distrib).symm

theorem absorb_factored_phases {A S X G : Type*} [Fintype A] [Fintype S]
    (χ : A → S → X → ℂ) (test : S → X → ℂ) (value : G → S → X)
    (high : A → G → ℝ)
    (hfactor : ∀ a g, character (high a g : CircleFourier.Circle) = ∏ s, χ a s (value g s))
    (low : G → ℝ) (g : G) :
    character ((low g + ∑ a, high a g : ℝ) : CircleFourier.Circle) * (∏ s, test s (value g s)) =
      character (low g : CircleFourier.Circle) * (∏ s, absorbedSiteTests χ test s (value g s)) := by
  rw [AddCircle.coe_add, character_add, character_real_sum]
  simp_rw [hfactor]
  rw [mul_assoc, absorbedSiteTests_product]

end Erdos3

end

end OAI

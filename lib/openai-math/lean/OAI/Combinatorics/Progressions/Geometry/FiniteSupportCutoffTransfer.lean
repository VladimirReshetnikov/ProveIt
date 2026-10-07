/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CyclicCutNeighborhood
import OAI.Combinatorics.Progressions.Estimates.ImageExtensionInverseBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A H : Type*} [AddCommGroup A] [AddCommGroup H] [DecidableEq H]

theorem imageExtension_subset_indicator (φ : A →+ H) (P Q : Finset A)
    (hφ : Set.InjOn φ (P : Set A)) (hQP : Q ⊆ P) (f : A → ℂ) (y : H) :
    imageExtension φ Q f y = imageExtension φ P f y * finiteIndicator (Q.image φ) y := by
  classical
  by_cases hy : y ∈ Q.image φ
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [imageExtension_apply (hφ.mono hQP) f hx, imageExtension_apply hφ f (hQP hx)]
    simp only [finiteIndicator, ite_eq_left (Finset.mem_image.mpr ⟨x, hx, rfl⟩), mul_one]
  · rw [imageExtension_eq_zero f (by simpa using hy)]
    simp only [finiteIndicator, ite_eq_right hy, mul_zero]

variable [Fintype H]

theorem density_mul_finiteSupportGowersNorm_le (j : ℕ) (φ : A →+ H) (Q : Finset A)
    (hQ : Q.Nonempty) (hφ : ReflectsPairSums φ (Q : Set A)) (f : A → ℂ) :
    ((Q.card : ℝ) / Fintype.card H) * finiteSupportGowersNorm (j + 1) Q f ≤
      gowersNorm (j + 1) (imageExtension φ Q f) := by
  have hd := gowersNorm_restrict_one_pos j (hQ.image φ)
  have hden := norm_expect_le_gowersNorm j (restrictTo (Q.image φ) (fun _ => (1 : ℂ)))
  rw [norm_expect_restrict_one, Finset.card_image_of_injOn hφ.injOn] at hden
  rw [finiteSupportGowersNorm_eq_restricted hφ j, restrictedGowersNorm,
    restrictTo_imageExtension]
  calc
    _ ≤ gowersNorm (j + 1) (restrictTo (Q.image φ) (fun _ => (1 : ℂ))) *
        (gowersNorm (j + 1) (imageExtension φ Q f) /
          gowersNorm (j + 1) (restrictTo (Q.image φ) (fun _ => (1 : ℂ)))) :=
      mul_le_mul_of_nonneg_right hden (div_nonneg (gowersNorm_nonneg j _) hd.le)
    _ = _ := mul_div_cancel₀ _ hd.ne'

theorem gowersNorm_imageExtension_le_finiteSupport (j : ℕ) (φ : A →+ H) (Q : Finset A)
    (hQ : Q.Nonempty) (hφ : ReflectsPairSums φ (Q : Set A)) (f : A → ℂ) :
    gowersNorm (j + 1) (imageExtension φ Q f) ≤ finiteSupportGowersNorm (j + 1) Q f := by
  have hd := gowersNorm_restrict_one_pos j (hQ.image φ)
  have hden : gowersNorm (j + 1) (restrictTo (Q.image φ) (fun _ => (1 : ℂ))) ≤ 1 :=
    gowersNorm_le_one j _ (by intro x; simp [restrictTo]; split_ifs <;> norm_num)
  rw [finiteSupportGowersNorm_eq_restricted hφ j, restrictedGowersNorm,
    restrictTo_imageExtension]
  exact (le_div_iff₀ hd).mpr (mul_le_of_le_one_right (gowersNorm_nonneg j _) hden)

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (N : I → ℕ) [∀ i, NeZero (N i)]

theorem finiteSupport_product_fiber_transfer
    {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]
    (j : ℕ) (φ : A →+ (∀ i, ZMod (N i))) (P Q : Finset A)
    (hQ : Q.Nonempty) (hQP : Q ⊆ P) (hφ : ReflectsPairSums φ (P : Set A))
    (ρ : (∀ i, ZMod (N i)) →+ K) (r : K)
    (a : ∀ i, ZMod (N i)) (L : I → ℕ)
    (himage : ∀ y, y ∈ Q.image φ ↔
      y ∈ cyclicProductBox N a L ∧ ρ y = r)
    (f : A → ℂ) (hf : ∀ x ∈ P, ‖f x‖ ≤ 1)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hlarge : η ≤ ((Q.card : ℝ) / Fintype.card (∀ i, ZMod (N i))) *
      finiteSupportGowersNorm (j + 2) Q f) :
    (η / 2) ^ (2 ^ (j + 2) * Fintype.card I + 1) /
      (4 * (Fintype.card I + 1)) ^ Fintype.card I ≤ finiteSupportGowersNorm (j + 2) P f := by
  let g := imageExtension φ P f
  have hg (y) : ‖g y‖ ≤ 1 := imageExtension_norm_le_one φ P f hφ.injOn hf y
  have hmask (y) : imageExtension φ Q f y =
      (g y * finiteIndicator {r} (ρ y)) * finiteIndicator (cyclicProductBox N a L) y := by
    rw [imageExtension_subset_indicator φ P Q hφ.injOn hQP f]
    by_cases hb : y ∈ cyclicProductBox N a L <;> by_cases hr : ρ y = r <;>
      simp [finiteIndicator, himage, hb, hr, g]
  have hcut : η ≤ gowersNorm (j + 2) (fun y =>
      (g y * finiteIndicator {r} (ρ y)) * finiteIndicator (cyclicProductBox N a L) y) := by
    have hlocal := hlarge.trans
      (density_mul_finiteSupportGowersNorm_le (j + 1) φ Q hQ (hφ.mono hQP) f)
    rw [funext hmask] at hlocal
    exact hlocal
  have hgf (y) : ‖g y * finiteIndicator {r} (ρ y)‖ ≤ 1 := by
    simpa only [norm_mul, one_mul] using mul_le_mul (hg y)
      (finiteIndicator_norm_le_one {r} (ρ y)) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  exact (gowersNorm_transfer_cyclicProductBox N j _ hgf a L hη hη1 hcut).trans
    ((gowersNorm_mul_fiber j ρ r g).trans
      (gowersNorm_imageExtension_le_finiteSupport (j + 1) φ P (hQ.mono hQP) hφ f))

end Erdos3

end

end OAI

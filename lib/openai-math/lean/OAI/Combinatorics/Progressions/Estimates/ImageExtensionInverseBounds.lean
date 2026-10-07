import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Fintype B] [DecidableEq B]

omit [Fintype B] in
theorem imageExtension_norm_le_one (φ : A →+ B) (Q : Finset A) (f : A → ℂ)
    (hφ : Set.InjOn φ (Q : Set A)) (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (y : B) :
    ‖imageExtension φ Q f y‖ ≤ 1 := by
  classical
  by_cases hy : y ∈ Q.image φ
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    rw [imageExtension_apply hφ f hx]
    exact hf x hx
  · rw [imageExtension_eq_zero f (by
      rintro ⟨x, hx, hxy⟩
      exact hy (Finset.mem_image.mpr ⟨x, hx, hxy⟩))]
    simp

theorem sum_imageExtension_mul (φ : A →+ B) (Q : Finset A) (f : A → ℂ) (g : B → ℂ) :
    (∑ y : B, imageExtension φ Q f y * g y) = ∑ x ∈ Q, f x * g (φ x) := by
  classical
  simp only [imageExtension, Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

theorem expect_imageExtension_mul (φ : A →+ B) (Q : Finset A) (hQ : Q.Nonempty)
    (f : A → ℂ) (g : B → ℂ) :
    (𝔼 y : B, imageExtension φ Q f y * g y) =
      ((Q.card : ℂ) / Fintype.card B) * (𝔼 x ∈ Q, f x * g (φ x)) := by
  classical
  rw [Fintype.expect_eq_sum_div_card, sum_imageExtension_mul, Finset.expect_eq_sum_div_card]
  have hq : (Q.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hQ.card_pos.ne'
  field_simp

theorem norm_expect_imageExtension_mul_le (φ : A →+ B) (Q : Finset A) (hQ : Q.Nonempty)
    (hφ : Set.InjOn φ (Q : Set A)) (f : A → ℂ) (g : B → ℂ) :
    ‖𝔼 y : B, imageExtension φ Q f y * g y‖ ≤ ‖𝔼 x ∈ Q, f x * g (φ x)‖ := by
  classical
  rw [expect_imageExtension_mul φ Q hQ, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  have hc : Q.card ≤ Fintype.card B := by
    have h := (Q.image φ).card_le_univ
    rwa [Finset.card_image_of_injOn hφ] at h
  have hratio : (Q.card : ℝ) / Fintype.card B ≤ 1 :=
    (div_le_one (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card B)).mpr (by exact_mod_cast hc)
  exact mul_le_of_le_one_left (norm_nonneg _) hratio

theorem exp_le_gowers_imageExtension (j : ℕ) (φ : A →+ B) (Q : Finset A)
    (hφ : ReflectsPairSums φ (Q : Set A)) (f : A → ℂ) {p q : ℝ}
    (hQ : Real.exp (-q) ≤ (Q.card : ℝ) / Fintype.card B)
    (hf : Real.exp (-p) ≤ finiteSupportGowersNorm (j + 1) Q f) :
    Real.exp (-(p + q)) ≤ gowersNorm (j + 1) (imageExtension φ Q f) := by
  classical
  have hm := norm_expect_le_gowersNorm j (restrictTo (Q.image φ) (fun _ => (1 : ℂ)))
  rw [norm_expect_restrict_one, Finset.card_image_of_injOn hφ.injOn] at hm
  have hd := hQ.trans hm
  have hdpos := lt_of_lt_of_le (Real.exp_pos (-q)) hd
  rw [finiteSupportGowersNorm_eq_restricted hφ, restrictedGowersNorm, restrictTo_imageExtension] at hf
  have hprod := (le_div_iff₀ hdpos).mp hf
  calc
    _ = Real.exp (-p) * Real.exp (-q) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-p) * gowersNorm (j + 1) (restrictTo (Q.image φ) (fun _ => (1 : ℂ))) :=
      mul_le_mul_of_nonneg_left hd (Real.exp_nonneg _)
    _ ≤ _ := hprod

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Probability.PivotDensitySupport

namespace OAI

section

namespace Erdos3

theorem normalizedFiberDensity_normalized_congr {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S₁ S₂ P₁ P₂ : I → ℝ) (T₁ T₂ : J → ℝ)
    (hS₁ : ∀ i, 0 < S₁ i) (hS₂ : ∀ i, 0 < S₂ i)
    (hP₁ : ∀ i, 0 < P₁ i) (hP₂ : ∀ i, 0 < P₂ i)
    (hp : normalizedIntegerPivot A S₁ P₁ = normalizedIntegerPivot A S₂ P₂)
    (hb : normalizedIntegerColumns B T₁ P₁ = normalizedIntegerColumns B T₂ P₂)
    (f : (J → ℝ) × (I → ℝ) → ℝ) :
    normalizedFiberDensity A hA B S₁ P₁ T₁ hS₁ hP₁ f =
      normalizedFiberDensity A hA B S₂ P₂ T₂ hS₂ hP₂ f := by
  have he : normalizedPivotEquiv A hA S₁ P₁ hS₁ hP₁ = normalizedPivotEquiv A hA S₂ P₂ hS₂ hP₂ := by
    ext v i
    change ((normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap v) i =
      ((normalizedPivotEquiv _ _ _ _ _ _).toContinuousLinearMap v) i
    rw [normalizedPivotEquiv_coe, normalizedPivotEquiv_coe, hp]
  unfold normalizedFiberDensity
  rw [he, hb]

theorem normalizedFiberDensity_common_scale {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S₁ S₂ P₁ P₂ : I → ℝ) (T₁ T₂ : J → ℝ)
    (hS₁ : ∀ i, 0 < S₁ i) (hS₂ : ∀ i, 0 < S₂ i)
    (hP₁ : ∀ i, 0 < P₁ i) (hP₂ : ∀ i, 0 < P₂ i)
    {c : ℝ} (hc : c ≠ 0) (hs : ∀ i, S₁ i = c * S₂ i)
    (hp : ∀ i, P₁ i = c * P₂ i) (ht : ∀ j, T₁ j = c * T₂ j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) :
    normalizedFiberDensity A hA B S₁ P₁ T₁ hS₁ hP₁ f =
      normalizedFiberDensity A hA B S₂ P₂ T₂ hS₂ hP₂ f := by
  apply normalizedFiberDensity_normalized_congr A hA B S₁ S₂ P₁ P₂ T₁ T₂ hS₁ hS₂ hP₁ hP₂
  · ext i j
    rw [normalizedIntegerPivot_entry, normalizedIntegerPivot_entry, hs, hp]
    field_simp [hc, (hP₂ i).ne']
  · ext i j
    rw [normalizedIntegerColumns_entry_div, normalizedIntegerColumns_entry_div, ht, hp]
    field_simp [hc, (hP₂ i).ne']

end Erdos3

end

end OAI

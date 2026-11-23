import GlobeFlattening.LongitudeProfile

/-!
# Joining longitude profiles across latitude layers
-/

open scoped BigOperators

namespace GlobeFlattening

noncomputable section

abbrev latitudeWeight := rampWeight

theorem latitudeWeight_eq_zero {start width y : ℝ} (hy : y ≤ start) :
    latitudeWeight start width y = 0 := rampWeight_eq_zero hy

theorem latitudeWeight_eq_one {start width y : ℝ} (hw : 0 < width) (hy : start + width ≤ y) :
    latitudeWeight start width y = 1 := rampWeight_eq_one hw hy

theorem latitudeWeight_bounds {start width y : ℝ} (hw : 0 < width) :
    0 ≤ latitudeWeight start width y ∧ latitudeWeight start width y ≤ 1 := rampWeight_bounds hw

/-- Add the change from one row to the next with its latitude weight. Only
one weight is nonconstant at any latitude when the layers are disjoint. -/
def latitudeProfile (starts : ℕ → ℝ) (width : ℝ) (count : ℕ)
    (row : ℕ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  rampProfile count (fun j => row j p.1) (fun j => latitudeWeight (starts j) width p.2)

theorem continuous_latitudeProfile (starts : ℕ → ℝ) (width : ℝ) (count : ℕ)
    {row : ℕ → ℝ → ℝ} (hrow : ∀ j, Continuous (row j)) :
    Continuous (latitudeProfile starts width count row) := by
  unfold latitudeProfile rampProfile
  refine ((hrow 0).comp continuous_fst).add (continuous_finsetSum _ fun j _ => ?_)
  have hweight : Continuous (fun p : ℝ × ℝ => latitudeWeight (starts j) width p.2) := by
    unfold latitudeWeight rampWeight clippedRamp
    fun_prop
  exact hweight.mul (((hrow (j + 1)).comp continuous_fst).sub ((hrow j).comp continuous_fst))

/-- Sums telescope when all previous layers are complete and all later
layers have not started. This includes the first and last latitude cores. -/
theorem latitudeProfile_at_core {starts : ℕ → ℝ} {width : ℝ} {count j : ℕ}
    {row : ℕ → ℝ → ℝ} {p : ℝ × ℝ}
    (hw : 0 < width) (hj : j ≤ count)
    (hbefore : ∀ i < j, starts i + width ≤ p.2)
    (hafter : ∀ i < count, j ≤ i → p.2 ≤ starts i) :
    latitudeProfile starts width count row p = row j p.1 :=
  rampProfile_at_core hj (fun i hi => latitudeWeight_eq_one hw (hbefore i hi))
    (fun i hi hji => latitudeWeight_eq_zero (hafter i hi hji))

/-- Between cores, the complete profile is the interpolation of the two
neighboring rows. This applies at the boundary of the layer as well. -/
theorem latitudeProfile_at_layer {starts : ℕ → ℝ} {width : ℝ} {count j : ℕ}
    {row : ℕ → ℝ → ℝ} {p : ℝ × ℝ}
    (hw : 0 < width) (hj : j < count)
    (hbefore : ∀ i < j, starts i + width ≤ p.2)
    (hafter : ∀ i < count, j < i → p.2 ≤ starts i) :
    latitudeProfile starts width count row p =
      (1 - latitudeWeight (starts j) width p.2) * row j p.1 +
        latitudeWeight (starts j) width p.2 * row (j + 1) p.1 := by
  unfold latitudeProfile
  rw [rampProfile_at_layer hj (fun i hi => latitudeWeight_eq_one hw (hbefore i hi))
    (fun i hi hji => latitudeWeight_eq_zero (hafter i hi hji))]
  ring

/-- The convex combination used in an interpolation layer preserves a
common lower slope between any pair of longitudes. -/
theorem latitude_blend_lower_slope {t slope x₁ x₂ a₁ a₂ b₁ b₂ : ℝ}
    (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : slope * (x₂ - x₁) ≤ a₂ - a₁)
    (hb : slope * (x₂ - x₁) ≤ b₂ - b₁) :
    slope * (x₂ - x₁) ≤ ((1 - t) * a₂ + t * b₂) - ((1 - t) * a₁ + t * b₁) := by
  have h₁ := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht₁)
  have h₂ := mul_le_mul_of_nonneg_left hb ht₀
  linarith

/-- The interpolation cannot increase a common bound on the two row errors
relative to the old value at the point. -/
theorem latitude_blend_error {t a b old bound : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : |a - old| ≤ bound) (hb : |b - old| ≤ bound) :
    |(1 - t) * a + t * b - old| ≤ bound := by
  have ht : 0 ≤ 1 - t := sub_nonneg.mpr ht₁
  have haa := abs_le.mp ha
  have hbb := abs_le.mp hb
  exact abs_le.mpr
    ⟨by linarith [mul_le_mul_of_nonneg_left haa.1 ht, mul_le_mul_of_nonneg_left hbb.1 ht₀],
     by linarith [mul_le_mul_of_nonneg_left haa.2 ht, mul_le_mul_of_nonneg_left hbb.2 ht₀]⟩

end

end GlobeFlattening

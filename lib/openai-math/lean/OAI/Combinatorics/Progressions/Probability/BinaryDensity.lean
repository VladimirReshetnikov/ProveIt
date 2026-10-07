import Mathlib

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def binaryDensity {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (p : X × Y) : ℝ :=
  f p.1 * g p.2

theorem binaryDensity_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (binaryDensity f g) := (hf.comp measurable_fst).mul (hg.comp measurable_snd)

theorem binaryDensity_integrable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite ν] {f : X → ℝ} {g : Y → ℝ}
    (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (binaryDensity f g) (μ.prod ν) := hf.mul_prod hg

theorem binaryDensity_mass {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (f : X → ℝ) (g : Y → ℝ) :
    (∫ p, binaryDensity f g p ∂μ.prod ν) = (∫ x, f x ∂μ) * ∫ y, g y ∂ν := integral_prod_mul f g

theorem binaryDensity_cap {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (C D : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D) (p : X × Y) :
    binaryDensity f g p ∈ Set.Icc (0 : ℝ) (C * D) :=
  ⟨mul_nonneg (hf _).1 (hg _).1, mul_le_mul (hf _).2 (hg _).2 (hg _).1 C.coe_nonneg⟩

theorem binaryDensity_lipschitz {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → ℝ) (g : Y → ℝ) (C D L M : ℝ≥0)
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) C) (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) D)
    (hL : LipschitzWith L f) (hM : LipschitzWith M g) :
    LipschitzWith (D * L + C * M) (binaryDensity f g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hdx : dist x.1 y.1 ≤ dist x y := le_max_left _ _
  have hdy : dist x.2 y.2 ≤ dist x y := le_max_right _ _
  have hleft : |f x.1 - f y.1| ≤ (L : ℝ) * dist x y := by
    have h := hL.dist_le_mul x.1 y.1
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdx L.coe_nonneg)
  have hright : |g x.2 - g y.2| ≤ (M : ℝ) * dist x y := by
    have h := hM.dist_le_mul x.2 y.2
    rw [Real.dist_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdy M.coe_nonneg)
  rw [Real.dist_eq]
  change |f x.1 * g x.2 - f y.1 * g y.2| ≤ _
  calc
    |f x.1 * g x.2 - f y.1 * g y.2| =
        |(f x.1 - f y.1) * g x.2 + f y.1 * (g x.2 - g y.2)| := by congr 1; ring
    _ ≤ |(f x.1 - f y.1) * g x.2| + |f y.1 * (g x.2 - g y.2)| := abs_add_le _ _
    _ = |f x.1 - f y.1| * g x.2 + f y.1 * |g x.2 - g y.2| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (hg _).1, abs_of_nonneg (hf _).1]
    _ ≤ ((L : ℝ) * dist x y) * D + C * ((M : ℝ) * dist x y) :=
      add_le_add (mul_le_mul hleft (hg _).2 (hg _).1 (mul_nonneg L.coe_nonneg dist_nonneg))
        (mul_le_mul (hf _).2 hright (abs_nonneg _) C.coe_nonneg)
    _ = (D * L + C * M : ℝ≥0) * dist x y := by push_cast; ring

theorem binaryDensity_test_product {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f φ : X → ℝ) (g ψ : Y → ℝ) :
    (∫ p, binaryDensity f g p * (φ p.1 * ψ p.2) ∂μ.prod ν) =
      (∫ x, f x * φ x ∂μ) * ∫ y, g y * ψ y ∂ν := by
  calc
    (∫ p, binaryDensity f g p * (φ p.1 * ψ p.2) ∂μ.prod ν) =
        ∫ p, (f p.1 * φ p.1) * (g p.2 * ψ p.2) ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold binaryDensity
      ring
    _ = _ := integral_prod_mul (fun x => f x * φ x) (fun y => g y * ψ y)

end Erdos3

end

end OAI

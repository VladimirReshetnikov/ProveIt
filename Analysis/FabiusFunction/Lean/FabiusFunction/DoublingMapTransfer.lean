import FabiusFunction.ClausenCorollaries
import Mathlib.MeasureTheory.Function.Floor

/-!
# The doubling map mod one and its transfer identity

The doubling map `T t = 2t mod 1` as `Int.fract (2t)`, connected to
the branchwise transfer identity of `DoublingTransferAdjoint`: for
integrable data,

`∫₀¹ f·(g ∘ T) = ∫₀¹ 𝒫f·g`,  `𝒫f = (f(·/2) + f((·+1)/2))/2`.

This puts the audits' circle dynamics on the interval without a
quotient: `T` agrees with the two affine branches off the two points
`{1/2, 1}`, so all branchwise identities transport along almost-
everywhere congruence.

* `doublingMap`, `doublingMap_eq_left/right`, `measurable_doublingMap`.
* `intervalIntegrable_comp_doublingMap_left/right` — integrability of
  composites on the two half-intervals.
* `integral_mul_comp_doublingMap` — **the transfer identity for `T`**.
* `integral_comp_doublingMap` — `T` preserves Lebesgue measure on
  `[0,1]` (the case `f = 𝟙`).
-/

set_option autoImplicit false

open Filter Topology intervalIntegral Real MeasureTheory Set

namespace Fabius

/-- The doubling map mod one. -/
noncomputable def doublingMap (t : ℝ) : ℝ := Int.fract (2 * t)

/-- The doubling map takes only nonnegative values. -/
theorem doublingMap_nonneg (t : ℝ) : 0 ≤ doublingMap t :=
  Int.fract_nonneg _

/-- Every value of the doubling map is strictly less than one. -/
theorem doublingMap_lt_one (t : ℝ) : doublingMap t < 1 :=
  Int.fract_lt_one _

/-- On `[0, 1/2)`, the doubling map is the affine branch `t ↦ 2 * t`. -/
theorem doublingMap_eq_left {t : ℝ} (h0 : 0 ≤ t) (h1 : t < 1 / 2) :
    doublingMap t = 2 * t :=
  Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- On `[1/2, 1)`, the doubling map is the affine branch `t ↦ 2 * t - 1`. -/
theorem doublingMap_eq_right {t : ℝ} (h0 : 1 / 2 ≤ t) (h1 : t < 1) :
    doublingMap t = 2 * t - 1 := by
  have h := Int.fract_sub_one (2 * t)
  rw [doublingMap, ← h]
  exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩

/-- The doubling map is Borel measurable. -/
theorem measurable_doublingMap : Measurable doublingMap :=
  (measurable_const_mul 2).fract

/-- Composites with `T` are integrable on the left half. -/
theorem intervalIntegrable_mul_comp_doublingMap_left {f g : ℝ → ℝ}
    (hint1 : IntervalIntegrable (fun u => f (u / 2) * g u)
      MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun t => f t * g (doublingMap t))
      MeasureTheory.volume 0 (1 / 2) := by
  have hA : IntervalIntegrable (fun t => f t * g (2 * t))
      MeasureTheory.volume 0 (1 / 2) := by
    have h : IntervalIntegrable
        (fun x : ℝ => f (2 * x / 2) * g (2 * x))
        MeasureTheory.volume (0 / 2) (1 / 2) :=
      hint1.comp_mul_left (c := 2)
    have heq : (fun x : ℝ => f (2 * x / 2) * g (2 * x)) =
        fun t => f t * g (2 * t) := by
      funext x
      rw [show (2:ℝ) * x / 2 = x by ring]
    rw [heq] at h
    convert h using 2
    norm_num
  rw [intervalIntegrable_iff] at hA ⊢
  apply hA.congr
  have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [MeasureTheory.ae_restrict_of_ae hhalf,
    MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht hmem
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2)] at hmem
  have hlt : t < 1 / 2 := lt_of_le_of_ne hmem.2 ht
  rw [doublingMap_eq_left hmem.1.le hlt]

/-- Composites with `T` are integrable on the right half. -/
theorem intervalIntegrable_mul_comp_doublingMap_right {f g : ℝ → ℝ}
    (hint2 : IntervalIntegrable (fun u => f ((u + 1) / 2) * g u)
      MeasureTheory.volume 0 1) :
    IntervalIntegrable (fun t => f t * g (doublingMap t))
      MeasureTheory.volume (1 / 2) 1 := by
  have hB : IntervalIntegrable (fun t => f t * g (2 * t - 1))
      MeasureTheory.volume (1 / 2) 1 := by
    have h1 : IntervalIntegrable
        (fun x : ℝ => f ((x - 1 + 1) / 2) * g (x - 1))
        MeasureTheory.volume (0 + 1) (1 + 1) := hint2.comp_sub_right 1
    have h2 : IntervalIntegrable
        (fun t : ℝ => f ((2 * t - 1 + 1) / 2) * g (2 * t - 1))
        MeasureTheory.volume ((0 + 1) / 2) ((1 + 1) / 2) :=
      h1.comp_mul_left (c := 2)
    have heq : (fun t : ℝ => f ((2 * t - 1 + 1) / 2) * g (2 * t - 1)) =
        fun t => f t * g (2 * t - 1) := by
      funext t
      rw [show ((2:ℝ) * t - 1 + 1) / 2 = t by ring]
    rw [heq] at h2
    convert h2 using 2 <;> norm_num
  rw [intervalIntegrable_iff] at hB ⊢
  apply hB.congr
  have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [MeasureTheory.ae_restrict_of_ae h1ae,
    MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t ht hmem
  rw [Set.uIoc_of_le (by norm_num : (1:ℝ) / 2 ≤ 1)] at hmem
  have hlt : t < 1 := lt_of_le_of_ne hmem.2 ht
  rw [doublingMap_eq_right hmem.1.le hlt]

/-- **The transfer identity for the doubling map**:
`∫₀¹ f·(g∘T) = ∫₀¹ 𝒫f·g` whenever the two branch products are
integrable. -/
theorem integral_mul_comp_doublingMap (f g : ℝ → ℝ)
    (hint1 : IntervalIntegrable (fun u => f (u / 2) * g u)
      MeasureTheory.volume 0 1)
    (hint2 : IntervalIntegrable (fun u => f ((u + 1) / 2) * g u)
      MeasureTheory.volume 0 1) :
    ∫ t in (0:ℝ)..1, f t * g (doublingMap t) =
      ∫ t in (0:ℝ)..1, (f (t / 2) + f ((t + 1) / 2)) / 2 * g t := by
  have hTA := intervalIntegrable_mul_comp_doublingMap_left hint1
  have hTB := intervalIntegrable_mul_comp_doublingMap_right hint2
  have hsplit : ∫ t in (0:ℝ)..1, f t * g (doublingMap t) =
      (∫ t in (0:ℝ)..(1/2:ℝ), f t * g (doublingMap t)) +
        ∫ t in (1/2:ℝ)..1, f t * g (doublingMap t) :=
    (intervalIntegral.integral_add_adjacent_intervals hTA hTB).symm
  have hcongrA : ∫ t in (0:ℝ)..(1/2:ℝ), f t * g (doublingMap t) =
      ∫ t in (0:ℝ)..(1/2:ℝ), f t * g (2 * t) := by
    apply intervalIntegral.integral_congr_ae
    have hhalf : ∀ᵐ t : ℝ, t ≠ (1 / 2 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [hhalf] with t ht hmem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1 / 2)] at hmem
    have hlt : t < 1 / 2 := lt_of_le_of_ne hmem.2 ht
    rw [doublingMap_eq_left hmem.1.le hlt]
  have hcongrB : ∫ t in (1/2:ℝ)..1, f t * g (doublingMap t) =
      ∫ t in (1/2:ℝ)..1, f t * g (2 * t - 1) := by
    apply intervalIntegral.integral_congr_ae
    have h1ae : ∀ᵐ t : ℝ, t ≠ (1 : ℝ) := by
      rw [MeasureTheory.ae_iff]
      simp
    filter_upwards [h1ae] with t ht hmem
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) / 2 ≤ 1)] at hmem
    have hlt : t < 1 := lt_of_le_of_ne hmem.2 ht
    rw [doublingMap_eq_right hmem.1.le hlt]
  rw [hsplit, hcongrA, hcongrB]
  exact integral_mul_comp_doubling' f g hint1 hint2

/-- **The doubling map preserves Lebesgue measure on `[0,1]`**: the
case `f = 𝟙` of the transfer identity. -/
theorem integral_comp_doublingMap (g : ℝ → ℝ)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1) :
    ∫ t in (0:ℝ)..1, g (doublingMap t) = ∫ t in (0:ℝ)..1, g t := by
  have h1 : IntervalIntegrable
      (fun u => (fun _ : ℝ => (1:ℝ)) (u / 2) * g u)
      MeasureTheory.volume 0 1 := by
    simpa using hg
  have h2 : IntervalIntegrable
      (fun u => (fun _ : ℝ => (1:ℝ)) ((u + 1) / 2) * g u)
      MeasureTheory.volume 0 1 := by
    simpa using hg
  have h := integral_mul_comp_doublingMap (fun _ => 1) g h1 h2
  calc ∫ t in (0:ℝ)..1, g (doublingMap t)
      = ∫ t in (0:ℝ)..1, (fun _ : ℝ => (1:ℝ)) t * g (doublingMap t) := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp
    _ = ∫ t in (0:ℝ)..1,
        ((fun _ : ℝ => (1:ℝ)) (t / 2) +
          (fun _ : ℝ => (1:ℝ)) ((t + 1) / 2)) / 2 * g t := h
    _ = ∫ t in (0:ℝ)..1, g t := by
        refine intervalIntegral.integral_congr fun t _ => ?_
        norm_num

end Fabius

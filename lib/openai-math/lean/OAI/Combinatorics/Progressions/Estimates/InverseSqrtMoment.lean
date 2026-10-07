import OAI.Combinatorics.Progressions.Geometry.BoxWindowAveraging

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem inverse_max_le_inverse_sqrt_product {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (max a b)⁻¹ ≤ (Real.sqrt a)⁻¹ * (Real.sqrt b)⁻¹ := by
  have hs : 0 < Real.sqrt a * Real.sqrt b := mul_pos (Real.sqrt_pos.mpr ha) (Real.sqrt_pos.mpr hb)
  rw [← mul_inv]
  apply (inv_le_inv₀ (lt_max_of_lt_left ha) hs).mpr
  have hm : 0 ≤ max a b := (lt_max_of_lt_left ha).le
  have hab : a * b ≤ (max a b) ^ 2 := by
    nlinarith [mul_le_mul (le_max_left a b) (le_max_right a b) hb.le hm]
  have heq : (Real.sqrt a * Real.sqrt b) ^ 2 = a * b := by
    rw [mul_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hb.le]
  nlinarith

noncomputable def unitInverseSqrt (x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun x => (Real.sqrt x)⁻¹) x

theorem unitInverseSqrt_eq_rpow : unitInverseSqrt =
    (Set.Ioc (0 : ℝ) 1).indicator (fun x => x ^ (-1 / 2 : ℝ)) := by
  funext x
  by_cases hx : x ∈ Set.Ioc (0 : ℝ) 1
  · simp only [unitInverseSqrt, Set.indicator_of_mem hx]
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.1.le, ← Real.sqrt_eq_rpow]
  · simp only [unitInverseSqrt, Set.indicator_of_notMem hx]

theorem unitInverseSqrt_nonneg (x : ℝ) : 0 ≤ unitInverseSqrt x :=
  Set.indicator_nonneg (fun _ _ => inv_nonneg.mpr (Real.sqrt_nonneg _)) x

theorem unitInverseSqrt_integrable : Integrable unitInverseSqrt := by
  rw [unitInverseSqrt_eq_rpow]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1)
      (by norm_num : (-1 : ℝ) < -1 / 2)).1

theorem unitInverseSqrt_mass : (∫ x, unitInverseSqrt x) = 2 := by
  rw [unitInverseSqrt_eq_rpow, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1 / 2))]
  norm_num

variable {ι : Type*} [Fintype ι]

noncomputable def unitBoxInverseSqrt (x : ι → ℝ) : ℝ := ∏ i, unitInverseSqrt (x i)

theorem unitBoxInverseSqrt_integrable : Integrable (unitBoxInverseSqrt (ι := ι)) :=
  Integrable.fintype_prod (fun _ => unitInverseSqrt_integrable)

theorem unitBoxInverseSqrt_mass : (∫ x : ι → ℝ, unitBoxInverseSqrt x) = 2 ^ Fintype.card ι := by
  unfold unitBoxInverseSqrt
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [unitInverseSqrt_mass, Finset.prod_const, Finset.card_univ]

theorem unitBoxInverseSqrt_eq (x : ι → ℝ) (hx : ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1) :
    unitBoxInverseSqrt x = (Real.sqrt (∏ i, x i))⁻¹ := by
  unfold unitBoxInverseSqrt
  simp only [unitInverseSqrt, Set.indicator_of_mem (hx _)]
  rw [Finset.prod_inv_distrib, Real.sqrt_prod _ (fun i _ => (hx i).1.le)]

end Erdos3

end

end OAI

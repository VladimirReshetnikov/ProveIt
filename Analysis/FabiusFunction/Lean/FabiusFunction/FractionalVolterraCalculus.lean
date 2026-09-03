import FabiusFunction.FractionalVolterra
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Affine covariance and order raising for fractional Volterra operators

This module adds two reusable pieces of positive-real fractional calculus to
`fractionalVolterra`.

* Positive affine changes of variables scale an order-`alpha` operator by
  `c ^ alpha`.
* Integration by parts raises the order of a derivative, with the exact
  Gamma-normalized boundary term.

The order-raising theorem deliberately assumes less than `C^1`: the original
function need only be continuous on the closed interval, its displayed
derivative need only exist in the interior, and that derivative need only be
interval integrable.  Degenerate ordered intervals are included.
-/

open scoped Interval Real
open MeasureTheory Set

namespace Fabius

set_option autoImplicit false

/-- Fractional Volterra operators are covariant under an increasing affine
change of variables.  The order is arbitrary because this is an algebraic
change-of-variables identity; the ordered endpoint makes every kernel base
nonnegative.  No regularity, integrability, or completeness assumption is
needed. -/
theorem fractionalVolterra_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha a x c d : ℝ) (f : ℝ → E) (hc : 0 < c) (hax : a ≤ x) :
    fractionalVolterra alpha (c * a + d) f (c * x + d) =
      (c ^ alpha) •
        fractionalVolterra alpha a (fun t => f (c * t + d)) x := by
  rw [fractionalVolterra, fractionalVolterra,
    ← intervalIntegral.smul_integral_comp_mul_add
      (fun u =>
        ((((c * x + d) - u) ^ (alpha - 1)) / Real.Gamma alpha) • f u)
      c d]
  have hcpow : c * c ^ (alpha - 1) = c ^ alpha := by
    calc
      c * c ^ (alpha - 1) = c ^ (1 : ℝ) * c ^ (alpha - 1) := by
        rw [Real.rpow_one]
      _ = c ^ ((1 : ℝ) + (alpha - 1)) :=
        (Real.rpow_add hc 1 (alpha - 1)).symm
      _ = c ^ alpha := by ring_nf
  calc
    c • ∫ t in a..x,
          ((((c * x + d) - (c * t + d)) ^ (alpha - 1)) /
              Real.Gamma alpha) • f (c * t + d) =
        c • ∫ t in a..x,
          (c ^ (alpha - 1)) •
            ((((x - t) ^ (alpha - 1)) / Real.Gamma alpha) •
              f (c * t + d)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hax] at ht
      change
        ((((c * x + d) - (c * t + d)) ^ (alpha - 1)) /
            Real.Gamma alpha) • f (c * t + d) =
          (c ^ (alpha - 1)) •
            ((((x - t) ^ (alpha - 1)) / Real.Gamma alpha) •
              f (c * t + d))
      rw [smul_smul]
      congr 1
      rw [show c * x + d - (c * t + d) = c * (x - t) by ring,
        Real.mul_rpow hc.le (sub_nonneg.mpr ht.2)]
      ring
    _ = c • ((c ^ (alpha - 1)) •
        ∫ t in a..x,
          (((x - t) ^ (alpha - 1)) / Real.Gamma alpha) •
            f (c * t + d)) := by
      rw [intervalIntegral.integral_smul]
    _ = (c ^ alpha) •
        ∫ t in a..x,
          (((x - t) ^ (alpha - 1)) / Real.Gamma alpha) •
            f (c * t + d) := by
      rw [smul_smul, hcpow]

/-- Inverse-smul form of positive affine covariance. -/
theorem fractionalVolterra_comp_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (alpha a x c d : ℝ) (f : ℝ → E) (hc : 0 < c) (hax : a ≤ x) :
    fractionalVolterra alpha a (fun t => f (c * t + d)) x =
      (c ^ alpha)⁻¹ •
        fractionalVolterra alpha (c * a + d) f (c * x + d) := by
  rw [fractionalVolterra_affine alpha a x c d f hc hax]
  simp [smul_smul, (Real.rpow_pos_of_pos hc alpha).ne']

/-- Gamma-normalized fractional integration by parts.  If `g'` is an
interval-integrable interior derivative of a continuous Banach-valued
function `g`, then applying order `alpha + 1` to `g'` equals applying order
`alpha` to `g`, up to the exact left-endpoint boundary term. -/
theorem fractionalVolterra_add_one_deriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {alpha a x : ℝ} (halpha : 0 < alpha) (hax : a ≤ x)
    {g g' : ℝ → E} (hg : ContinuousOn g (Icc a x))
    (hderiv : ∀ t ∈ Ioo a x, HasDerivWithinAt g (g' t) (Ioi t) t)
    (hg' : IntervalIntegrable g' volume a x) :
    fractionalVolterra (alpha + 1) a g' x =
      fractionalVolterra alpha a g x -
        (((x - a) ^ alpha / Real.Gamma (alpha + 1)) • g a) := by
  rcases hax.eq_or_lt with rfl | hax
  · simp [Real.zero_rpow halpha.ne']
  let u : ℝ → ℝ :=
    fun t => (x - t) ^ alpha / Real.Gamma (alpha + 1)
  let u' : ℝ → ℝ :=
    fun t => -((x - t) ^ (alpha - 1) / Real.Gamma alpha)
  have hu : ContinuousOn u (Icc a x) := by
    dsimp only [u]
    exact ((continuousOn_const.sub continuousOn_id).rpow_const
      (fun _ _ => Or.inr halpha.le)).div_const _
  have hu_deriv : ∀ t ∈ Ioo a x, HasDerivAt u (u' t) t := by
    intro t ht
    have hlin : HasDerivAt (fun s : ℝ => x - s) (-1) t := by
      simpa only [id_eq] using (hasDerivAt_id t).const_sub x
    have hpow := hlin.rpow_const (p := alpha)
      (Or.inl (sub_ne_zero.mpr (ne_of_gt ht.2)))
    dsimp only [u, u']
    have hraw := hpow.div_const (Real.Gamma (alpha + 1))
    refine hraw.congr_deriv ?_
    rw [Real.Gamma_add_one halpha.ne']
    field_simp [halpha.ne', (Real.Gamma_pos_of_pos halpha).ne']
  have hu' : IntervalIntegrable u' volume a x := by
    have hk := intervalIntegrable_fractionalVolterra_kernel
      (E := ℝ) halpha hax.le (f := fun _ => (1 : ℝ)) continuousOn_const
    have hk' : IntervalIntegrable
        (fun t : ℝ => (x - t) ^ (alpha - 1) / Real.Gamma alpha)
        volume a x := by
      simpa only [smul_eq_mul, mul_one] using hk
    change IntervalIntegrable
      (-(fun t : ℝ => (x - t) ^ (alpha - 1) / Real.Gamma alpha))
      volume a x
    exact hk'.neg
  have hu_uIcc : ContinuousOn u (uIcc a x) := by
    simpa only [uIcc_of_le hax.le] using hu
  have hg_uIcc : ContinuousOn g (uIcc a x) := by
    simpa only [uIcc_of_le hax.le] using hg
  have hu_deriv_uIcc :
      ∀ t ∈ Ioo (min a x) (max a x), HasDerivAt u (u' t) t := by
    simpa only [min_eq_left hax.le, max_eq_right hax.le] using hu_deriv
  have hg_deriv_uIcc :
      ∀ t ∈ Ioo (min a x) (max a x),
        HasDerivWithinAt g (g' t) (Ioi t) t := by
    simpa only [min_eq_left hax.le, max_eq_right hax.le] using hderiv
  have hibp :=
    intervalIntegral.integral_smul_deriv_eq_deriv_smul_of_hasDeriv_right
      hu_uIcc hg_uIcc
      (fun t ht => (hu_deriv_uIcc t ht).hasDerivWithinAt)
      hg_deriv_uIcc hu' hg'
  rw [fractionalVolterra, fractionalVolterra]
  simp only [add_sub_cancel_right]
  change (∫ t in a..x, u t • g' t) =
    (∫ t in a..x,
      (((x - t) ^ (alpha - 1)) / Real.Gamma alpha) • g t) -
      (((x - a) ^ alpha / Real.Gamma (alpha + 1)) • g a)
  rw [hibp]
  dsimp only [u, u']
  rw [sub_self, Real.zero_rpow halpha.ne', zero_div, zero_smul]
  simp only [neg_smul, intervalIntegral.integral_neg]
  abel

/-- Boundary-free order raising when the primitive vanishes at its base
point. -/
theorem fractionalVolterra_add_one_deriv_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    {alpha a x : ℝ} (halpha : 0 < alpha) (hax : a ≤ x)
    {g g' : ℝ → E} (hg : ContinuousOn g (Icc a x))
    (hderiv : ∀ t ∈ Ioo a x, HasDerivWithinAt g (g' t) (Ioi t) t)
    (hg' : IntervalIntegrable g' volume a x) (hga : g a = 0) :
    fractionalVolterra (alpha + 1) a g' x =
      fractionalVolterra alpha a g x := by
  rw [fractionalVolterra_add_one_deriv halpha hax hg hderiv hg', hga,
    smul_zero, sub_zero]

end Fabius

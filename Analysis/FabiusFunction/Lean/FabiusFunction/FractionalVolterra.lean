import FabiusFunction.NormalizedVolterra
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Positive real-order Volterra operators

This module defines the normalized left Riemann--Liouville integral of
positive real order.  For an order `α`, base point `a`, input `f`, and
endpoint `x`, the operator is

`1 / Γ(α) ∫_a^x (x - t)^(α - 1) • f(t) dt`.

The definition is total, but its analytic theorems use the classical causal
regime `0 < α` and `a ≤ x`.  The codomain is an arbitrary real normed
space.  The main bridge identifies every positive natural order exactly with
`normalizedVolterra`.  A compact-right-support lemma also replaces the upper
endpoint by a minimum, which is the reusable bridge to the causal formulas
used for compactly supported inputs.

The shifted beta-kernel integral is evaluated exactly.  The full
fractional-order semigroup law is left to a later theorem because it additionally
requires a triangular Fubini argument for the input function.
-/

open scoped Interval Real
open MeasureTheory Set

namespace Fabius

set_option autoImplicit false

/-- The normalized left Volterra operator of real order `α` based at `a`.

The definition uses an oriented interval integral and is therefore total in
all parameters.  Its Riemann--Liouville interpretation is used below only for
positive orders and ordered endpoints. -/
noncomputable def fractionalVolterra
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α a : ℝ) (f : ℝ → E) (x : ℝ) : E :=
  ∫ t in a..x, (((x - t) ^ (α - 1)) / Real.Gamma α) • f t

/-- Every real-order Volterra operator vanishes when its endpoint equals its
base point. -/
@[simp]
theorem fractionalVolterra_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α a : ℝ) (f : ℝ → E) :
    fractionalVolterra α a f a = 0 := by
  simp [fractionalVolterra]

/-- Equality on the closed interval between the endpoints is enough to
replace the input of a fractional Volterra operator. -/
theorem fractionalVolterra_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α a x : ℝ) {f g : ℝ → E}
    (hfg : Set.EqOn f g (uIcc a x)) :
    fractionalVolterra α a f x = fractionalVolterra α a g x := by
  rw [fractionalVolterra, fractionalVolterra]
  apply intervalIntegral.integral_congr
  intro t ht
  change (((x - t) ^ (α - 1)) / Real.Gamma α) • f t =
    (((x - t) ^ (α - 1)) / Real.Gamma α) • g t
  rw [hfg ht]

/-- Scalar multiplication commutes with every real-order Volterra operator. -/
theorem fractionalVolterra_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α a x c : ℝ) (f : ℝ → E) :
    fractionalVolterra α a (fun t => c • f t) x =
      c • fractionalVolterra α a f x := by
  rw [fractionalVolterra, fractionalVolterra,
    ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro t _ht
  simp only [smul_smul]
  rw [mul_comm]

/-- For positive order, the fractional Volterra kernel times a continuous
input is interval integrable between ordered endpoints. -/
theorem intervalIntegrable_fractionalVolterra_kernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α a x : ℝ} (hα : 0 < α) (hax : a ≤ x)
    {f : ℝ → E} (hf : ContinuousOn f (Icc a x)) :
    IntervalIntegrable
      (fun t => (((x - t) ^ (α - 1)) / Real.Gamma α) • f t)
      volume a x := by
  have hpow : IntervalIntegrable (fun y : ℝ => y ^ (α - 1))
      volume (x - a) 0 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hshift : IntervalIntegrable (fun t : ℝ => (x - t) ^ (α - 1))
      volume a x := by
    simpa only [sub_sub_cancel, sub_zero] using hpow.comp_sub_left x
  have hscalar : IntervalIntegrable
      (fun t : ℝ => (x - t) ^ (α - 1) / Real.Gamma α)
      volume a x :=
    hshift.div_const (Real.Gamma α)
  exact hscalar.smul_continuousOn (by simpa only [uIcc_of_le hax] using hf)

/-- An interval integral whose integrand vanishes on the open right tail can
be cut off at `min x b`.  Endpoint values are irrelevant.

This operator-independent form is the reusable support-truncation engine for
fractional Volterra integrals and other causal kernels. -/
theorem intervalIntegral_eq_integral_min_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b x : ℝ} (hab : a ≤ b) (hax : a ≤ x)
    {g : ℝ → E} (hg : IntervalIntegrable g volume a x)
    (hzero : Set.EqOn g 0 (Ioo b x)) :
    (∫ t in a..x, g t) = ∫ t in a..min x b, g t := by
  rcases le_total x b with hxb | hbx
  · rw [min_eq_left hxb]
  · rw [min_eq_right hbx]
    have hbmem : b ∈ uIcc a x := by
      rw [uIcc_of_le hax]
      exact ⟨hab, hbx⟩
    have hparts :
        IntervalIntegrable g volume a b ∧
          IntervalIntegrable g volume b x :=
      (IntervalIntegrable.trans_iff hbmem).mp hg
    have htail : (∫ t in b..x, g t) = 0 := by
      calc
        (∫ t in b..x, g t) = ∫ _t in b..x, (0 : E) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards [Measure.ae_ne volume x] with t htx ht
          rw [uIoc_of_le hbx] at ht
          have ht' : t ∈ Ioo b x := ⟨ht.1, ht.2.lt_of_ne htx⟩
          simpa using hzero ht'
        _ = 0 := by simp
    have hjoin := intervalIntegral.integral_add_adjacent_intervals
      hparts.1 hparts.2
    rw [htail, add_zero] at hjoin
    exact hjoin.symm

/-- If a continuous input vanishes on the open interval from `b` to the
endpoint, a positive-order fractional Volterra integral may be cut off at
`min x b`.

The kernel remains centered at the original endpoint `x`; only the zero tail
of the integration interval is removed. -/
theorem fractionalVolterra_eq_intervalIntegral_min_of_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α a b x : ℝ} (hα : 0 < α) (hab : a ≤ b) (hax : a ≤ x)
    {f : ℝ → E} (hf : ContinuousOn f (Icc a x))
    (hzero : Set.EqOn f 0 (Ioo b x)) :
    fractionalVolterra α a f x =
      ∫ t in a..min x b,
        (((x - t) ^ (α - 1)) / Real.Gamma α) • f t := by
  rw [fractionalVolterra]
  apply intervalIntegral_eq_integral_min_of_eq_zero hab hax
    (intervalIntegrable_fractionalVolterra_kernel hα hax hf)
  intro t ht
  have hft : f t = 0 := by simpa using hzero ht
  simp only [hft, smul_zero, Pi.zero_apply]

/-- Fractional Volterra integration is additive on continuous inputs in the
positive-order, ordered-endpoint regime. -/
theorem fractionalVolterra_add_input
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α a x : ℝ} (hα : 0 < α) (hax : a ≤ x)
    {f g : ℝ → E} (hf : ContinuousOn f (Icc a x))
    (hg : ContinuousOn g (Icc a x)) :
    fractionalVolterra α a (fun t => f t + g t) x =
      fractionalVolterra α a f x + fractionalVolterra α a g x := by
  rw [fractionalVolterra, fractionalVolterra, fractionalVolterra]
  calc
    (∫ t in a..x,
        (((x - t) ^ (α - 1)) / Real.Gamma α) • (f t + g t)) =
        ∫ t in a..x,
          ((((x - t) ^ (α - 1)) / Real.Gamma α) • f t +
            (((x - t) ^ (α - 1)) / Real.Gamma α) • g t) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change (((x - t) ^ (α - 1)) / Real.Gamma α) • (f t + g t) =
        (((x - t) ^ (α - 1)) / Real.Gamma α) • f t +
          (((x - t) ^ (α - 1)) / Real.Gamma α) • g t
      rw [smul_add]
    _ = (∫ t in a..x,
          (((x - t) ^ (α - 1)) / Real.Gamma α) • f t) +
        ∫ t in a..x,
          (((x - t) ^ (α - 1)) / Real.Gamma α) • g t := by
      rw [intervalIntegral.integral_add
        (intervalIntegrable_fractionalVolterra_kernel hα hax hf)
        (intervalIntegrable_fractionalVolterra_kernel hα hax hg)]

/-- Order one is the ordinary oriented Volterra primitive. -/
theorem fractionalVolterra_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) (x : ℝ) :
    fractionalVolterra 1 a f x = ∫ t in a..x, f t := by
  simp [fractionalVolterra, Real.Gamma_one]

/-- At every positive natural order, the real-order operator agrees exactly
with the factorial-normalized Cauchy kernel `normalizedVolterra`. -/
theorem fractionalVolterra_nat_succ
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (a : ℝ) (f : ℝ → E) (x : ℝ) :
    fractionalVolterra ((n + 1 : ℕ) : ℝ) a f x =
      normalizedVolterra (n + 1) a f x := by
  simp only [fractionalVolterra, normalizedVolterra_succ, Nat.cast_add,
    Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast,
    Real.Gamma_nat_eq_factorial]

/-- Evaluation of the shifted real beta kernel on a nondegenerate interval. -/
theorem intervalIntegral_fractionalVolterra_betaKernel
    {α β s x : ℝ} (hα : 0 < α) (hβ : 0 < β) (hsx : s < x) :
    (∫ u in s..x,
        (x - u) ^ (α - 1) * (u - s) ^ (β - 1)) =
      (x - s) ^ (α + β - 1) *
        (Real.Gamma α * Real.Gamma β / Real.Gamma (α + β)) := by
  let L : ℝ := x - s
  have hL : 0 < L := by
    simpa only [L] using sub_pos.mpr hsx
  have hscaled :
      (∫ y in 0..L,
          y ^ (β - 1) * (L - y) ^ (α - 1)) =
        L ^ (α + β - 1) *
          (Real.Gamma α * Real.Gamma β /
            Real.Gamma (α + β)) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    calc
      (∫ y in 0..L,
          ((y ^ (β - 1) * (L - y) ^ (α - 1) : ℝ) : ℂ)) =
          ∫ y in 0..L,
          (y : ℂ) ^ ((β : ℂ) - 1) *
            ((L : ℂ) - y) ^ ((α : ℂ) - 1) := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hL.le] at hy
        change ((y ^ (β - 1) * (L - y) ^ (α - 1) : ℝ) : ℂ) =
          (y : ℂ) ^ ((β : ℂ) - 1) *
            ((L : ℂ) - (y : ℂ)) ^ ((α : ℂ) - 1)
        rw [Complex.ofReal_mul,
          Complex.ofReal_cpow hy.1,
          Complex.ofReal_cpow (sub_nonneg.mpr hy.2)]
        push_cast
        rfl
      _ = (L : ℂ) ^ ((β : ℂ) + (α : ℂ) - 1) *
          Complex.betaIntegral (β : ℂ) (α : ℂ) :=
        Complex.betaIntegral_scaled (β : ℂ) (α : ℂ) hL
      _ = ((L ^ (α + β - 1) *
          (Real.Gamma α * Real.Gamma β /
            Real.Gamma (α + β)) : ℝ) : ℂ) := by
        rw [Complex.betaIntegral_eq_Gamma_mul_div
          (β : ℂ) (α : ℂ)
          (by simpa using hβ) (by simpa using hα)]
        have hexp :
            (β : ℂ) + (α : ℂ) - 1 =
              ((α + β - 1 : ℝ) : ℂ) := by
          push_cast
          ring
        have hsum :
            (β : ℂ) + (α : ℂ) = ((α + β : ℝ) : ℂ) := by
          push_cast
          ring
        rw [hexp, hsum, Complex.Gamma_ofReal β,
          Complex.Gamma_ofReal α,
          Complex.Gamma_ofReal (α + β),
          ← Complex.ofReal_cpow hL.le]
        push_cast
        ring
  calc
    (∫ u in s..x,
        (x - u) ^ (α - 1) * (u - s) ^ (β - 1)) =
        ∫ u in s..x,
          (u - s) ^ (β - 1) *
            (L - (u - s)) ^ (α - 1) := by
      apply intervalIntegral.integral_congr
      intro u _hu
      have hu : L - (u - s) = x - u := by
        dsimp only [L]
        ring
      change (x - u) ^ (α - 1) * (u - s) ^ (β - 1) =
        (u - s) ^ (β - 1) * (L - (u - s)) ^ (α - 1)
      rw [hu, mul_comm]
    _ = ∫ y in 0..L,
        y ^ (β - 1) * (L - y) ^ (α - 1) := by
      simpa only [sub_self, L] using
        (intervalIntegral.integral_comp_sub_right
          (a := s) (b := x)
          (fun y : ℝ =>
            y ^ (β - 1) * (L - y) ^ (α - 1)) s)
    _ = (x - s) ^ (α + β - 1) *
        (Real.Gamma α * Real.Gamma β /
          Real.Gamma (α + β)) := by
      simpa only [L] using hscaled

end Fabius

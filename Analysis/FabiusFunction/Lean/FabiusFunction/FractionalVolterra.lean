import FabiusFunction.NormalizedVolterra
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
`normalizedVolterra`.

The beta-convolution and fractional-order semigroup laws are deliberately
left to a later module: their proofs require a separate triangular Fubini
argument and should not be hidden inside the elementary operator API.
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

end Fabius

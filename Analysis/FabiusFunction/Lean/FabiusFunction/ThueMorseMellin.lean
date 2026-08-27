import FabiusFunction.ThueMorseInfiniteProduct
import FabiusFunction.ThueMorseDirichlet
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.PSeries

/-!
# The Mellin representation of the shifted Dirichlet series

The atlas's Dirichlet–Mellin bridge, in the real absolutely-convergent
regime: for `σ > 1` and `a > 0`,

`Γ(σ)·D(σ,a) = ∫₀^∞ t^(σ-1)·e^(-at)·𝓔(t) dt`,

where `𝓔(t) = ∏(1-e^(-2^j t))` is the lacunary boundary product.  The
proof composes the analytic infinite-product identity with the Gamma
integral term by term; absolute convergence justifies the interchange.

* `integrableOn_rpow_mul_exp` — integrability of the Mellin kernel.
* `thueMorseDirichlet_eq_tsum` — for `σ > 1` the conditionally-defined
  `D(σ,a)` is the absolutely convergent `tsum`.
* `thueMorseDirichlet_mellin` — **the Mellin representation**
  (the `D(s,a)` display of the atlas's Dirichlet–Mellin row, real
  regime).

The two facts this file used to re-derive inline — `|ε(n)| = 1` and
`e^(-t)^n = e^(-n·t)` — are now `abs_thueMorseSign_real` and
`exp_neg_nat_mul` from `ThueMorseBoundaryFlatness`.
-/

set_option autoImplicit false

open Finset Filter MeasureTheory Set

namespace Fabius

/-- The Mellin kernel `t^(σ-1)·e^(-ct)` is integrable on `(0,∞)` for
`σ > 0`, `c > 0`. -/
theorem integrableOn_rpow_mul_exp (σ c : ℝ) (hσ : 0 < σ) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(c * t)))
      (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ (σ - 1))
      (Ioi 0) := Real.GammaIntegral_convergent hσ
  have hcomp : IntegrableOn
      (fun t : ℝ => Real.exp (-(c * t)) * (c * t) ^ (σ - 1)) (Ioi 0) := by
    have h := (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (-x) * x ^ (σ - 1)) 0 hc).mpr
      (by simpa using hg)
    simpa using h
  refine MeasureTheory.IntegrableOn.congr_fun
    (hcomp.const_mul (c ^ (1 - σ))) ?_ measurableSet_Ioi
  intro t ht
  have ht0 : (0 : ℝ) < t := ht
  dsimp only
  rw [Real.mul_rpow hc.le ht0.le,
    show (1 : ℝ) - σ = -(σ - 1) by ring, Real.rpow_neg hc.le]
  field_simp [(Real.rpow_pos_of_pos hc (σ - 1)).ne']
  try ring

/-- For `σ > 1` the shifted Dirichlet series converges absolutely and
its conditional limit is the `tsum`. -/
theorem thueMorseDirichlet_eq_tsum (σ a : ℝ) (hσ : 1 < σ) (ha : 0 < a) :
    thueMorseDirichlet σ a =
      ∑' n : ℕ, ((n : ℝ) + a) ^ (-σ) * (thueMorseSign n : ℝ) := by
  have hsummable : Summable
      (fun n : ℕ => ((n : ℝ) + a) ^ (-σ) * (thueMorseSign n : ℝ)) := by
    refine Summable.of_norm ?_
    have hp := (Real.summable_one_div_nat_add_rpow a σ).mpr hσ
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_) hp
    have hpos : (0 : ℝ) < (n : ℝ) + a := by positivity
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_thueMorseSign_real n, mul_one,
      abs_of_nonneg (Real.rpow_nonneg hpos.le _),
      Real.rpow_neg hpos.le, abs_of_pos hpos, one_div]
  have htend := hsummable.hasSum.tendsto_sum_nat
  exact Filter.Tendsto.limUnder_eq htend

/-- **The Mellin representation** in the real regime: for `σ > 1` and
`a > 0`,
`Γ(σ)·D(σ,a) = ∫₀^∞ t^(σ-1)·e^(-at)·𝓔(t) dt`. -/
theorem thueMorseDirichlet_mellin (σ a : ℝ) (hσ : 1 < σ) (ha : 0 < a) :
    Real.Gamma σ * thueMorseDirichlet σ a =
      ∫ t in Ioi (0 : ℝ),
        t ^ (σ - 1) * Real.exp (-(a * t)) * lacunaryExpProduct t := by
  have hσ0 : 0 < σ := by linarith
  -- rewrite the integrand through the analytic product identity
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      t ^ (σ - 1) * Real.exp (-(a * t)) * lacunaryExpProduct t =
      ∑' n : ℕ, (thueMorseSign n : ℝ) *
        (t ^ (σ - 1) * Real.exp (-(((n : ℝ) + a) * t))) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [← tsum_thueMorseSign_exp_eq_lacunaryExpProduct t ht0,
      ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [exp_neg_nat_mul]
    have hcomb : Real.exp (-(a * t)) * Real.exp (-((n : ℝ) * t)) =
        Real.exp (-(((n : ℝ) + a) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc t ^ (σ - 1) * Real.exp (-(a * t)) *
          ((thueMorseSign n : ℝ) * Real.exp (-((n : ℝ) * t)))
        = (thueMorseSign n : ℝ) * (t ^ (σ - 1) *
            (Real.exp (-(a * t)) * Real.exp (-((n : ℝ) * t)))) := by
          ring
      _ = (thueMorseSign n : ℝ) * (t ^ (σ - 1) *
            Real.exp (-(((n : ℝ) + a) * t))) := by
          rw [hcomb]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr]
  -- interchange the sum and the integral
  have hFint : ∀ n : ℕ,
      Integrable (fun t : ℝ => (thueMorseSign n : ℝ) *
        (t ^ (σ - 1) * Real.exp (-(((n : ℝ) + a) * t))))
        (volume.restrict (Ioi 0)) := by
    intro n
    exact (integrableOn_rpow_mul_exp σ ((n : ℝ) + a) hσ0
      (by positivity)).const_mul _
  have hvalue : ∀ n : ℕ,
      ∫ t in Ioi (0 : ℝ),
        t ^ (σ - 1) * Real.exp (-(((n : ℝ) + a) * t)) =
      (1 / ((n : ℝ) + a)) ^ σ * Real.Gamma σ :=
    fun n => Real.integral_rpow_mul_exp_neg_mul_Ioi hσ0 (by positivity)
  have habs : ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), ‖(thueMorseSign n : ℝ) *
        (t ^ (σ - 1) * Real.exp (-(((n : ℝ) + a) * t)))‖) =
      (1 / ((n : ℝ) + a)) ^ σ * Real.Gamma σ := by
    intro n
    rw [← hvalue n]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_thueMorseSign_real n, one_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _),
      abs_of_nonneg (Real.exp_pos _).le]
  have hnormsum : Summable (fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖(thueMorseSign n : ℝ) *
        (t ^ (σ - 1) * Real.exp (-(((n : ℝ) + a) * t)))‖) := by
    refine Summable.congr ?_ (fun n => (habs n).symm)
    apply Summable.mul_right
    have hp := (Real.summable_one_div_nat_add_rpow a σ).mpr hσ
    refine hp.congr fun n => ?_
    have hpos : (0 : ℝ) < (n : ℝ) + a := by positivity
    rw [abs_of_pos hpos, one_div, one_div, Real.inv_rpow hpos.le]
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    hFint hnormsum
  rw [← hswap]
  -- evaluate the series of Gamma integrals
  have hterm : ∀ n : ℕ,
      (∫ t in Ioi (0 : ℝ), (thueMorseSign n : ℝ) *
        (t ^ (σ - 1) * Real.exp (-(((n : ℝ) + a) * t)))) =
      Real.Gamma σ * (((n : ℝ) + a) ^ (-σ) * (thueMorseSign n : ℝ)) := by
    intro n
    rw [MeasureTheory.integral_const_mul, hvalue n]
    have hpos : (0 : ℝ) < (n : ℝ) + a := by positivity
    have hid : (1 / ((n : ℝ) + a)) ^ σ = ((n : ℝ) + a) ^ (-σ) := by
      rw [one_div, Real.inv_rpow hpos.le, ← Real.rpow_neg hpos.le]
    rw [hid]
    ring
  rw [tsum_congr hterm, tsum_mul_left, thueMorseDirichlet_eq_tsum σ a hσ ha]

end Fabius

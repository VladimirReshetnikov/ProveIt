import FabiusFunction.IntervalParseval
import FabiusFunction.FourierProduct
import FabiusFunction.WeakConvergence

/-!
# The energy of Rvachev's function from its half-integer Fourier samples

Rvachev's up-function is supported in `[-1, 1]`, so it is determined by the
values of its Fourier transform on the lattice `½ℤ` dual to that interval, and
its energy is recovered from those samples alone:

`∫_ℝ up(t)² dt = ½ · ∑_{k ∈ ℤ} |û(k/2)|²`.

This is the interval Parseval identity of `IntervalParseval`, specialized.  It
is the second equality of the "total Fourier energy" proposition in the
Rvachev Fourier-decay volume; the first equality there, Plancherel, is
`integral_norm_sq_rvachevFourier_eq_two_mul_fabiusSquareEnergy`.

The integer samples are known exactly — `û(0) = 1` and `û(m) = 0` for every
other integer `m`, by `rvachevFourier_int_eq_ite` — so only the half-integer
samples carry information, and the two-sided lattice sum folds, using also
the evenness `rvachevFourier_neg`, to `∫ up² = ½ + ∑_{m ≥ 0} û(m + ½)²`, the
form in which the volume states it.  That folding — splitting the `ℤ`-sum
into its even and odd halves and reflecting the negative half — is not yet
formalized here; this module stops at the two-sided identity, which is the
analytic content, and the folding is bookkeeping about `tsum` over `ℤ`.

## Conventions

`rvachevFourier F z = ∫ up(t) · exp(-2πi·t·z) dt` is, on the real axis,
exactly Mathlib's `𝓕` of the complex lift of `up`; `rvachevFourier_eq_fourierIntegral`
records this, and everything else is transported through it.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped FourierTransform

namespace Fabius

/-- On the real axis, `rvachevFourier` is Mathlib's Fourier transform `𝓕` of
the complex lift of Rvachev's function: the two are the same integral with
the same `2π` in the exponent and no prefactor. -/
theorem rvachevFourier_eq_fourierIntegral (F : BoundedFabius) (x : ℝ) :
    rvachevFourier F (x : ℂ) = 𝓕 (fun t : ℝ => (rvachevUp F t : ℂ)) x := by
  rw [rvachevFourier, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (rvachevUp F t : ℂ) * Complex.exp (-2 * Real.pi * Complex.I * t * x) =
    Complex.exp (((-2 * Real.pi * t * x : ℝ) : ℂ) * Complex.I) • (rvachevUp F t : ℂ)
  rw [smul_eq_mul, mul_comm]
  congr 2
  push_cast
  ring

/-- The complex lift of Rvachev's function vanishes off `[-1, 1]`. -/
theorem rvachevUp_ofReal_eq_zero_of_not_mem_Icc (F : BoundedFabius) (hF : IsFabius F)
    {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : ((rvachevUp F x : ℝ) : ℂ) = 0 := by
  rw [rvachevUp_eq_zero_of_not_mem_Ioo F hF (fun h => hx (Ioo_subset_Icc_self h)),
    Complex.ofReal_zero]

/-- Rvachev's function is square-integrable: it is continuous with compact
support. -/
theorem rvachevUp_memLp_two (F : BoundedFabius) (hF : IsFabius F) :
    MemLp (rvachevUp F) 2 volume :=
  (rvachev_contDiff F hF).continuous.memLp_of_hasCompactSupport
    (rvachevUp_hasCompactSupport F hF)

/-- **Energy from the dual-lattice samples.**  The energy of Rvachev's function
is half the sum of the squared moduli of its Fourier transform over the
half-integers: interval Parseval on `[-1, 1]`. -/
theorem integral_sq_rvachevUp_eq_half_tsum_sq_rvachevFourier
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ t : ℝ, rvachevUp F t ^ 2) =
      2⁻¹ * ∑' k : ℤ, ‖rvachevFourier F (((k : ℝ) / 2 : ℝ) : ℂ)‖ ^ 2 := by
  have h := IntervalParseval.integral_sq_eq_tsum_sq_fourierIntegral_symm_real
    (L := 1) one_pos (h := rvachevUp F)
    (fun x hx => rvachevUp_eq_zero_of_not_mem_Ioo F hF
      (fun hmem => hx (Ioo_subset_Icc_self hmem)))
    (rvachevUp_memLp_two F hF)
  rw [h, show (2 : ℝ) * 1 = 2 by norm_num]
  congr 1
  refine tsum_congr fun k => ?_
  rw [rvachevFourier_eq_fourierIntegral]

end Fabius

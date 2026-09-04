import FabiusFunction.IntervalParseval
import FabiusFunction.IntSumFolding
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
form in which the volume states it
(`integral_sq_rvachevUp_eq_half_add_tsum_sq_rvachevFourier`).  The folding
itself is the general `IntSum.tsum_eq_zero_add_two_mul_tsum_odd`: any even
summable family vanishing at nonzero even integers sums to its value at `0`
plus twice its sum over the positive odd integers.

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

/-! ### Folding the lattice sum onto the half-integers

The samples at the integers are `1` at `0` and `0` elsewhere, and the
transform is even on the real axis, so the two-sided lattice sum collapses to
`1` plus twice the sum over the positive half-integers.  The bookkeeping is
`IntSum.tsum_eq_zero_add_two_mul_tsum_odd`, stated for any even summable
family vanishing at nonzero even integers. -/

/-- The squared moduli of the dual-lattice samples form a summable family. -/
theorem summable_sq_rvachevFourier_half (F : BoundedFabius) (hF : IsFabius F) :
    Summable fun k : ℤ => ‖rvachevFourier F (((k : ℝ) / 2 : ℝ) : ℂ)‖ ^ 2 := by
  have hs := (IntervalParseval.hasSum_sq_fourierIntegral_dual_lattice
    (a := -1) (b := 1) (by norm_num) (h := fun t : ℝ => (rvachevUp F t : ℂ))
    (fun x hx => rvachevUp_ofReal_eq_zero_of_not_mem_Icc F hF hx)
    ((rvachevUp_memLp_two F hF).ofReal.restrict _)).summable
  refine hs.congr fun k => ?_
  rw [rvachevFourier_eq_fourierIntegral, show (1 : ℝ) - -1 = 2 by norm_num]

/-- The dual-lattice sample is even in the index. -/
theorem norm_sq_rvachevFourier_half_neg (F : BoundedFabius) (hF : IsFabius F) (k : ℤ) :
    ‖rvachevFourier F (((((-k : ℤ) : ℝ) / 2 : ℝ)) : ℂ)‖ ^ 2 =
      ‖rvachevFourier F (((k : ℝ) / 2 : ℝ) : ℂ)‖ ^ 2 := by
  have : (((((-k : ℤ) : ℝ) / 2 : ℝ)) : ℂ) = -((((k : ℝ) / 2 : ℝ) : ℂ)) := by push_cast; ring
  rw [this, rvachevFourier_neg F hF]

/-- The dual-lattice sample vanishes at every nonzero even index: those are the
nonzero integer samples. -/
theorem norm_sq_rvachevFourier_half_two_mul (F : BoundedFabius) (hF : IsFabius F)
    {m : ℤ} (hm : m ≠ 0) :
    ‖rvachevFourier F (((((2 * m : ℤ) : ℝ) / 2 : ℝ)) : ℂ)‖ ^ 2 = 0 := by
  have : (((((2 * m : ℤ) : ℝ) / 2 : ℝ)) : ℂ) = ((m : ℤ) : ℂ) := by push_cast; ring
  rw [this, rvachevFourier_int_eq_ite F hF, if_neg hm]
  simp

/-- **The half-integer energy formula.**  The energy of Rvachev's function is
`½` plus the sum of the squared Fourier samples at the positive half-integers:
`∫ up² = ½ + ∑_{m ≥ 0} û(m + ½)²`.  The integer samples contribute exactly
`û(0)² = 1`, halved. -/
theorem integral_sq_rvachevUp_eq_half_add_tsum_sq_rvachevFourier
    (F : BoundedFabius) (hF : IsFabius F) :
    (∫ t : ℝ, rvachevUp F t ^ 2) =
      2⁻¹ + ∑' m : ℕ, ‖rvachevFourier F ((((m : ℝ) + 1 / 2 : ℝ)) : ℂ)‖ ^ 2 := by
  rw [integral_sq_rvachevUp_eq_half_tsum_sq_rvachevFourier F hF]
  have hmain := IntSum.tsum_eq_zero_add_two_mul_tsum_odd
    (summable_sq_rvachevFourier_half F hF)
    (norm_sq_rvachevFourier_half_neg F hF)
    (fun m hm => norm_sq_rvachevFourier_half_two_mul F hF hm)
  have h0 : ‖rvachevFourier F (((((0 : ℤ) : ℝ) / 2 : ℝ)) : ℂ)‖ ^ 2 = 1 := by
    rw [show (((((0 : ℤ) : ℝ) / 2 : ℝ)) : ℂ) = ((0 : ℤ) : ℂ) by push_cast; ring,
      rvachevFourier_int_eq_ite F hF, if_pos rfl]
    simp
  have hodd : ∀ n : ℕ,
      ‖rvachevFourier F (((((2 * (n : ℤ) + 1 : ℤ) : ℝ) / 2 : ℝ)) : ℂ)‖ ^ 2 =
        ‖rvachevFourier F ((((n : ℝ) + 1 / 2 : ℝ)) : ℂ)‖ ^ 2 := by
    intro n
    have : (((((2 * (n : ℤ) + 1 : ℤ) : ℝ) / 2 : ℝ)) : ℂ) = (((n : ℝ) + 1 / 2 : ℝ) : ℂ) := by
      push_cast; ring
    rw [this]
  rw [hmain, h0, tsum_congr hodd]
  ring

end Fabius

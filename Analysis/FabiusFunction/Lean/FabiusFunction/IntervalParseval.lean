import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform

/-!
# Parseval on an interval: a time-limited function is determined by its dual-lattice samples

A square-integrable function supported in an interval of length `T` carries no
more information than the values its Fourier transform takes on the lattice
`T⁻¹ℤ` dual to that interval, and its energy is recovered from those samples
alone, with the lattice covolume as the only constant:

`∫_ℝ ‖h‖² = T⁻¹ · ∑_{n ∈ ℤ} ‖ĥ(n / T)‖²`.

This is Parseval for the circle `ℝ / Tℤ` read on the line.  The bridge is
`fourierIntegral_eq_mul_fourierCoeffOn`: for `h` vanishing off `[a,b]` the
Fourier *transform* sampled at `n / (b - a)` is exactly `(b - a)` times the
`n`-th Fourier *coefficient* of `h` on `[a,b]`, because the two integrands
agree on `[a,b]` and the transform sees nothing else.  Squaring turns the
factor `(b-a)` of the bridge and the factor `(b-a)⁻¹` of the circle Parseval
identity into the single factor `(b-a)⁻¹` above.

## Conventions

Both conventions are Mathlib's, and they must be quoted together because a
Parseval constant is exactly where a mismatch hides.

* On the line, `𝓕` is `Real.fourierIntegral`:
  `𝓕 h w = ∫ v, exp (-2πi·v·w) · h v dv` — the `2π` sits in the exponent and
  there is no `(2π)^(-1/2)` prefactor.
* On the interval, `fourierCoeffOn hab h n = (b-a)⁻¹ ∫_a^b exp (-2πi·n·x/(b-a)) h x dx`,
  and Mathlib's `hasSum_sq_fourierCoeffOn` reads
  `∑_n ‖ĥ(n)‖² = (b-a)⁻¹ ∫_a^b ‖h‖²`.

Because the frequency variable `w` is an ordinary frequency and not an angular
one, the lattice dual to an interval of length `T` is `T⁻¹ℤ`, not `(2π/T)ℤ`.
With a support half-width `L` the interval has length `T = 2L`; **that** is the
origin of the factor two in the symmetric statements below, where the samples
sit at `k/(2L)` and the constant is `(2L)⁻¹`.  At `L = 1` this is
`∫_ℝ ‖h‖² = ½ ∑_{k ∈ ℤ} ‖ĥ(k/2)‖²`.

## Main results

* `MeasureTheory.intervalIntegral_eq_integral_of_forall_compl_Icc_eq_zero` — an
  integral over `[a,b]` of a function vanishing off `[a,b]` is the integral over
  the whole line.
* `IntervalParseval.fourierIntegral_eq_mul_fourierCoeffOn` — **the bridge**:
  `𝓕 h (n / (b-a)) = (b-a) · fourierCoeffOn hab h n`.
* `IntervalParseval.hasSum_sq_fourierIntegral_dual_lattice` and
  `IntervalParseval.integral_sq_eq_tsum_sq_fourierIntegral` — **the identity**,
  as a `HasSum` and as a `tsum`.
* `IntervalParseval.integral_sq_eq_tsum_sq_fourierIntegral_of_le` — the
  oversampled form: the support interval only has to *fit* inside a period, so
  the identity holds on every lattice `T⁻¹ℤ` with `T` at least the diameter of
  the support.  This is the generality the statement really has; the equality
  case is the classical one.
* `IntervalParseval.integral_sq_eq_tsum_sq_fourierIntegral_symm`,
  `..._half_width_one`, `..._symm_real` — the symmetric specializations
  `supp h ⊆ [-L, L]`, its unit case `L = 1`, and the real-valued restatement.

The hypotheses are the weakest that make the statements true: square
integrability is asked only on the support interval in the core results, and
a global `MemLp h 2 volume` (which yields it through `MemLp.restrict`) only
where the interval is allowed to move.  Nothing here is specific to any
particular function; the module deliberately imports no application.
-/

set_option autoImplicit false

open MeasureTheory
open scoped FourierTransform

namespace MeasureTheory

/-- A function that vanishes outside `[a,b]` has the same integral over `[a,b]`
as over the whole line.  Stated for values in an arbitrary real normed space,
since the proof never looks at the target beyond additivity. -/
theorem intervalIntegral_eq_integral_of_forall_compl_Icc_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} (hab : a ≤ b) {g : ℝ → E} (hg : ∀ x ∉ Set.Icc a b, g x = 0) :
    (∫ x in a..b, g x) = ∫ x : ℝ, g x := by
  rw [_root_.intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hg

end MeasureTheory

namespace IntervalParseval

/-! ### Samples of the transform are the coefficients on the interval -/

/-- **The bridge between the line and the circle.**  A function vanishing off
`[a,b]` cannot tell the Fourier transform of the line from the Fourier
coefficients of the interval: at the dual-lattice frequency `n / (b - a)` the
two differ only by the length of the interval,

`𝓕 h (n / (b - a)) = (b - a) · fourierCoeffOn hab h n`.

No integrability hypothesis is needed — if `h` is not integrable both sides are
the same junk value, because they are literally the same integral. -/
theorem fourierIntegral_eq_mul_fourierCoeffOn
    {a b : ℝ} (hab : a < b) {h : ℝ → ℂ}
    (hsupp : ∀ x ∉ Set.Icc a b, h x = 0) (n : ℤ) :
    𝓕 h ((n : ℝ) / (b - a)) = ((b - a : ℝ) : ℂ) * fourierCoeffOn hab h n := by
  have hT : (0 : ℝ) < b - a := sub_pos.mpr hab
  -- the two exponential kernels agree pointwise
  have hexp : ∀ v : ℝ,
      Complex.exp (((-2 * Real.pi * v * ((n : ℝ) / (b - a)) : ℝ) : ℂ) * Complex.I) =
        fourier (-n) (v : AddCircle (b - a)) := by
    intro v
    rw [fourier_coe_apply]
    congr 1
    push_cast
    ring
  have hker : ∀ v : ℝ,
      Complex.exp (((-2 * Real.pi * v * ((n : ℝ) / (b - a)) : ℝ) : ℂ) * Complex.I) • h v =
        fourier (-n) (v : AddCircle (b - a)) • h v := fun v => by rw [hexp v]
  -- outside `[a,b]` the integrand vanishes, so the line integral is an interval one
  have hbridge : (∫ v in a..b,
        Complex.exp (((-2 * Real.pi * v * ((n : ℝ) / (b - a)) : ℝ) : ℂ) * Complex.I) • h v) =
      ∫ v : ℝ,
        Complex.exp (((-2 * Real.pi * v * ((n : ℝ) / (b - a)) : ℝ) : ℂ) * Complex.I) • h v :=
    intervalIntegral_eq_integral_of_forall_compl_Icc_eq_zero hab.le
      (fun v hv => by rw [hsupp v hv, smul_zero])
  have hcongr : (∫ v in a..b,
        Complex.exp (((-2 * Real.pi * v * ((n : ℝ) / (b - a)) : ℝ) : ℂ) * Complex.I) • h v) =
      ∫ v in a..b, fourier (-n) (v : AddCircle (b - a)) • h v :=
    intervalIntegral.integral_congr (fun v _ => hker v)
  rw [Real.fourier_real_eq_integral_exp_smul, ← hbridge, hcongr,
    fourierCoeffOn_eq_integral, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    mul_one_div, div_self hT.ne', Complex.ofReal_one, one_mul]

/-! ### Parseval on the dual lattice -/

/-- **The interval Parseval identity.**  For `h` square integrable and
supported in `[a,b]`, the squared moduli of the samples of `𝓕 h` on the dual
lattice `(b-a)⁻¹ℤ` sum to `(b - a)` times the energy of `h`.

Read the other way round — as in
`integral_sq_eq_tsum_sq_fourierIntegral` — this recovers the energy of a
time-limited signal from countably many samples of its spectrum. -/
theorem hasSum_sq_fourierIntegral_dual_lattice
    {a b : ℝ} (hab : a < b) {h : ℝ → ℂ}
    (hsupp : ∀ x ∉ Set.Icc a b, h x = 0)
    (hL2 : MemLp h 2 (volume.restrict (Set.Ioc a b))) :
    HasSum (fun n : ℤ => ‖𝓕 h ((n : ℝ) / (b - a))‖ ^ 2)
      ((b - a) * ∫ x : ℝ, ‖h x‖ ^ 2) := by
  have hT : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hint : (∫ x in a..b, ‖h x‖ ^ 2) = ∫ x : ℝ, ‖h x‖ ^ 2 :=
    intervalIntegral_eq_integral_of_forall_compl_Icc_eq_zero hab.le
      (fun x hx => by simp [hsupp x hx])
  have hcoef : (b - a) ^ 2 * (b - a)⁻¹ = b - a := by
    rw [pow_two, mul_assoc, mul_inv_cancel₀ hT.ne', mul_one]
  have hval : (b - a) ^ 2 * ((b - a)⁻¹ • ∫ x in a..b, ‖h x‖ ^ 2) =
      (b - a) * ∫ x : ℝ, ‖h x‖ ^ 2 := by
    rw [smul_eq_mul, hint, ← mul_assoc, hcoef]
  have hterm : ∀ n : ℤ,
      (b - a) ^ 2 * ‖fourierCoeffOn hab h n‖ ^ 2 = ‖𝓕 h ((n : ℝ) / (b - a))‖ ^ 2 := by
    intro n
    rw [fourierIntegral_eq_mul_fourierCoeffOn hab hsupp n, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT, mul_pow]
  have hfun : (fun n : ℤ => ‖𝓕 h ((n : ℝ) / (b - a))‖ ^ 2) =
      fun n : ℤ => (b - a) ^ 2 * ‖fourierCoeffOn hab h n‖ ^ 2 :=
    funext fun n => (hterm n).symm
  rw [← hval, hfun]
  exact (hasSum_sq_fourierCoeffOn hab hL2).mul_left ((b - a) ^ 2)

/-- **The energy of a time-limited function from its dual-lattice samples**:
if `h` is square integrable and vanishes off `[a,b]`, then

`∫_ℝ ‖h‖² = (b-a)⁻¹ ∑_{n ∈ ℤ} ‖𝓕 h (n/(b-a))‖²`.

The constant is the covolume of the sampling lattice; see the module header for
where it comes from in Mathlib's normalization. -/
theorem integral_sq_eq_tsum_sq_fourierIntegral
    {a b : ℝ} (hab : a < b) {h : ℝ → ℂ}
    (hsupp : ∀ x ∉ Set.Icc a b, h x = 0)
    (hL2 : MemLp h 2 (volume.restrict (Set.Ioc a b))) :
    (∫ x : ℝ, ‖h x‖ ^ 2) =
      (b - a)⁻¹ * ∑' n : ℤ, ‖𝓕 h ((n : ℝ) / (b - a))‖ ^ 2 := by
  have hT : (0 : ℝ) < b - a := sub_pos.mpr hab
  rw [(hasSum_sq_fourierIntegral_dual_lattice hab hsupp hL2).tsum_eq, ← mul_assoc,
    inv_mul_cancel₀ hT.ne', one_mul]

/-- **Oversampling.**  The support interval only has to *fit* inside a period:
if `h` vanishes off `[a,b]` and `b ≤ a + T` with `T > 0`, then the identity
holds verbatim on the coarser lattice `T⁻¹ℤ`,

`∫_ℝ ‖h‖² = T⁻¹ ∑_{n ∈ ℤ} ‖𝓕 h (n/T)‖²`.

Enlarging `T` refines the lattice `T⁻¹ℤ`, so there are more samples; the
constant `T⁻¹` in front shrinks by exactly the same factor, and the energy
comes out unchanged.  The classical statement is the case `b = a + T`. -/
theorem integral_sq_eq_tsum_sq_fourierIntegral_of_le
    {a b T : ℝ} (hT : 0 < T) (hbT : b ≤ a + T) {h : ℝ → ℂ}
    (hsupp : ∀ x ∉ Set.Icc a b, h x = 0) (hL2 : MemLp h 2 volume) :
    (∫ x : ℝ, ‖h x‖ ^ 2) = T⁻¹ * ∑' n : ℤ, ‖𝓕 h ((n : ℝ) / T)‖ ^ 2 := by
  have hab : a < a + T := lt_add_of_pos_right a hT
  have hsupp' : ∀ x ∉ Set.Icc a (a + T), h x = 0 := by
    intro x hx
    refine hsupp x fun hmem => hx ?_
    rw [Set.mem_Icc] at hmem ⊢
    exact ⟨hmem.1, hmem.2.trans hbT⟩
  have h0 := integral_sq_eq_tsum_sq_fourierIntegral hab hsupp'
    (hL2.restrict (Set.Ioc a (a + T)))
  rwa [show a + T - a = T by ring] at h0

/-! ### Symmetric supports -/

/-- The identity for a support half-width: if `h` vanishes off `[-L, L]` then
the period is `2L`, the samples sit at `k/(2L)`, and

`∫_ℝ ‖h‖² = (2L)⁻¹ ∑_{k ∈ ℤ} ‖𝓕 h (k/(2L))‖²`. -/
theorem integral_sq_eq_tsum_sq_fourierIntegral_symm
    {L : ℝ} (hL : 0 < L) {h : ℝ → ℂ}
    (hsupp : ∀ x ∉ Set.Icc (-L) L, h x = 0) (hL2 : MemLp h 2 volume) :
    (∫ x : ℝ, ‖h x‖ ^ 2) =
      (2 * L)⁻¹ * ∑' k : ℤ, ‖𝓕 h ((k : ℝ) / (2 * L))‖ ^ 2 := by
  refine integral_sq_eq_tsum_sq_fourierIntegral_of_le (T := 2 * L) ?_ ?_ hsupp hL2
  · linarith
  · linarith

/-- The unit case `L = 1`, the shape in which the identity is usually quoted:
a square-integrable function supported in `[-1, 1]` has

`∫_ℝ ‖h‖² = ½ ∑_{k ∈ ℤ} ‖𝓕 h (k/2)‖²`,

the samples running over the half-integers together with the integers. -/
theorem integral_sq_eq_tsum_sq_fourierIntegral_half_width_one
    {h : ℝ → ℂ} (hsupp : ∀ x ∉ Set.Icc (-1 : ℝ) 1, h x = 0)
    (hL2 : MemLp h 2 volume) :
    (∫ x : ℝ, ‖h x‖ ^ 2) = 2⁻¹ * ∑' k : ℤ, ‖𝓕 h ((k : ℝ) / 2)‖ ^ 2 := by
  have h0 := integral_sq_eq_tsum_sq_fourierIntegral_symm (L := 1) one_pos hsupp hL2
  rwa [show (2 : ℝ) * 1 = 2 by norm_num] at h0

/-- The real-valued restatement of the symmetric identity.  The transform is
still taken of the complex lift, since that is where the Fourier transform
lives, but the energy on the left is the honest real integral `∫ h²`. -/
theorem integral_sq_eq_tsum_sq_fourierIntegral_symm_real
    {L : ℝ} (hL : 0 < L) {h : ℝ → ℝ}
    (hsupp : ∀ x ∉ Set.Icc (-L) L, h x = 0) (hL2 : MemLp h 2 volume) :
    (∫ x : ℝ, h x ^ 2) =
      (2 * L)⁻¹ * ∑' k : ℤ, ‖𝓕 (fun x : ℝ => (h x : ℂ)) ((k : ℝ) / (2 * L))‖ ^ 2 := by
  have hsupp' : ∀ x ∉ Set.Icc (-L) L, ((h x : ℂ)) = 0 := by
    intro x hx
    rw [hsupp x hx, Complex.ofReal_zero]
  have h0 := integral_sq_eq_tsum_sq_fourierIntegral_symm
    (h := fun x : ℝ => (h x : ℂ)) hL hsupp' hL2.ofReal
  have hnorm : (∫ x : ℝ, ‖(h x : ℂ)‖ ^ 2) = ∫ x : ℝ, h x ^ 2 := by
    congr 1
    funext x
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [← hnorm]
  exact h0

end IntervalParseval

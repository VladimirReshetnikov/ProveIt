import FabiusFunction.FourierProduct
import FabiusFunction.GeometricScaleProducts
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The generalized Rvachev transform of an exponent sequence

The exponents volume attaches to every *admissible exponent sequence*
`a : ℕ → ℕ` — admissible meaning `A(1/2) = ∑_h a h · 2 ^ (-h) < ∞` —
the **generalized Rvachev transform**

`Φ_a(z) = ∏_{h ≥ 0} sinc (z / 2 ^ h) ^ (a h)`,

where the volume's normalized sinc is `sinc w = sin (π w) / (π w)`.
The corpus's `complexSinc` is the *unnormalized* removable
`sin w / w`, so the volume's `sinc (z / 2 ^ h)` is the corpus's
`complexSinc (π * z / 2 ^ h)`; this is exactly the factor appearing in
`Fabius.rvachevFourierProduct`, and `generalizedRvachevProduct_one`
below is the regression test pinning that identification.

Only the classical case `a h = 1` was formalized before this file.
This module builds the definition and the elementary layer of the
volume's master theorem:

* the family of factors is `Multipliable` in Mathlib's (unconditional)
  sense at **every** `z : ℂ`, including the points where factors
  vanish, exactly as `Fabius.sincFactors_multipliable` does for the
  classical product;
* the transform is additive in the exponent sequence;
* on finitely supported exponents it is the corresponding finite
  product;
* its zero set is described completely;
* the one-step dyadic shift/refinement law holds.

## What is deliberately **not** proved here

Nothing in this file asserts convergence that is uniform on compact
sets, nothing asserts that `Φ_a` is differentiable or entire, no
probabilistic model (the sum `X_a` of scaled uniform variables) is
constructed, and the regrouping of the product into the canonical form
`∏_{n ≥ 1} (1 - z² / n²) ^ (m_a n)` is absent.  Those are separate and
larger developments; at `a h = 1` the corresponding statements are
`RvachevProductContinuity` (uniform convergence on compacts of the
*real* axis, and continuity there) and `SincCanonicalProduct` (the
canonical regrouping with multiplicity `1 + v₂ m`).

Two of the three have since been carried out at general weight, both
building on this file's `Multipliable` results:
`FabiusFunction.GeneralizedCanonicalForm` proves the regrouping, and
`FabiusFunction.GeneralizedRvachevEntire` proves locally uniform
convergence on every ball, hence that `Φ_a` is entire.  The
probabilistic model remains absent.  The sentence above still
describes *this* file accurately — it is a statement of scope, not a
claim about the corpus.

The admissibility hypothesis is spelled `Summable fun h => a h / 2 ^ h`
with the values cast into `ℝ`.  `DigitDefectCounting` states the same
condition for *real* weight sequences as
`Summable fun h => |a h| / 2 ^ h`; `summable_natCast_div_two_pow_iff`
records that for `ℕ`-valued weights the two spellings agree, so the
hypothesis of that file is met by the cast of an admissible `a`.

## Main declarations

* `Fabius.generalizedRvachevProduct` — the **definition**
  `Φ_a(z) = ∏' h, complexSinc (π * z / 2 ^ h) ^ (a h)`.
* `Fabius.shiftExponent`, `Fabius.shiftExponent_apply` — the shift
  `(S a) h = a (h + 1)` and its defining equation.
* `Fabius.summable_natCast_div_two_pow_iff` — for `ℕ`-valued weights
  the admissibility hypothesis used here and the absolute-value
  spelling used by `DigitDefectCounting` are the same statement.
* `Fabius.exp_sub_one_le_mul_exp` — the elementary real inequality
  `exp t - 1 ≤ t · exp t`, valid for every real `t`.
* `Fabius.norm_one_add_pow_sub_one_le` — the **power deviation
  bound** `‖(1 + y) ^ n - 1‖ ≤ exp (n · ‖y‖) - 1` in `ℂ`, obtained
  from Mathlib's `Finset.norm_prod_one_add_sub_one_le` for the constant
  family on `Finset.range n`.
* `Fabius.summable_norm_of_norm_le_exp_sub_one` — the comparison test
  in the shape produced by that bound: if `v` is summable and
  nonnegative and `‖x n‖ ≤ exp (v n) - 1`, then `‖x ·‖` is summable.
* `Fabius.summable_natCast_mul_norm_sincFactor_sub_one` — the
  **weighted factor-deviation series** `∑_h a h · ‖sinc factor - 1‖`
  converges under admissibility.
* `Fabius.summable_norm_generalizedSincFactor_sub_one`,
  `Fabius.summable_generalizedSincFactor_sub_one` — the deviations
  `complexSinc (π z / 2 ^ h) ^ (a h) - 1` are absolutely summable.
* `Fabius.generalizedSincFactors_multipliable` — **convergence**: the
  factors are multipliable at every `z : ℂ`.
* `Fabius.generalizedRvachevProduct_one` — **classical recovery**
  `Φ_{(1,1,…)} = rvachevFourierProduct`, the normalization test.
* `Fabius.generalizedRvachevProduct_zero_exponent` — `Φ_0 = 1`.
* `Fabius.generalizedRvachevProduct_at_zero` — `Φ_a(0) = 1`.
* `Fabius.generalizedRvachevProduct_add` — **additivity**
  `Φ_{a+b} = Φ_a · Φ_b`.
* `Fabius.generalizedRvachevProduct_eq_prod` — **finite support**: if
  `a` vanishes off a `Finset s`, the transform is the finite product
  over `s`; no admissibility is needed.
* `Fabius.complexSinc_pi_div_two_pow_eq_zero_iff` — the `h`-th factor
  vanishes exactly at the nonzero integer multiples of `2 ^ h`.
* `Fabius.generalizedRvachevProduct_eq_zero_of_factor` — one vanishing
  factor with a nonzero exponent kills the product; no admissibility.
* `Fabius.generalizedRvachevProduct_ne_zero` — conversely, under
  admissibility no product zero is hidden in the tail.
* `Fabius.generalizedRvachevProduct_eq_zero_iff` — the **zero set**:
  `Φ_a(z) = 0` iff `z = k · 2 ^ h` for some `h` with `a h ≠ 0` and some
  nonzero integer `k`.
* `Fabius.summable_shiftExponent` — admissibility is inherited by the
  shift `S a`.
* `Fabius.generalizedRvachevProduct_two_mul` — the **shift-refinement
  law** `Φ_a(2z) = complexSinc (π · 2z) ^ (a 0) · Φ_{S a}(z)`, the
  general-exponent form of `rvachevFourierProduct_two_mul`.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter

namespace Fabius

/-- **The generalized Rvachev transform** of an exponent sequence
`a : ℕ → ℕ`,

`Φ_a(z) = ∏' h, complexSinc (π * z / 2 ^ h) ^ (a h)`.

The normalization is fixed once and for all by the factor written
here: `complexSinc` is the removable `sin w / w`, so the `h`-th factor
is `sin (π z / 2 ^ h) / (π z / 2 ^ h)`, which is the exponents volume's
`sinc (z / 2 ^ h)` with `sinc w = sin (π w) / (π w)`.  At `a h = 1`
this is `rvachevFourierProduct` on the nose; see
`generalizedRvachevProduct_one`.

The definition is unconditional: `tprod` is `1` on families that are
not multipliable, so no admissibility hypothesis is built in.  It is
`generalizedSincFactors_multipliable` that makes the value meaningful,
and that lemma does carry the hypothesis. -/
noncomputable def generalizedRvachevProduct (a : ℕ → ℕ) (z : ℂ) : ℂ :=
  ∏' h : ℕ, complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h

/-- The shift `S` on exponent sequences, `(S a) h = a (h + 1)`.  It
deletes the coarsest dyadic layer. -/
def shiftExponent (a : ℕ → ℕ) (h : ℕ) : ℕ := a (h + 1)

/-- The defining equation of the shift, as a rewrite rule. -/
@[simp] theorem shiftExponent_apply (a : ℕ → ℕ) (h : ℕ) :
    shiftExponent a h = a (h + 1) := rfl

/-- For a `ℕ`-valued weight sequence the admissibility hypothesis used
throughout this file coincides with the absolute-value spelling
`Summable fun h => |a h| / 2 ^ h` that `DigitDefectCounting` uses for
real weight sequences: the absolute value is redundant on
nonnegative casts. -/
theorem summable_natCast_div_two_pow_iff (a : ℕ → ℕ) :
    (Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) ↔
      Summable fun h : ℕ => |(a h : ℝ)| / 2 ^ h := by
  have habs : ∀ h : ℕ,
      (a h : ℝ) / 2 ^ h = |(a h : ℝ)| / 2 ^ h := by
    intro h
    rw [abs_of_nonneg (Nat.cast_nonneg (a h) : (0 : ℝ) ≤ (a h : ℝ))]
  exact summable_congr habs

/-- `exp t - 1 ≤ t · exp t` for **every** real `t`.

Multiplying `1 - t ≤ exp (-t)` through by the positive number `exp t`
turns the right-hand side into `1`.  Only the case `t ≥ 0` is used
below, but the inequality needs no sign hypothesis. -/
theorem exp_sub_one_le_mul_exp (t : ℝ) :
    Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
  have h2 : (-t + 1) * Real.exp t ≤ Real.exp (-t) * Real.exp t :=
    mul_le_mul_of_nonneg_right h hpos.le
  have h3 : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  rw [h3] at h2
  have h4 : (-t + 1) * Real.exp t =
      Real.exp t - t * Real.exp t := by ring
  rw [h4] at h2
  linarith

/-- **Power deviation bound**: `‖(1 + y) ^ n - 1‖ ≤ exp (n ‖y‖) - 1`.

This is Mathlib's `Finset.norm_prod_one_add_sub_one_le` applied to the
constant family `fun _ => y` on `Finset.range n`, where the finite
product is `(1 + y) ^ n` and the finite sum of norms is `n · ‖y‖`.
It is the estimate that lets a *raised* sinc factor be compared with
the unraised one at the cost of a single factor `a h`. -/
theorem norm_one_add_pow_sub_one_le (y : ℂ) (n : ℕ) :
    ‖(1 + y) ^ n - 1‖ ≤ Real.exp ((n : ℝ) * ‖y‖) - 1 := by
  simpa only [Finset.prod_const, Finset.card_range, Finset.sum_const,
    nsmul_eq_mul] using
    Finset.norm_prod_one_add_sub_one_le (Finset.range n)
      (fun _ : ℕ => y)

/-- Comparison test in the shape produced by
`norm_one_add_pow_sub_one_le`: if the nonnegative sequence `v` is
summable and `‖x n‖ ≤ exp (v n) - 1` for every `n`, then `‖x ·‖` is
summable.

The two steps are `exp t - 1 ≤ t · exp t` and the fact that a summable
nonnegative sequence is bounded termwise by its own sum, so the
factor `exp (v n)` is bounded by the constant `exp (∑' v)`.

The index type is arbitrary: both ingredients
(`Summable.of_nonneg_of_le` and `Summable.le_tsum`) are
index-generic, and the double-index case is needed downstream by
`FabiusFunction.GeneralizedCanonicalForm`. -/
theorem summable_norm_of_norm_le_exp_sub_one
    {ι : Type*} {v : ι → ℝ} {x : ι → ℂ} (hv : Summable v)
    (h0 : ∀ n, 0 ≤ v n)
    (hx : ∀ n, ‖x n‖ ≤ Real.exp (v n) - 1) :
    Summable fun n => ‖x n‖ := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_
    (hv.mul_right (Real.exp (∑' m, v m)))
  intro n
  have hle : v n ≤ ∑' m, v m := hv.le_tsum n fun m _ => h0 m
  calc ‖x n‖ ≤ Real.exp (v n) - 1 := hx n
    _ ≤ v n * Real.exp (v n) := exp_sub_one_le_mul_exp (v n)
    _ ≤ v n * Real.exp (∑' m, v m) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle) (h0 n)

/-- **The weighted factor-deviation series converges.**  Under
admissibility,

`∑_h a h · ‖complexSinc (π z / 2 ^ h) - 1‖ < ∞`.

Near the origin `complexSinc w - 1 = O(w)` (`complexSinc_sub_one_isBigO`
in `FourierProduct`), and the arguments `π z / 2 ^ h` tend to `0`, so
the `h`-th deviation is eventually at most `C π ‖z‖ / 2 ^ h`; the
admissibility hypothesis then dominates the weighted series. -/
theorem summable_natCast_mul_norm_sincFactor_sub_one
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Summable fun h : ℕ => (a h : ℝ) *
      ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖ := by
  obtain ⟨C, hC0⟩ := complexSinc_sub_one_isBigO.bound
  have hC : ∀ᶠ w : ℂ in nhds 0,
      ‖complexSinc w - 1‖ ≤ C * ‖w‖ := hC0
  have harg : Tendsto (fun h : ℕ => (Real.pi : ℂ) * z / (2 : ℂ) ^ h)
      atTop (nhds 0) := by
    have hpow : Tendsto (fun h : ℕ => ((2 : ℂ)⁻¹) ^ h) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    simpa [div_eq_mul_inv, inv_pow] using
      hpow.const_mul ((Real.pi : ℂ) * z)
  have hev : ∀ᶠ h : ℕ in atTop,
      ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖ ≤
        C * ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖ := by
    filter_upwards [harg.eventually hC] with h hh
    exact hh
  have hnw : ∀ h : ℕ,
      ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖ = Real.pi * ‖z‖ / 2 ^ h := by
    intro h
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_two]
  have hbound : ∀ᶠ h : ℕ in atTop,
      ‖(a h : ℝ) *
          ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖‖ ≤
        C * (Real.pi * ‖z‖) * ((a h : ℝ) / 2 ^ h) := by
    filter_upwards [hev] with h hh
    have hnn : (0 : ℝ) ≤ (a h : ℝ) *
        ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖ :=
      mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc (a h : ℝ) *
          ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1‖
        ≤ (a h : ℝ) * (C * ‖(Real.pi : ℂ) * z / (2 : ℂ) ^ h‖) :=
          mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
      _ = C * (Real.pi * ‖z‖) * ((a h : ℝ) / 2 ^ h) := by
          rw [hnw h]
          ring
  exact Summable.of_norm_bounded_eventually_nat
    (ha.mul_left (C * (Real.pi * ‖z‖))) hbound

/-- **Absolute summability of the raised factor deviations.**  Under
admissibility the series

`∑_h ‖complexSinc (π z / 2 ^ h) ^ (a h) - 1‖`

converges.  This is the quantitative statement behind the
multipliability of the generalized product. -/
theorem summable_norm_generalizedSincFactor_sub_one
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Summable fun h : ℕ =>
      ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1‖ := by
  refine summable_norm_of_norm_le_exp_sub_one
    (summable_natCast_mul_norm_sincFactor_sub_one a ha z)
    (fun h => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) ?_
  intro h
  have hy : (1 : ℂ) +
      (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1) =
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) := by ring
  have hb := norm_one_add_pow_sub_one_le
    (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) - 1) (a h)
  rwa [hy] at hb

/-- The raised factor deviations form a summable complex series. -/
theorem summable_generalizedSincFactor_sub_one
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Summable fun h : ℕ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1 :=
  Summable.of_norm
    (summable_norm_generalizedSincFactor_sub_one a ha z)

/-- **Convergence of the generalized Rvachev product.**  For every
admissible exponent sequence and every `z : ℂ` the raised sinc factors
are `Multipliable`.

As for the classical product (`Fabius.sincFactors_multipliable`) this
holds at *every* point of the plane, the zeros included: Mathlib's
`Multipliable` is unconditional convergence of the net of finite
subproducts and permits the limit `0`, so no factor has to be nonzero.
Nothing uniform in `z` is claimed. -/
theorem generalizedSincFactors_multipliable
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    Multipliable fun h : ℕ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h := by
  have hp := Complex.multipliable_one_add_of_summable
    (summable_generalizedSincFactor_sub_one a ha z)
  convert hp using 1
  funext h
  ring

/-- **Classical recovery**, the normalization test: the constant
exponent sequence `a h = 1` returns Rvachev's Fourier product exactly.
If this were not an identity the normalization chosen in
`generalizedRvachevProduct` would be wrong. -/
theorem generalizedRvachevProduct_one (z : ℂ) :
    generalizedRvachevProduct (fun _ => 1) z =
      rvachevFourierProduct z := by
  unfold generalizedRvachevProduct rvachevFourierProduct
  refine tprod_congr fun h => ?_
  exact pow_one _

/-- The zero exponent sequence gives the constant function `1`. -/
theorem generalizedRvachevProduct_zero_exponent (z : ℂ) :
    generalizedRvachevProduct (fun _ => 0) z = 1 := by
  unfold generalizedRvachevProduct
  simp

/-- Every generalized Rvachev transform is normalized to `1` at the
origin: each factor is `complexSinc 0 = 1`. -/
theorem generalizedRvachevProduct_at_zero (a : ℕ → ℕ) :
    generalizedRvachevProduct a 0 = 1 := by
  unfold generalizedRvachevProduct
  simp [complexSinc]

/-- **Additivity in the exponent sequence**: `Φ_{a+b} = Φ_a · Φ_b`.

Pointwise `x ^ (a h + b h) = x ^ (a h) · x ^ (b h)`, and both factor
families are multipliable, so the two infinite products may be
combined.  This is the multiplicative half of the convolution-monoid
statement of the volume; the accompanying statement about convolution
of probability laws is not formalized here. -/
theorem generalizedRvachevProduct_add
    (a b : ℕ → ℕ)
    (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (hb : Summable fun h : ℕ => (b h : ℝ) / 2 ^ h)
    (z : ℂ) :
    generalizedRvachevProduct (a + b) z =
      generalizedRvachevProduct a z *
        generalizedRvachevProduct b z := by
  have h1 := generalizedSincFactors_multipliable a ha z
  have h2 := generalizedSincFactors_multipliable b hb z
  have hpt : ∀ h : ℕ,
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ (a + b) h =
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h *
          complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ b h := by
    intro h
    simp only [Pi.add_apply, pow_add]
  unfold generalizedRvachevProduct
  calc ∏' h : ℕ,
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ (a + b) h
      = ∏' h : ℕ,
          (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h *
            complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ b h) :=
        tprod_congr hpt
    _ = _ := h1.tprod_mul h2

/-- **Finitely supported exponents give a finite product.**  If `a`
vanishes off the finite set `s`, then

`Φ_a(z) = ∏ h ∈ s, complexSinc (π z / 2 ^ h) ^ (a h)`.

No admissibility hypothesis is needed: off `s` every factor is
`x ^ 0 = 1`.  This is the base case of the whole theory, and the
volume's "finite uniform box spline" regime. -/
theorem generalizedRvachevProduct_eq_prod (a : ℕ → ℕ) (z : ℂ)
    {s : Finset ℕ} (hs : ∀ h ∉ s, a h = 0) :
    generalizedRvachevProduct a z =
      ∏ h ∈ s,
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h := by
  unfold generalizedRvachevProduct
  refine tprod_eq_prod fun h hh => ?_
  show complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h = 1
  rw [hs h hh, pow_zero]

/-- **The zeros of a single scale-`h` factor.**  The `h`-th factor
`complexSinc (π z / 2 ^ h)` vanishes exactly at the nonzero integer
multiples of `2 ^ h`.

This is `complexSinc_eq_zero_iff` transported through the argument
change `w = π z / 2 ^ h`: the condition `w = k π` becomes
`z = k · 2 ^ h`, and `w ≠ 0` becomes `k ≠ 0`. -/
theorem complexSinc_pi_div_two_pow_eq_zero_iff (z : ℂ) (h : ℕ) :
    complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) = 0 ↔
      ∃ k : ℤ, k ≠ 0 ∧ z = (k : ℂ) * (2 : ℂ) ^ h := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have htwo : (2 : ℂ) ^ h ≠ 0 := pow_ne_zero h (by norm_num)
  rw [complexSinc_eq_zero_iff]
  constructor
  · rintro ⟨hw0, k, hk⟩
    have hmul : (Real.pi : ℂ) * z =
        ((k : ℂ) * Real.pi) * (2 : ℂ) ^ h := (div_eq_iff htwo).mp hk
    have hz : z = (k : ℂ) * (2 : ℂ) ^ h := by
      apply mul_left_cancel₀ hpi
      calc (Real.pi : ℂ) * z
          = ((k : ℂ) * Real.pi) * (2 : ℂ) ^ h := hmul
        _ = (Real.pi : ℂ) * ((k : ℂ) * (2 : ℂ) ^ h) := by ring
    refine ⟨k, ?_, hz⟩
    intro hk0
    apply hw0
    rw [hk, hk0]
    simp
  · rintro ⟨k, hk0, rfl⟩
    have hkc : (k : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hk0
    have harg : (Real.pi : ℂ) * ((k : ℂ) * (2 : ℂ) ^ h) /
        (2 : ℂ) ^ h = (k : ℂ) * Real.pi := by
      rw [div_eq_iff htwo]
      ring
    refine ⟨?_, k, harg⟩
    rw [harg]
    exact mul_ne_zero hkc hpi

/-- A single vanishing factor carrying a nonzero exponent annihilates
the whole product.  No admissibility hypothesis is needed: a `tprod`
with a zero factor is `0`. -/
theorem generalizedRvachevProduct_eq_zero_of_factor
    (a : ℕ → ℕ) (z : ℂ) (h : ℕ) (hah : a h ≠ 0)
    (hfac : complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) = 0) :
    generalizedRvachevProduct a z = 0 := by
  unfold generalizedRvachevProduct
  refine tprod_of_exists_eq_zero ⟨h, ?_⟩
  show complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h = 0
  rw [hfac, zero_pow hah]

/-- **No hidden zeros.**  If no raised factor vanishes then the
generalized product does not vanish either.

Absolute summability of the factor deviations
(`summable_norm_generalizedSincFactor_sub_one`) is exactly the
hypothesis of Mathlib's `tprod_one_add_ne_zero_of_summable`, so the
tail of the product cannot conspire to reach `0`. -/
theorem generalizedRvachevProduct_ne_zero
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ)
    (hne : ∀ h : ℕ,
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h ≠ 0) :
    generalizedRvachevProduct a z ≠ 0 := by
  unfold generalizedRvachevProduct
  have hsum : Summable fun h : ℕ =>
      ‖complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1‖ :=
    summable_norm_generalizedSincFactor_sub_one a ha z
  have hprod := tprod_one_add_ne_zero_of_summable
    (f := fun h : ℕ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1)
    (fun h => by
      have hx : (1 : ℂ) +
          (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1)
          = complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h := by
        ring
      rw [hx]
      exact hne h) hsum
  have hbody : (fun h : ℕ => (1 : ℂ) +
      (complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h - 1))
      = fun h : ℕ =>
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^ a h := by
    funext h
    ring
  rwa [hbody] at hprod

/-- **The zero set of the generalized Rvachev transform.**  For an
admissible exponent sequence,

`Φ_a(z) = 0` ↔ `z = k · 2 ^ h` for some `h` with `a h ≠ 0` and some
nonzero integer `k`.

At `a h = 1` the right-hand side describes the same subset of `ℂ` as
`rvachevFourierProduct_eq_zero_iff` does — `h = 0` produces every
nonzero integer, and conversely every `k · 2 ^ h` with `k ≠ 0` is a
nonzero integer — but that
identification of the two descriptions is not carried out here, and
the multiplicity of each zero is not computed here either.

Both are carried out downstream, at general weight, in
`FabiusFunction.GeneralizedZeroDivisor`: the arithmetic form of the
zero set is `generalizedRvachevProduct_eq_zero_iff_int`
(`Φ_a(z) = 0 ↔ ∃ n ≠ 0, z = n ∧ m_a(|n|) ≠ 0`) and the multiplicity
is `analyticOrderAt_generalizedRvachevProduct_int`. -/
theorem generalizedRvachevProduct_eq_zero_iff
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    generalizedRvachevProduct a z = 0 ↔
      ∃ h : ℕ, a h ≠ 0 ∧
        ∃ k : ℤ, k ≠ 0 ∧ z = (k : ℂ) * (2 : ℂ) ^ h := by
  constructor
  · intro hzero
    by_contra hcon
    refine generalizedRvachevProduct_ne_zero a ha z ?_ hzero
    intro h
    by_cases hah : a h = 0
    · rw [hah, pow_zero]
      exact one_ne_zero
    · refine pow_ne_zero _ ?_
      intro hfac
      obtain ⟨k, hk0, hzk⟩ :=
        (complexSinc_pi_div_two_pow_eq_zero_iff z h).mp hfac
      exact hcon ⟨h, hah, k, hk0, hzk⟩
  · rintro ⟨h, hah, k, hk0, hzk⟩
    exact generalizedRvachevProduct_eq_zero_of_factor a z h hah
      ((complexSinc_pi_div_two_pow_eq_zero_iff z h).mpr
        ⟨k, hk0, hzk⟩)

/-- Admissibility is inherited by the shift: renumbering after deleting
the coarsest layer doubles every remaining term, and the doubled tail
of a convergent series converges.  The termwise identity
`2 · a (h+1) / 2 ^ (h+1) = (S a) h / 2 ^ h` is what the proof uses; the
corresponding identity between the *sums* `A_{S a}(1/2)` and
`A_a(1/2)` is not stated here. -/
theorem summable_shiftExponent
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h) :
    Summable fun h : ℕ => (shiftExponent a h : ℝ) / 2 ^ h := by
  have h1 : Summable fun h : ℕ => (a (h + 1) : ℝ) / 2 ^ (h + 1) :=
    (summable_nat_add_iff
      (f := fun h : ℕ => (a h : ℝ) / 2 ^ h) 1).mpr ha
  have h2 : Summable fun h : ℕ =>
      2 * ((a (h + 1) : ℝ) / 2 ^ (h + 1)) := h1.mul_left 2
  have hpt : ∀ h : ℕ, 2 * ((a (h + 1) : ℝ) / 2 ^ (h + 1)) =
      (shiftExponent a h : ℝ) / 2 ^ h := by
    intro h
    rw [shiftExponent_apply, pow_succ, ← div_div]
    ring
  exact h2.congr hpt

/-- **Shift-refinement law**: dilating the argument by `2` peels off
the coarsest factor,

`Φ_a(2z) = complexSinc (π · 2z) ^ (a 0) · Φ_{S a}(z)`.

This is the general-exponent form of
`Fabius.rvachevFourierProduct_two_mul`.  The scale bookkeeping
`2 · z / 2 ^ (h+1) = z / 2 ^ h` is `Fabius.geom_scale_arg`; the peeling
of the zeroth factor is Mathlib's `tprod_eq_zero_mul'`, whose
multipliability hypothesis is supplied by
`generalizedSincFactors_multipliable` for the shifted sequence.

Only the one-step law is proved in this module.  Its full iterated form
`Φ_a(2^m z)` is proved downstream as
`Fabius.generalizedRvachevProduct_two_pow_mul` in
`FabiusFunction.WeightLinearityProducts`.  The same downstream module
also proves the finite-difference factorization of `Φ_{S^m a}` as
`generalizedRvachevProduct_shift_factorization`, wherever the
differences it uses are nonnegative — which is where both sides are
defined, `Φ` accepting only `ℕ`-valued weights. -/
theorem generalizedRvachevProduct_two_mul
    (a : ℕ → ℕ) (ha : Summable fun h : ℕ => (a h : ℝ) / 2 ^ h)
    (z : ℂ) :
    generalizedRvachevProduct a (2 * z) =
      complexSinc ((Real.pi : ℂ) * (2 * z)) ^ a 0 *
        generalizedRvachevProduct (shiftExponent a) z := by
  have hkey : ∀ h : ℕ,
      complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ (h + 1)) ^
          a (h + 1) =
        complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^
          shiftExponent a h := by
    intro h
    have he : (Real.pi : ℂ) * (2 * z) =
        (2 : ℂ) ^ 1 * ((Real.pi : ℂ) * z) := by ring
    have hg := geom_scale_arg (2 : ℂ) ((Real.pi : ℂ) * z)
      (by norm_num) 1 h
    rw [shiftExponent_apply, he, hg]
  have hshift : Multipliable fun h : ℕ =>
      complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^
        shiftExponent a h :=
    generalizedSincFactors_multipliable (shiftExponent a)
      (summable_shiftExponent a ha) z
  have hmul : Multipliable fun h : ℕ =>
      complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ (h + 1)) ^
        a (h + 1) := (multipliable_congr hkey).mpr hshift
  have hpeel : ∏' h : ℕ,
      complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ h) ^ a h =
      complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ 0) ^ a 0 *
        ∏' h : ℕ,
          complexSinc ((Real.pi : ℂ) * (2 * z) /
            (2 : ℂ) ^ (h + 1)) ^ a (h + 1) :=
    tprod_eq_zero_mul'
      (f := fun h : ℕ =>
        complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ h) ^ a h)
      hmul
  have htail : ∏' h : ℕ,
      complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ (h + 1)) ^
        a (h + 1) =
      ∏' h : ℕ, complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^
        shiftExponent a h := tprod_congr hkey
  show ∏' h : ℕ,
      complexSinc ((Real.pi : ℂ) * (2 * z) / (2 : ℂ) ^ h) ^ a h =
    complexSinc ((Real.pi : ℂ) * (2 * z)) ^ a 0 *
      ∏' h : ℕ, complexSinc ((Real.pi : ℂ) * z / (2 : ℂ) ^ h) ^
        shiftExponent a h
  rw [hpeel, htail, pow_zero, div_one]

end Fabius

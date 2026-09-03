import FabiusFunction.QuintupleProduct
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

/-!
# Theta product forms

Jacobi's three theta functions, as infinite products.  This is
`qg:prop-theta-products` of the `q`-Pochhammer monograph:

```
ϑ₃(z ∣ τ) = (q², -qζ, -q/ζ ; q²)_∞,
ϑ₄(z ∣ τ) = (q²,  qζ,  q/ζ ; q²)_∞,
ϑ₂(z ∣ τ) = q^{1/4} ζ^{1/2} (q², -q²ζ, -ζ⁻¹ ; q²)_∞,
```

with the null values `ϑ₂(0∣τ) = 2q^{1/4}(q²;q²)_∞(-q²;q²)_∞²`,
`ϑ₃(0∣τ) = (q²;q²)_∞(-q;q²)_∞²`, `ϑ₄(0∣τ) = (q²;q²)_∞(q;q²)_∞²`, under the
chapter's conventions `q = e^{πiτ}`, `ζ = e^{2πiz}`, `q^α := e^{πiατ}`,
`ζ^{1/2} := e^{πiz}`, `Im τ > 0`.

Everything is a base-`q²` specialization of Jacobi's triple product
(`hasSum_jacobi_triple_product'`).  The one computation the source compresses
into `(-1)^n (q²)^{C(n,2)} (-qζ)^n = q^{n²} ζ^n` is the exponent bookkeeping
`n² = 2·C(n,2) + n`, isolated here as `pow_sqExponent`.

## What is covered

**Layer A — the nome form**, over an arbitrary complete normed field `𝕜`,
under `‖q‖ < 1`, `q ≠ 0`, `ζ ≠ 0`.  This is strictly more general than the
source, which works over `ℂ` in the variables `(z, τ)`; it is also free of
every fractional-power convention, the factor `q^{1/4} ζ^{1/2}` simply not
occurring.

* `hasSum_pow_sqExponent_mul_zpow`:
  `∑_{n∈ℤ} q^{n²} ζⁿ = (q²;q²)_∞ (-qζ;q²)_∞ (-q/ζ;q²)_∞`  (`eq:qg-theta3-product`);
* `hasSum_neg_one_zpow_mul_pow_sqExponent_mul_zpow`:
  `∑_{n∈ℤ} (-1)ⁿ q^{n²} ζⁿ = (q²;q²)_∞ (qζ;q²)_∞ (q/ζ;q²)_∞`  (`eq:qg-theta4-product`);
* `hasSum_pow_sqAddExponent_mul_zpow`:
  `∑_{n∈ℤ} q^{n²+n} ζⁿ = (q²;q²)_∞ (-q²ζ;q²)_∞ (-ζ⁻¹;q²)_∞`  (`eq:qg-theta2-product`,
  with the prefactor `q^{1/4} ζ^{1/2}` stripped);
* `hasSum_pow_sqExponent`, `hasSum_neg_one_zpow_mul_pow_sqExponent`,
  `hasSum_pow_sqAddExponent`: the three `ζ = 1` specializations
  (`eq:qg-theta3-null`, `eq:qg-theta4-null`, `eq:qg-theta2-null`, the last
  again without the prefactor);
* `qPochhammerInfIn_neg_one`: `(-1;q)_∞ = 2(-q;q)_∞`, the peel the source
  quotes only at base `q²`;
* `bilateralTheta_sq`: the same identity in the `bilateralTheta` API.

All of Layer A is stated as `HasSum`, so it also asserts the unconditional
summability over `ℤ` that the source's `∑_{n∈ℤ}` leaves implicit.

**Layer B — the `(z, τ)` bridge over `ℂ`.**  Mathlib's `jacobiTheta₂ z τ`
*is* the source's `ϑ₃(z ∣ τ)` on the nose, so

* `jacobiTheta₂_eq_qPochhammerInfIn` is `eq:qg-theta3-product` verbatim in the
  standard parametrization, for `0 < τ.im`;
* `jacobiTheta₂_add_half_eq` gives `eq:qg-theta4-product` through
  `ϑ₄(z∣τ) = ϑ₃(z + 1/2 ∣ τ)`;
* `jacobiTheta₂_add_half_mul_eq` gives `eq:qg-theta2-product` through
  `ϑ₂(z∣τ) = q^{1/4} ζ^{1/2} · ϑ₃(z + τ/2 ∣ τ)`, again with the prefactor
  stripped: the statement is about `ϑ₃(z + τ/2 ∣ τ)`, not about a defined `ϑ₂`.

The nome `q = e^{πiτ}` and the multiplier `ζ = e^{2πiz}` are named `nome` and
`thetaZeta`.

## What is NOT covered

* There are no named `ℂ`-definitions of `ϑ₂` and `ϑ₄` carrying the prefactor
  `q^{1/4} ζ^{1/2} = e^{πiτ/4} · e^{πiz}`.  Mathlib supplies only
  `jacobiTheta₂` (`= ϑ₃`); `ϑ₂` and `ϑ₄` are reached here solely through the
  argument shifts `z + τ/2` and `z + 1/2`.  Consequently
  `eq:qg-theta2-product` and `eq:qg-theta2-null` appear with the prefactor
  stripped rather than literally present.
* Nothing is said about `τ.im ≤ 0`, where Mathlib sets `jacobiTheta₂ = 0`.
* Nothing from the neighbouring results of the chapter: the heat equation
  `qg:prop-theta-heat`, Poisson summation `qg:thm-poisson`, the Gaussian
  Fourier transform `qg:lem-gaussian-fourier`, Jacobi's imaginary
  transformation `qg:thm-jacobi-imaginary`, or the theta–eta modularity
  `qg:thm-theta-eta-modular`.  In particular the elementary Pochhammer
  relations `(-q;q²)_∞ (q;q²)_∞ = (q²;q⁴)_∞` used there are out of scope.

## Main declarations

* `sqExponent`, `sqAddExponent`, `pow_sqExponent`, `pow_sqAddExponent`.
* `hasSum_pow_sqExponent_mul_zpow`,
  `hasSum_neg_one_zpow_mul_pow_sqExponent_mul_zpow`,
  `hasSum_pow_sqAddExponent_mul_zpow`.
* `hasSum_pow_sqExponent`, `hasSum_neg_one_zpow_mul_pow_sqExponent`,
  `hasSum_pow_sqAddExponent`.
* `nome`, `thetaZeta`, `jacobiTheta₂_eq_qPochhammerInfIn`,
  `jacobiTheta₂_add_half_eq`, `jacobiTheta₂_add_half_mul_eq`.
-/

set_option autoImplicit false

open Filter Topology
open scoped Real

namespace Fabius

noncomputable section

/-! ## Exponent bookkeeping

The triple product carries the exponent `C(k,2) = k(k-1)/2` (`thetaExponent`);
the theta series carry `k²` and `k²+k`.  The two bridges below are the whole
of the source's `(-1)^n (q²)^{C(n,2)} (-qζ)^n = q^{n²} ζ^n`. -/

/-- The square exponent `k² ∈ ℕ`, defined for every integer `k`. -/
def sqExponent (k : ℤ) : ℕ := (k * k).toNat

/-- The defining property of the square exponent: `sqExponent k = k²`. -/
theorem sqExponent_cast (k : ℤ) : (sqExponent k : ℤ) = k ^ 2 := by
  unfold sqExponent
  rw [Int.toNat_of_nonneg (mul_self_nonneg k)]
  ring

/-- `k² + k ≥ 0` for every integer `k`: it is `(k+1)((k+1)-1)`. -/
theorem mul_self_add_nonneg (k : ℤ) : 0 ≤ k * k + k := by
  have h := mul_sub_one_nonneg (k + 1)
  rw [show (k + 1) * ((k + 1) - 1) = k * k + k from by ring] at h
  exact h

/-- The shifted square exponent `k² + k ∈ ℕ`, defined for every integer `k`. -/
def sqAddExponent (k : ℤ) : ℕ := (k * k + k).toNat

/-- The defining property of the shifted square exponent:
`sqAddExponent k = k² + k`. -/
theorem sqAddExponent_cast (k : ℤ) : (sqAddExponent k : ℤ) = k ^ 2 + k := by
  unfold sqAddExponent
  rw [Int.toNat_of_nonneg (mul_self_add_nonneg k)]
  ring

section NomeForm

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The exponent bridge** `n² = 2·C(n,2) + n`, in multiplicative form:
`q^{n²} = (q²)^{C(n,2)} · qⁿ`.  This is the computation the source displays as
`(-1)^n (q²)^{\binom n2} (-qζ)^n = q^{n²} ζ^n`. -/
theorem pow_sqExponent {q : 𝕜} (hq0 : q ≠ 0) (k : ℤ) :
    q ^ sqExponent k = (q ^ 2) ^ thetaExponent k * q ^ k := by
  have hexp : ((sqExponent k : ℕ) : ℤ) = ((2 * thetaExponent k : ℕ) : ℤ) + k := by
    have h := two_mul_thetaExponent k
    have h2 := sqExponent_cast k
    push_cast
    linear_combination h2 - h
  rw [← pow_mul, ← zpow_natCast q (sqExponent k), ← zpow_natCast q (2 * thetaExponent k), hexp,
    zpow_add₀ hq0]

/-- `q^{n²+n} = q^{n²} · qⁿ`. -/
theorem pow_sqAddExponent {q : 𝕜} (hq0 : q ≠ 0) (k : ℤ) :
    q ^ sqAddExponent k = q ^ sqExponent k * q ^ k := by
  have hexp : ((sqAddExponent k : ℕ) : ℤ) = ((sqExponent k : ℕ) : ℤ) + k := by
    rw [sqAddExponent_cast, sqExponent_cast]
  rw [← zpow_natCast q (sqAddExponent k), ← zpow_natCast q (sqExponent k), hexp, zpow_add₀ hq0]

/-! ## The three product forms, in nome variables -/

/-- **`eq:qg-theta3-product`.**  For `‖q‖ < 1`, `q ≠ 0` and `ζ ≠ 0`,

`∑_{n ∈ ℤ} q^{n²} ζⁿ = (q²;q²)_∞ (-qζ;q²)_∞ (-q/ζ;q²)_∞`,

that is `ϑ₃(z∣τ) = (q², -qζ, -q/ζ ; q²)_∞`.  Jacobi's triple product at base
`q²` and argument `qζ`. -/
theorem hasSum_pow_sqExponent_mul_zpow {q ζ : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hζ : ζ ≠ 0) :
    HasSum (fun n : ℤ => q ^ sqExponent n * ζ ^ n)
      (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q * ζ)) (q ^ 2) *
        qPochhammerInfIn (-(q / ζ)) (q ^ 2)) := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have h := hasSum_jacobi_triple_product' (q := q ^ 2) hq2 (mul_ne_zero hq0 hζ)
  have harg : q ^ 2 / (q * ζ) = q / ζ := by
    rw [pow_two]
    exact mul_div_mul_left q ζ hq0
  rw [harg] at h
  have hval : qPochhammerInfIn (-(q * ζ)) (q ^ 2) * qPochhammerInfIn (-(q / ζ)) (q ^ 2) *
      qPochhammerInfIn (q ^ 2) (q ^ 2) =
      qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q * ζ)) (q ^ 2) *
        qPochhammerInfIn (-(q / ζ)) (q ^ 2) := by
    ring
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [pow_sqExponent hq0, mul_zpow]
  ring

/-- The same identity in the `bilateralTheta` API of `ThetaQuasiPeriodicity`:
`θ_{q²}(qζ) = (q²;q²)_∞ (-qζ;q²)_∞ (-q/ζ;q²)_∞`. -/
theorem bilateralTheta_sq {q ζ : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hζ : ζ ≠ 0) :
    bilateralTheta (q ^ 2) (q * ζ) =
      qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q * ζ)) (q ^ 2) *
        qPochhammerInfIn (-(q / ζ)) (q ^ 2) := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have h := hasSum_bilateralTheta hq2 (mul_ne_zero hq0 hζ)
  refine h.unique ((hasSum_pow_sqExponent_mul_zpow hq hq0 hζ).congr_fun fun n => ?_)
  rw [pow_sqExponent hq0, mul_zpow]
  ring

/-- **`eq:qg-theta4-product`.**  For `‖q‖ < 1`, `q ≠ 0` and `ζ ≠ 0`,

`∑_{n ∈ ℤ} (-1)ⁿ q^{n²} ζⁿ = (q²;q²)_∞ (qζ;q²)_∞ (q/ζ;q²)_∞`,

that is `ϑ₄(z∣τ) = (q², qζ, q/ζ ; q²)_∞`.  The previous identity at `-ζ`. -/
theorem hasSum_neg_one_zpow_mul_pow_sqExponent_mul_zpow {q ζ : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0)
    (hζ : ζ ≠ 0) :
    HasSum (fun n : ℤ => (-1 : 𝕜) ^ n * q ^ sqExponent n * ζ ^ n)
      (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (q * ζ) (q ^ 2) *
        qPochhammerInfIn (q / ζ) (q ^ 2)) := by
  have h := hasSum_pow_sqExponent_mul_zpow hq hq0 (neg_ne_zero.mpr hζ)
  have hval : qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q * -ζ)) (q ^ 2) *
      qPochhammerInfIn (-(q / -ζ)) (q ^ 2) =
      qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (q * ζ) (q ^ 2) *
        qPochhammerInfIn (q / ζ) (q ^ 2) := by
    rw [mul_neg, div_neg, neg_neg, neg_neg]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [neg_eq_neg_one_mul ζ, mul_zpow]
  ring

/-- **`eq:qg-theta2-product`**, with the prefactor `q^{1/4} ζ^{1/2}` stripped.
For `‖q‖ < 1`, `q ≠ 0` and `ζ ≠ 0`,

`∑_{n ∈ ℤ} q^{n²+n} ζⁿ = (q²;q²)_∞ (-q²ζ;q²)_∞ (-ζ⁻¹;q²)_∞`.

The source states `ϑ₂(z∣τ) = q^{1/4} ζ^{1/2} (q², -q²ζ, -ζ⁻¹ ; q²)_∞`, and its
proof passes through exactly this bilateral sum,
`ϑ₂(z∣τ) = q^{1/4} ζ^{1/2} ∑_{n∈ℤ} q^{n(n+1)} ζⁿ`.  Obtained from
`hasSum_pow_sqExponent_mul_zpow` at `qζ`. -/
theorem hasSum_pow_sqAddExponent_mul_zpow {q ζ : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (hζ : ζ ≠ 0) :
    HasSum (fun n : ℤ => q ^ sqAddExponent n * ζ ^ n)
      (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q ^ 2 * ζ)) (q ^ 2) *
        qPochhammerInfIn (-ζ⁻¹) (q ^ 2)) := by
  have h := hasSum_pow_sqExponent_mul_zpow hq hq0 (mul_ne_zero hq0 hζ)
  have hval : qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q * (q * ζ))) (q ^ 2) *
      qPochhammerInfIn (-(q / (q * ζ))) (q ^ 2) =
      qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q ^ 2 * ζ)) (q ^ 2) *
        qPochhammerInfIn (-ζ⁻¹) (q ^ 2) := by
    rw [show q * (q * ζ) = q ^ 2 * ζ from by ring, div_mul_cancel_left₀ hq0 ζ]
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [pow_sqAddExponent hq0, mul_zpow]
  ring

/-! ## The null values `ζ = 1` -/

/-- `(-1;q)_∞ = 2 (-q;q)_∞`: peeling the first factor `1 - (-1) = 2`.  The
source uses this only at base `q²`; it holds at every contracting base. -/
theorem qPochhammerInfIn_neg_one {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn (-1 : 𝕜) q = 2 * qPochhammerInfIn (-q) q := by
  rw [qPochhammerInfIn_succ_shift (-1 : 𝕜) hq, neg_one_mul]
  norm_num

/-- **`eq:qg-theta3-null`.**  `∑_{n ∈ ℤ} q^{n²} = (q²;q²)_∞ (-q;q²)_∞²`, that
is `ϑ₃(0∣τ) = (q²;q²)_∞ (-q;q²)_∞²`. -/
theorem hasSum_pow_sqExponent {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun n : ℤ => q ^ sqExponent n)
      (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-q) (q ^ 2) ^ 2) := by
  have h := hasSum_pow_sqExponent_mul_zpow (q := q) (ζ := 1) hq hq0 one_ne_zero
  have hval : qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q * 1)) (q ^ 2) *
      qPochhammerInfIn (-(q / 1)) (q ^ 2) =
      qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-q) (q ^ 2) ^ 2 := by
    rw [mul_one, div_one]
    ring
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [one_zpow, mul_one]

/-- **`eq:qg-theta4-null`.**  `∑_{n ∈ ℤ} (-1)ⁿ q^{n²} = (q²;q²)_∞ (q;q²)_∞²`,
that is `ϑ₄(0∣τ) = (q²;q²)_∞ (q;q²)_∞²`. -/
theorem hasSum_neg_one_zpow_mul_pow_sqExponent {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun n : ℤ => (-1 : 𝕜) ^ n * q ^ sqExponent n)
      (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn q (q ^ 2) ^ 2) := by
  have h := hasSum_neg_one_zpow_mul_pow_sqExponent_mul_zpow (q := q) (ζ := 1) hq hq0 one_ne_zero
  have hval : qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (q * 1) (q ^ 2) *
      qPochhammerInfIn (q / 1) (q ^ 2) =
      qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn q (q ^ 2) ^ 2 := by
    rw [mul_one, div_one]
    ring
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [one_zpow, mul_one]

/-- **`eq:qg-theta2-null`**, with the prefactor `q^{1/4}` stripped:
`∑_{n ∈ ℤ} q^{n²+n} = 2 (q²;q²)_∞ (-q²;q²)_∞²`.  The source states
`ϑ₂(0∣τ) = 2 q^{1/4} (q²;q²)_∞ (-q²;q²)_∞²`; the factor `2` is
`(-1;q²)_∞ = 2(-q²;q²)_∞`. -/
theorem hasSum_pow_sqAddExponent {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    HasSum (fun n : ℤ => q ^ sqAddExponent n)
      (2 * (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q ^ 2)) (q ^ 2) ^ 2)) := by
  have hq2 : ‖q ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have h := hasSum_pow_sqAddExponent_mul_zpow (q := q) (ζ := 1) hq hq0 one_ne_zero
  have hval : qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q ^ 2 * 1)) (q ^ 2) *
      qPochhammerInfIn (-(1 : 𝕜)⁻¹) (q ^ 2) =
      2 * (qPochhammerInfIn (q ^ 2) (q ^ 2) * qPochhammerInfIn (-(q ^ 2)) (q ^ 2) ^ 2) := by
    rw [mul_one, inv_one, qPochhammerInfIn_neg_one hq2]
    ring
  rw [hval] at h
  refine h.congr_fun fun n => ?_
  rw [one_zpow, mul_one]

end NomeForm

/-! ## The bridge to Mathlib's two-variable Jacobi theta function

Mathlib's `jacobiTheta₂ z τ = ∑'_{n∈ℤ} exp(2πinz + πin²τ)` is exactly the
source's `ϑ₃(z ∣ τ)`, so the identities above become the displayed formulas of
`qg:prop-theta-products` in the standard `(z, τ)` parametrization.  `ϑ₄` and
`ϑ₂` are reached through the shifts `ϑ₄(z∣τ) = ϑ₃(z + 1/2 ∣ τ)` and
`ϑ₂(z∣τ) = q^{1/4} ζ^{1/2} ϑ₃(z + τ/2 ∣ τ)`; the prefactor of the latter is
not carried by any definition here. -/

section ComplexBridge

/-- The nome `q = e^{πiτ}` of the chapter's conventions. -/
def nome (τ : ℂ) : ℂ := Complex.exp ((π : ℂ) * Complex.I * τ)

/-- The multiplier `ζ = e^{2πiz}` of the chapter's conventions. -/
def thetaZeta (z : ℂ) : ℂ := Complex.exp (2 * (π : ℂ) * Complex.I * z)

/-- The nome never vanishes. -/
theorem nome_ne_zero (τ : ℂ) : nome τ ≠ 0 := by
  unfold nome
  exact Complex.exp_ne_zero _

/-- The multiplier never vanishes. -/
theorem thetaZeta_ne_zero (z : ℂ) : thetaZeta z ≠ 0 := by
  unfold thetaZeta
  exact Complex.exp_ne_zero _

/-- In the upper half plane the nome is a strict contraction:
`‖q‖ = e^{-π Im τ} < 1`. -/
theorem norm_nome_lt_one {τ : ℂ} (hτ : 0 < τ.im) : ‖nome τ‖ < 1 := by
  have hre : ((π : ℂ) * Complex.I * τ).re = -(π * τ.im) := by
    rw [show ((π : ℂ) * Complex.I * τ) = ((π : ℂ) * τ) * Complex.I from by ring,
      Complex.mul_I_re, Complex.im_ofReal_mul]
  unfold nome
  rw [Complex.norm_exp, hre, Real.exp_lt_one_iff]
  have hpos : 0 < π * τ.im := mul_pos Real.pi_pos hτ
  linarith

/-- The half-period shift negates the multiplier: `e^{2πi(z + 1/2)} = -ζ`. -/
theorem thetaZeta_add_half (z : ℂ) : thetaZeta (z + 1 / 2) = -thetaZeta z := by
  unfold thetaZeta
  rw [show (2 : ℂ) * (π : ℂ) * Complex.I * (z + 1 / 2) =
      2 * (π : ℂ) * Complex.I * z + (π : ℂ) * Complex.I from by ring,
    Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]

/-- The quasi-period shift multiplies the multiplier by the nome:
`e^{2πi(z + τ/2)} = ζ q`. -/
theorem thetaZeta_add_half_mul (z τ : ℂ) : thetaZeta (z + τ / 2) = thetaZeta z * nome τ := by
  unfold thetaZeta nome
  rw [show (2 : ℂ) * (π : ℂ) * Complex.I * (z + τ / 2) =
      2 * (π : ℂ) * Complex.I * z + (π : ℂ) * Complex.I * τ from by ring, Complex.exp_add]

/-- Mathlib's theta summand in nome variables: `e^{2πinz + πin²τ} = q^{n²} ζⁿ`. -/
theorem jacobiTheta₂_term_eq (n : ℤ) (z τ : ℂ) :
    jacobiTheta₂_term n z τ = nome τ ^ sqExponent n * thetaZeta z ^ n := by
  unfold nome thetaZeta
  have key : jacobiTheta₂_term n z τ =
      Complex.exp (((n ^ 2 : ℤ) : ℂ) * ((π : ℂ) * Complex.I * τ)) *
        Complex.exp ((n : ℂ) * (2 * (π : ℂ) * Complex.I * z)) := by
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [key, Complex.exp_int_mul, Complex.exp_int_mul,
    ← zpow_natCast (Complex.exp ((π : ℂ) * Complex.I * τ)) (sqExponent n), sqExponent_cast]

/-- **`eq:qg-theta3-product` in the `(z, τ)` parametrization.**  For
`0 < Im τ`, with `q = e^{πiτ}` and `ζ = e^{2πiz}`,

`ϑ₃(z ∣ τ) = (q²;q²)_∞ (-qζ;q²)_∞ (-q/ζ;q²)_∞`,

where `ϑ₃` is Mathlib's `jacobiTheta₂`. -/
theorem jacobiTheta₂_eq_qPochhammerInfIn (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ z τ =
      qPochhammerInfIn (nome τ ^ 2) (nome τ ^ 2) *
        qPochhammerInfIn (-(nome τ * thetaZeta z)) (nome τ ^ 2) *
        qPochhammerInfIn (-(nome τ / thetaZeta z)) (nome τ ^ 2) := by
  have hs : HasSum (fun n : ℤ => nome τ ^ sqExponent n * thetaZeta z ^ n) (jacobiTheta₂ z τ) :=
    (hasSum_jacobiTheta₂_term z hτ).congr_fun fun n => (jacobiTheta₂_term_eq n z τ).symm
  exact hs.unique
    (hasSum_pow_sqExponent_mul_zpow (norm_nome_lt_one hτ) (nome_ne_zero τ) (thetaZeta_ne_zero z))

/-- **`eq:qg-theta4-product` in the `(z, τ)` parametrization.**  Since
`ϑ₄(z ∣ τ) = ϑ₃(z + 1/2 ∣ τ)`, for `0 < Im τ`,

`ϑ₄(z ∣ τ) = (q²;q²)_∞ (qζ;q²)_∞ (q/ζ;q²)_∞`. -/
theorem jacobiTheta₂_add_half_eq (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (z + 1 / 2) τ =
      qPochhammerInfIn (nome τ ^ 2) (nome τ ^ 2) *
        qPochhammerInfIn (nome τ * thetaZeta z) (nome τ ^ 2) *
        qPochhammerInfIn (nome τ / thetaZeta z) (nome τ ^ 2) := by
  rw [jacobiTheta₂_eq_qPochhammerInfIn (z + 1 / 2) hτ, thetaZeta_add_half, mul_neg, div_neg,
    neg_neg, neg_neg]

/-- **`eq:qg-theta2-product` in the `(z, τ)` parametrization**, with the
prefactor `q^{1/4} ζ^{1/2} = e^{πiτ/4} e^{πiz}` stripped.  Since
`ϑ₂(z ∣ τ) = q^{1/4} ζ^{1/2} · ϑ₃(z + τ/2 ∣ τ)`, for `0 < Im τ`,

`ϑ₃(z + τ/2 ∣ τ) = (q²;q²)_∞ (-q²ζ;q²)_∞ (-ζ⁻¹;q²)_∞`. -/
theorem jacobiTheta₂_add_half_mul_eq (z : ℂ) {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta₂ (z + τ / 2) τ =
      qPochhammerInfIn (nome τ ^ 2) (nome τ ^ 2) *
        qPochhammerInfIn (-(nome τ ^ 2 * thetaZeta z)) (nome τ ^ 2) *
        qPochhammerInfIn (-(thetaZeta z)⁻¹) (nome τ ^ 2) := by
  have h1 : nome τ * (thetaZeta z * nome τ) = nome τ ^ 2 * thetaZeta z := by ring
  have h2 : nome τ / (thetaZeta z * nome τ) = (thetaZeta z)⁻¹ := by
    rw [mul_comm]
    exact div_mul_cancel_left₀ (nome_ne_zero τ) (thetaZeta z)
  rw [jacobiTheta₂_eq_qPochhammerInfIn (z + τ / 2) hτ, thetaZeta_add_half_mul, h1, h2]

end ComplexBridge

end

end Fabius

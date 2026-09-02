import FabiusFunction.ThetaQuasiPeriodicity
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Watson's quintuple product identity

For `‖q‖ < 1`, `q ≠ 0` and `z ≠ 0` in a complete normed field,

`(q;q)_∞ (-z;q)_∞ (-q/z;q)_∞ (qz²;q²)_∞ (q/z²;q²)_∞
    = ∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2} z^{3n} (1 + z q^n)`.

Here `(a₁,…,a_k;q)_∞` is the multi-argument symbol of the monograph, so the left side is
`qPochhammerInfIn q q * qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q *
 (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2))`,
that is `∏_{j ≥ 0} (1 - q^{j+1})(1 + z q^j)(1 + q^{j+1}/z)(1 - q z² q^{2j})(1 - (q/z²) q^{2j})`.

## The proof

Write `e(k) = k(k-1)/2` (`thetaExponent`) and `p(k) = k(3k-1)/2` (`pentagonalExponent`).
Jacobi's triple product supplies two bilateral theta series,

* `A(z) = ∑_{r ∈ ℤ} q^{e(r)} z^r = (-z;q)_∞ (-q/z;q)_∞ (q;q)_∞`, and
* `B(z) = ∑_{s ∈ ℤ} (-1)^s (q²)^{e(s)} (q z²)^s = (q z²;q²)_∞ (q/z²;q²)_∞ (q²;q²)_∞`,

both *absolutely* summable.  Hence `A(z) · B(z)` is an unconditionally summable family over
`ℤ × ℤ` (`summable_mul_of_summable_norm`), which may be regrouped at will.  Shearing the index
by `(m, s) ↦ (m - 2s, s)` (`shearEquiv`) and summing the `s`-fibre gives, for each `m`,

`∑_{s ∈ ℤ} q^{e(m-2s)} z^{m-2s} (-1)^s (q²)^{e(s)} (q z²)^s
    = q^{e(m)} z^m · θ_{q⁶}(-q^{4-2m})`   (`quintupleCoeff`, `hasSum_quintupleTerm_fiber`),

the whole double sum thus being `∑_{m ∈ ℤ} quintupleCoeff q z m` (`hasSum_quintupleCoeff`).
This replaces the TeX's appeal to "normal convergence on compact annuli permits coefficient
extraction": no uniqueness-of-Laurent-coefficients argument is used, only the fibrewise
regrouping `HasSum.prod_fiberwise` of an absolutely summable family, which is strictly stronger.

Iterated quasi-periodicity of `θ` in multiplicative form,
`θ_Q(Q^j u) · (Q^{e(j)} u^j) = θ_Q(u)` (`bilateralTheta_zpow_mul`), moves the inner theta from
`-q^{c-6n}` to `-q^{c}` at the cost of `(-1)^n q^{3n²+3n-cn}`
(`bilateralTheta_pow_six_shift`).  For `m = 3n`, `3n+1`, `3n+2` one has `c = 4`, `2`, `0`, and

* `θ_{q⁶}(-q⁴) = θ_{q⁶}(-q²) = (q²;q⁶)_∞ (q⁴;q⁶)_∞ (q⁶;q⁶)_∞ = (q²;q²)_∞`, by the
  threefold dissection `qPochhammerInfIn_two_dissection` (a lemma the TeX never displays), while
* `θ_{q⁶}(-q⁰) = θ_{q⁶}(-1) = 0`, since `-1 = -(q⁶)⁰` lies on the zero set of `θ`
  (`bilateralTheta_eq_zero_iff`).

The last point kills the classes `m ≡ 2 (mod 3)` **uniformly in `n`**, with no case split on the
sign of `n`; the TeX proof's "the product contains the factor `1 - Q⁰` after an integral
quasi-periodic shift" hides a case distinction (for `n ≥ 0` the vanishing factor sits in the
first Pochhammer symbol, for `n ≤ -1` in the second).  Regrouping `m` modulo `3` with
`Int.divModEquiv 3` and dividing by `(q²;q²)_∞ ≠ 0` finishes.

## Main declarations

* `thetaExponent_shear`: `e(m) + 6e(s) + (4-2m)s = e(m-2s) + 2e(s) + s`, the exponent identity
  behind the shear.
* `bilateralTheta_zpow_mul`: iterated quasi-periodicity `θ_q(q^j u)·(q^{e(j)} u^j) = θ_q(u)`.
* `qPochhammerInfIn_two_dissection`: `(q²;q²)_∞ = (q²;q⁶)_∞ (q⁴;q⁶)_∞ (q⁶;q⁶)_∞`.
* `bilateralTheta_pow_six_neg_two`, `bilateralTheta_pow_six_neg_four`,
  `bilateralTheta_pow_six_neg_one`: the three evaluations of the inner theta.
* `quintupleTerm`, `quintupleCoeff`, `hasSum_quintupleTerm_fiber`, `hasSum_quintupleCoeff`:
  the bilateral Laurent expansion of the quintuple product times `(q²;q²)_∞`.
* `quintupleCoeff_three_mul`, `quintupleCoeff_three_mul_add_one`,
  `quintupleCoeff_three_mul_add_two`: the three residue classes modulo `3`.
* `hasSum_quintuple_product`: the identity in its paired form, whose summand uses only
  nonnegative exponents of `q`.
* `hasSum_quintuple_product'`: the literal shape `(-1)^n q^{p(n)} z^{3n} (1 + z q^n)` of the
  monograph, and `tsum_quintuple_product`.

## Scope relative to the monograph statement

The theorem `qg:thm-quintuple-product` is covered in full, and generalised in two ways.  First,
the chapter is framed over `ℂ` ("throughout the analytic sections, `0 < |q| < 1`"), whereas every
statement here is over an arbitrary complete normed field `𝕜`, so it also covers `ℝ` and the
`p`-adic fields.  Second, the conclusion is a `HasSum`, which asserts unconditional summability of
the right-hand family in addition to its value; the TeX's `∑_{n ∈ ℤ}` leaves this implicit.

The hypothesis `q ≠ 0` is not forced by the mathematics — the identity also holds at `q = 0`,
both sides collapsing to `1 + z` — but by the available API (`hasSum_jacobi_triple_product` at
base `q²` needs `q z² ≠ 0`, and the argument `q^{4-2m}` of the inner theta needs `q ≠ 0`).  Since
the chapter assumes `0 < |q|`, this is not a gap.  The `remark` on coefficient dissection and
root-system products that follows the theorem in the TeX is an informal structural comparison and
is not formalised.
-/

set_option autoImplicit false

open Filter Topology

namespace Fabius

noncomputable section

/-! ## Exponent arithmetic

All four identities are proved by doubling and `linear_combination`, using the defining
properties `2 e(k) = k(k-1)` and `2 p(k) = k(3k-1)` of the two exponent functions. -/

/-- The shear identity `e(m) + 6 e(s) + (4-2m) s = e(m-2s) + 2 e(s) + s`.  It equates the
exponent of `q` in the `(m,s)` term of the sheared double product with the exponent produced by
the inner theta series at base `q⁶` and argument `-q^{4-2m}`. -/
theorem thetaExponent_shear (m s : ℤ) :
    (thetaExponent m : ℤ) + 6 * (thetaExponent s : ℤ) + (4 - 2 * m) * s
      = (thetaExponent (m - 2 * s) : ℤ) + 2 * (thetaExponent s : ℤ) + s := by
  have h1 := two_mul_thetaExponent m
  have h2 := two_mul_thetaExponent s
  have h3 := two_mul_thetaExponent (m - 2 * s)
  refine mul_left_cancel₀ (two_ne_zero' ℤ) ?_
  linear_combination h1 + 4 * h2 - h3

/-- `e(3n) = p(n) + (3n² + 3n - 4n)`: the exponent bookkeeping of the class `m ≡ 0 (mod 3)`. -/
theorem thetaExponent_three_mul_eq (n : ℤ) :
    (thetaExponent (n * 3) : ℤ) = (pentagonalExponent n : ℤ) + (3 * n ^ 2 + 3 * n - 4 * n) := by
  have h1 := two_mul_thetaExponent (n * 3)
  have h2 := two_mul_pentagonalExponent n
  refine mul_left_cancel₀ (two_ne_zero' ℤ) ?_
  linear_combination h1 - h2

/-- `e(3n+1) = p(-n) + (3n² + 3n - 2n)`: the exponent bookkeeping of the class
`m ≡ 1 (mod 3)`.  The TeX omits this calculation. -/
theorem thetaExponent_three_mul_add_one_eq (n : ℤ) :
    (thetaExponent (n * 3 + 1) : ℤ)
      = (pentagonalExponent (-n) : ℤ) + (3 * n ^ 2 + 3 * n - 2 * n) := by
  have h1 := two_mul_thetaExponent (n * 3 + 1)
  have h2 := two_mul_pentagonalExponent (-n)
  refine mul_left_cancel₀ (two_ne_zero' ℤ) ?_
  linear_combination h1 - h2

/-- `p(n) + n = p(-n)`: the identity that turns the paired form of the quintuple product into
the monograph's `(1 + z q^n)` form. -/
theorem pentagonalExponent_add_self_eq (n : ℤ) :
    (pentagonalExponent n : ℤ) + n = (pentagonalExponent (-n) : ℤ) := by
  have h1 := two_mul_pentagonalExponent n
  have h2 := two_mul_pentagonalExponent (-n)
  refine mul_left_cancel₀ (two_ne_zero' ℤ) ?_
  linear_combination h1 - h2

/-! ## The shear of `ℤ × ℤ` -/

/-- The shear `(m, s) ↦ (m - 2s, s)` of `ℤ × ℤ`.  Composing the double family of the product
`A(z) · B(z)` with it collects, in the fibre over `m`, exactly the terms contributing `z^m`. -/
def shearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1 - 2 * p.2, p.2)
  invFun p := (p.1 + 2 * p.2, p.2)
  left_inv := by
    rintro ⟨m, s⟩
    simp only [Prod.mk.injEq, eq_self_iff_true, and_true]
    ring
  right_inv := by
    rintro ⟨m, s⟩
    simp only [Prod.mk.injEq, eq_self_iff_true, and_true]
    ring

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
/-- A positive power of a strict contraction is a strict contraction. -/
theorem norm_pow_lt_one_of_norm_lt_one {q : 𝕜} (hq : ‖q‖ < 1) {k : ℕ} (hk : k ≠ 0) :
    ‖q ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq hk

omit [CompleteSpace 𝕜] in
/-- `(-1)^{-n} = (-1)^n` for integer `n`: both are inverse to `(-1)^n`. -/
theorem neg_one_zpow_neg (n : ℤ) : ((-1 : 𝕜)) ^ (-n) = (-1 : 𝕜) ^ n := by
  have hne1 : (-1 : 𝕜) ≠ 0 := neg_ne_zero.mpr (one_ne_zero : (1 : 𝕜) ≠ 0)
  have h : ((-1 : 𝕜)) ^ (-n) * (-1 : 𝕜) ^ n = 1 := by
    rw [← zpow_add₀ hne1, show -n + n = (0 : ℤ) by ring, zpow_zero]
  have h2 : ((-1 : 𝕜)) ^ n * (-1 : 𝕜) ^ n = 1 := by
    rw [← zpow_add₀ hne1]
    exact Even.neg_one_zpow ⟨n, rfl⟩
  exact mul_right_cancel₀ (zpow_ne_zero n hne1) (h.trans h2.symm)

/-! ## Iterated quasi-periodicity of the bilateral theta series -/

/-- **Iterated quasi-periodicity**, in multiplicative form:
`θ_q(q^j u) · (q^{e(j)} u^j) = θ_q(u)` for every integer `j`.  Stated multiplicatively so that
the induction step is pure ring algebra with no inverses left over. -/
theorem bilateralTheta_zpow_mul {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {u : 𝕜} (hu : u ≠ 0)
    (j : ℤ) :
    bilateralTheta q (q ^ j * u) * (q ^ thetaExponent j * u ^ j) = bilateralTheta q u := by
  have key : ∀ k : ℤ,
      bilateralTheta q (q ^ (k + 1) * u) * (q ^ thetaExponent (k + 1) * u ^ (k + 1))
        = bilateralTheta q (q ^ k * u) * (q ^ thetaExponent k * u ^ k) := by
    intro k
    have hne : (q : 𝕜) ^ k * u ≠ 0 := mul_ne_zero (zpow_ne_zero k hq0) hu
    have harg : (q : 𝕜) ^ (k + 1) * u = q * (q ^ k * u) := by
      rw [zpow_add_one₀ hq0]
      ring
    rw [harg, bilateralTheta_mul_left hq hq0 hne, pow_thetaExponent_add_one hq0 k,
      zpow_add_one₀ hu]
    have hre : ((q : 𝕜) ^ k * u)⁻¹ * bilateralTheta q (q ^ k * u) *
        (q ^ thetaExponent k * q ^ k * (u ^ k * u))
        = bilateralTheta q (q ^ k * u) * (q ^ thetaExponent k * u ^ k) *
          ((q ^ k * u)⁻¹ * (q ^ k * u)) := by ring
    rw [hre, inv_mul_cancel₀ hne, mul_one]
  have he0 : thetaExponent 0 = 0 := by
    have h := two_mul_thetaExponent 0
    omega
  induction j using Int.induction_on with
  | zero => simp only [zpow_zero, one_mul, he0, pow_zero, mul_one]
  | succ i ih => exact (key (i : ℤ)).trans ih
  | pred i ih =>
    have h := key (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h
    exact h.symm.trans ih

/-- The quasi-periodic shift used for the inner theta series: at base `q⁶`,
`θ_{q⁶}(-q^{c-6n}) · ((-1)^n q^{3n²+3n-cn}) = θ_{q⁶}(-q^c)`.  This is the step the TeX describes
only as "quasi-periodicity gives". -/
theorem bilateralTheta_pow_six_shift {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (c n : ℤ) :
    bilateralTheta (q ^ 6) (-(q ^ (c - 6 * n))) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - c * n))
      = bilateralTheta (q ^ 6) (-(q ^ c)) := by
  have hq6 : ‖(q : 𝕜) ^ 6‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hq60 : (q : 𝕜) ^ 6 ≠ 0 := pow_ne_zero 6 hq0
  have hu : (-(q ^ c) : 𝕜) ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero c hq0)
  have h := bilateralTheta_zpow_mul hq6 hq60 hu (-n)
  have ha : ((q : 𝕜) ^ 6) ^ (-n) * -(q ^ c) = -(q ^ (c - 6 * n)) := by
    rw [← zpow_natCast q 6, ← zpow_mul, mul_neg, ← zpow_add₀ hq0,
      show ((6 : ℕ) : ℤ) * -n + c = c - 6 * n by push_cast; ring]
  have hb : ((q : 𝕜) ^ 6) ^ thetaExponent (-n) = q ^ (3 * n ^ 2 + 3 * n) := by
    rw [← pow_mul, ← zpow_natCast q (6 * thetaExponent (-n)),
      show ((6 * thetaExponent (-n) : ℕ) : ℤ) = 3 * n ^ 2 + 3 * n by
        push_cast
        linear_combination 3 * two_mul_thetaExponent (-n)]
  have hc : ((-(q ^ c) : 𝕜)) ^ (-n) = (-1 : 𝕜) ^ n * q ^ (-(c * n)) := by
    rw [neg_eq_neg_one_mul ((q : 𝕜) ^ c), mul_zpow, neg_one_zpow_neg, ← zpow_mul,
      show c * -n = -(c * n) by ring]
  have hsplit : (q : 𝕜) ^ (3 * n ^ 2 + 3 * n - c * n)
      = q ^ (3 * n ^ 2 + 3 * n) * q ^ (-(c * n)) := by
    rw [← zpow_add₀ hq0,
      show 3 * n ^ 2 + 3 * n + -(c * n) = 3 * n ^ 2 + 3 * n - c * n by ring]
  rw [ha, hb, hc] at h
  rw [← h, hsplit]
  ring

/-! ## The three evaluations of the inner theta series -/

/-- The threefold dissection `(q²;q²)_∞ = (q²;q⁶)_∞ (q⁴;q⁶)_∞ (q⁶;q⁶)_∞`.  The TeX uses this
identity silently and never displays it. -/
theorem qPochhammerInfIn_two_dissection {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn (q ^ 2) (q ^ 2)
      = qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 6) * qPochhammerInfIn ((q : 𝕜) ^ 4) (q ^ 6) *
        qPochhammerInfIn ((q : 𝕜) ^ 6) (q ^ 6) := by
  have hq2 : ‖(q : 𝕜) ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have h := qPochhammerInfIn_dissection ((q : 𝕜) ^ 2) hq2 (r := 3) (by norm_num)
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul] at h
  rw [h, show (q : 𝕜) ^ 2 * ((q : 𝕜) ^ 2) ^ 0 = q ^ 2 by ring,
    show (q : 𝕜) ^ 2 * ((q : 𝕜) ^ 2) ^ 1 = q ^ 4 by ring,
    show (q : 𝕜) ^ 2 * ((q : 𝕜) ^ 2) ^ 2 = q ^ 6 by ring,
    show ((q : 𝕜) ^ 2) ^ 3 = q ^ 6 by ring]

/-- `θ_{q⁶}(-q²) = (q²;q²)_∞`. -/
theorem bilateralTheta_pow_six_neg_two {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (2 : ℤ)))
      = qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) := by
  have hq6 : ‖(q : 𝕜) ^ 6‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hne : (-((q : 𝕜) ^ (2 : ℤ))) ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero 2 hq0)
  have e2 : (q : 𝕜) ^ (2 : ℤ) = q ^ (2 : ℕ) := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have ha : (-(-((q : 𝕜) ^ (2 : ℤ)))) = q ^ (2 : ℕ) := by rw [neg_neg, e2]
  have hb : (-((q : 𝕜) ^ 6 / -(q ^ (2 : ℤ)))) = q ^ (4 : ℕ) := by
    rw [div_neg, neg_neg, e2, div_eq_iff (pow_ne_zero 2 hq0)]
    ring
  rw [bilateralTheta_eq_prod hq6 hne, ha, hb, qPochhammerInfIn_two_dissection hq]

/-- `θ_{q⁶}(-q⁴) = (q²;q²)_∞`. -/
theorem bilateralTheta_pow_six_neg_four {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (4 : ℤ)))
      = qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) := by
  have hq6 : ‖(q : 𝕜) ^ 6‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hne : (-((q : 𝕜) ^ (4 : ℤ))) ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero 4 hq0)
  have e4 : (q : 𝕜) ^ (4 : ℤ) = q ^ (4 : ℕ) := by
    rw [show (4 : ℤ) = ((4 : ℕ) : ℤ) by norm_num, zpow_natCast]
  have ha : (-(-((q : 𝕜) ^ (4 : ℤ)))) = q ^ (4 : ℕ) := by rw [neg_neg, e4]
  have hb : (-((q : 𝕜) ^ 6 / -(q ^ (4 : ℤ)))) = q ^ (2 : ℕ) := by
    rw [div_neg, neg_neg, e4, div_eq_iff (pow_ne_zero 4 hq0)]
    ring
  rw [bilateralTheta_eq_prod hq6 hne, ha, hb, qPochhammerInfIn_two_dissection hq]
  ring

/-- `θ_{q⁶}(-q⁰) = θ_{q⁶}(-1) = 0`: the point `-1 = -(q⁶)⁰` lies on the zero set of `θ`.  This
is the uniform replacement for the TeX's case-dependent "the product contains the factor
`1 - Q⁰` after an integral quasi-periodic shift". -/
theorem bilateralTheta_pow_six_neg_one {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) :
    bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (0 : ℤ))) = 0 := by
  have hq6 : ‖(q : 𝕜) ^ 6‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hq60 : (q : 𝕜) ^ 6 ≠ 0 := pow_ne_zero 6 hq0
  rw [zpow_zero]
  refine (bilateralTheta_eq_zero_iff hq6 hq60
    (neg_ne_zero.mpr (one_ne_zero : (1 : 𝕜) ≠ 0))).mpr ⟨0, ?_⟩
  rw [zpow_zero]

/-! ## The sheared double family and its fibres -/

/-- The `(m, s)` term of the sheared product of the two bilateral theta series: the `(m-2s)`-th
term of `A(z) = ∑_r q^{e(r)} z^r` times the `s`-th term of
`B(z) = ∑_s (-1)^s (q²)^{e(s)} (q z²)^s`. -/
def quintupleTerm (q z : 𝕜) (p : ℤ × ℤ) : 𝕜 :=
  q ^ thetaExponent (p.1 - 2 * p.2) * z ^ (p.1 - 2 * p.2) *
    ((-1 : 𝕜) ^ p.2 * (q ^ 2) ^ thetaExponent p.2 * (q * z ^ 2) ^ p.2)

/-- The defining formula for `quintupleTerm`. -/
theorem quintupleTerm_def (q z : 𝕜) (m s : ℤ) :
    quintupleTerm q z (m, s)
      = q ^ thetaExponent (m - 2 * s) * z ^ (m - 2 * s) *
        ((-1 : 𝕜) ^ s * (q ^ 2) ^ thetaExponent s * (q * z ^ 2) ^ s) := rfl

/-- The coefficient of `z^m`: `q^{e(m)} z^m · θ_{q⁶}(-q^{4-2m})`. -/
def quintupleCoeff (q z : 𝕜) (m : ℤ) : 𝕜 :=
  q ^ thetaExponent m * z ^ m * bilateralTheta (q ^ 6) (-(q ^ (4 - 2 * m)))

/-- The defining formula for `quintupleCoeff`. -/
theorem quintupleCoeff_def (q z : 𝕜) (m : ℤ) :
    quintupleCoeff q z m
      = q ^ thetaExponent m * z ^ m * bilateralTheta (q ^ 6) (-(q ^ (4 - 2 * m))) := rfl

/-- The `(m,s)` term, rewritten as the `s`-th term of `q^{e(m)} z^m θ_{q⁶}(-q^{4-2m})`.  All the
exponent bookkeeping of the shear is concentrated here, in `thetaExponent_shear`. -/
theorem quintupleTerm_eq {q : 𝕜} (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) (m s : ℤ) :
    quintupleTerm q z (m, s)
      = q ^ thetaExponent m * z ^ m *
        ((q ^ 6) ^ thetaExponent s * (-(q ^ (4 - 2 * m))) ^ s) := by
  have hz2 : ((z : 𝕜) ^ 2) ^ s = z ^ (2 * s) := by
    rw [← zpow_natCast z 2, ← zpow_mul, show ((2 : ℕ) : ℤ) * s = 2 * s by norm_num]
  have hqz2 : ((q : 𝕜) ^ 2) ^ thetaExponent s = q ^ (2 * (thetaExponent s : ℤ)) := by
    rw [← pow_mul, ← zpow_natCast q (2 * thetaExponent s), Nat.cast_mul, Nat.cast_ofNat]
  have hqz6 : ((q : 𝕜) ^ 6) ^ thetaExponent s = q ^ (6 * (thetaExponent s : ℤ)) := by
    rw [← pow_mul, ← zpow_natCast q (6 * thetaExponent s), Nat.cast_mul, Nat.cast_ofNat]
  have hqe1 : (q : 𝕜) ^ thetaExponent (m - 2 * s) = q ^ ((thetaExponent (m - 2 * s) : ℤ)) :=
    (zpow_natCast q _).symm
  have hqem : (q : 𝕜) ^ thetaExponent m = q ^ ((thetaExponent m : ℤ)) :=
    (zpow_natCast q _).symm
  have hneg : ((-((q : 𝕜) ^ (4 - 2 * m))) ^ s) = (-1 : 𝕜) ^ s * q ^ ((4 - 2 * m) * s) := by
    rw [neg_eq_neg_one_mul ((q : 𝕜) ^ (4 - 2 * m)), mul_zpow, ← zpow_mul]
  have hsplit : (q : 𝕜) ^ ((thetaExponent m : ℤ) + 6 * (thetaExponent s : ℤ) + (4 - 2 * m) * s)
      = q ^ ((thetaExponent m : ℤ)) *
        (q ^ (6 * (thetaExponent s : ℤ)) * q ^ ((4 - 2 * m) * s)) := by
    rw [← zpow_add₀ hq0, ← zpow_add₀ hq0,
      show (thetaExponent m : ℤ) + (6 * (thetaExponent s : ℤ) + (4 - 2 * m) * s)
        = (thetaExponent m : ℤ) + 6 * (thetaExponent s : ℤ) + (4 - 2 * m) * s by ring]
  rw [quintupleTerm_def]
  calc q ^ thetaExponent (m - 2 * s) * z ^ (m - 2 * s) *
        ((-1 : 𝕜) ^ s * (q ^ 2) ^ thetaExponent s * (q * z ^ 2) ^ s)
      = (-1 : 𝕜) ^ s *
          (q ^ ((thetaExponent (m - 2 * s) : ℤ)) *
            (q ^ (2 * (thetaExponent s : ℤ)) * q ^ s)) *
          (z ^ (m - 2 * s) * z ^ (2 * s)) := by
        rw [mul_zpow, hz2, hqz2, hqe1]
        ring
    _ = (-1 : 𝕜) ^ s *
          q ^ ((thetaExponent (m - 2 * s) : ℤ) + 2 * (thetaExponent s : ℤ) + s) * z ^ m := by
        rw [← zpow_add₀ hq0, ← zpow_add₀ hq0, ← zpow_add₀ hz,
          show m - 2 * s + 2 * s = m by ring,
          show (thetaExponent (m - 2 * s) : ℤ) + (2 * (thetaExponent s : ℤ) + s)
            = (thetaExponent (m - 2 * s) : ℤ) + 2 * (thetaExponent s : ℤ) + s by ring]
    _ = (-1 : 𝕜) ^ s *
          q ^ ((thetaExponent m : ℤ) + 6 * (thetaExponent s : ℤ) + (4 - 2 * m) * s) * z ^ m := by
        rw [thetaExponent_shear m s]
    _ = q ^ thetaExponent m * z ^ m *
          ((q ^ 6) ^ thetaExponent s * (-(q ^ (4 - 2 * m))) ^ s) := by
        rw [hqz6, hneg, hqem, hsplit]
        ring

/-- **The fibre sum.**  For each `m`, the `s`-fibre of the sheared double family sums to
`quintupleCoeff q z m`. -/
theorem hasSum_quintupleTerm_fiber {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0)
    (m : ℤ) :
    HasSum (fun s : ℤ => quintupleTerm q z (m, s)) (quintupleCoeff q z m) := by
  have hq6 : ‖(q : 𝕜) ^ 6‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hu : (-((q : 𝕜) ^ (4 - 2 * m))) ≠ 0 := neg_ne_zero.mpr (zpow_ne_zero _ hq0)
  have h := (hasSum_bilateralTheta hq6 hu).mul_left (q ^ thetaExponent m * z ^ m)
  rw [quintupleCoeff_def]
  exact h.congr_fun fun s => quintupleTerm_eq hq0 hz m s

/-- **The bilateral Laurent expansion of the quintuple product.**  For `‖q‖ < 1`, `q ≠ 0`,
`z ≠ 0`,

`∑_{m ∈ ℤ} q^{e(m)} z^m θ_{q⁶}(-q^{4-2m})
    = (-z;q)_∞(-q/z;q)_∞(q;q)_∞ · (qz²;q²)_∞(q/z²;q²)_∞(q²;q²)_∞`.

Both theta families are absolutely summable, so the product is an unconditionally summable family
over `ℤ × ℤ`; shearing and regrouping fibrewise proves the identity with no analytic
coefficient-extraction step. -/
theorem hasSum_quintupleCoeff {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) :
    HasSum (quintupleCoeff q z)
      ((qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q) *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2) *
          qPochhammerInfIn (q ^ 2) (q ^ 2))) := by
  have hq2 : ‖(q : 𝕜) ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hqz : ((q : 𝕜) * z ^ 2) ≠ 0 := mul_ne_zero hq0 (pow_ne_zero 2 hz)
  have hA := hasSum_jacobi_triple_product' hq hz
  have hB := hasSum_jacobi_triple_product hq2 hqz
  have hdiv : (q : 𝕜) ^ 2 / (q * z ^ 2) = q / z ^ 2 := by
    rw [div_eq_div_iff hqz (pow_ne_zero 2 hz)]
    ring
  rw [hdiv] at hB
  have hnA : Summable fun k : ℤ => ‖(q ^ thetaExponent k * z ^ k : 𝕜)‖ := by
    have hs := summable_pow_thetaExponent_mul_zpow (norm_nonneg q) hq (norm_pos_iff.mpr hz)
    refine hs.congr fun k => ?_
    simp only [norm_mul, norm_pow, norm_zpow]
  have hnB : Summable fun s : ℤ =>
      ‖((-1 : 𝕜) ^ s * (q ^ 2) ^ thetaExponent s * (q * z ^ 2) ^ s)‖ := by
    have hs := summable_pow_thetaExponent_mul_zpow (norm_nonneg ((q : 𝕜) ^ 2)) hq2
      (norm_pos_iff.mpr hqz)
    refine hs.congr fun s => ?_
    simp only [norm_mul, norm_pow, norm_zpow, norm_neg, norm_one, one_zpow, one_mul]
  have hmul : Summable fun x : ℤ × ℤ =>
      (q ^ thetaExponent x.1 * z ^ x.1 : 𝕜) *
        ((-1 : 𝕜) ^ x.2 * (q ^ 2) ^ thetaExponent x.2 * (q * z ^ 2) ^ x.2) :=
    summable_mul_of_summable_norm
      (f := fun k : ℤ => (q ^ thetaExponent k * z ^ k : 𝕜))
      (g := fun k : ℤ => ((-1 : 𝕜) ^ k * (q ^ 2) ^ thetaExponent k * (q * z ^ 2) ^ k))
      hnA hnB
  have hAB := hA.mul hB hmul
  have hshear : HasSum (quintupleTerm q z)
      ((qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q) *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2) *
          qPochhammerInfIn (q ^ 2) (q ^ 2))) :=
    (shearEquiv.hasSum_iff.mpr hAB).congr_fun fun p => rfl
  exact hshear.prod_fiberwise fun m => hasSum_quintupleTerm_fiber hq hq0 hz m

/-! ## The three residue classes modulo three -/

/-- The class `m = 3n`: `quintupleCoeff q z (3n) = (q²;q²)_∞ (-1)^n q^{p(n)} z^{3n}`. -/
theorem quintupleCoeff_three_mul {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (z : 𝕜) (n : ℤ) :
    quintupleCoeff q z (n * 3)
      = qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * q ^ pentagonalExponent n * z ^ (n * 3)) := by
  have hne1 : (-1 : 𝕜) ≠ 0 := neg_ne_zero.mpr (one_ne_zero : (1 : 𝕜) ≠ 0)
  have hone : ((-1 : 𝕜)) ^ n * (-1 : 𝕜) ^ n = 1 := by
    rw [← zpow_add₀ hne1]
    exact Even.neg_one_zpow ⟨n, rfl⟩
  have hU : ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 4 * n)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero n hne1) (zpow_ne_zero _ hq0)
  have hshift := bilateralTheta_pow_six_shift hq hq0 4 n
  rw [bilateralTheta_pow_six_neg_four hq hq0] at hshift
  have hq3 : (q : 𝕜) ^ pentagonalExponent n * q ^ (3 * n ^ 2 + 3 * n - 4 * n)
      = q ^ thetaExponent (n * 3) := by
    rw [← zpow_natCast q (pentagonalExponent n), ← zpow_add₀ hq0,
      ← zpow_natCast q (thetaExponent (n * 3)), thetaExponent_three_mul_eq n]
  have hval : quintupleCoeff q z (n * 3)
      = q ^ thetaExponent (n * 3) * z ^ (n * 3) *
        bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (4 - 6 * n))) := by
    rw [quintupleCoeff_def, show (4 : ℤ) - 2 * (n * 3) = 4 - 6 * n by ring]
  refine mul_right_cancel₀ hU ?_
  rw [hval]
  have hL : q ^ thetaExponent (n * 3) * z ^ (n * 3) *
        bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (4 - 6 * n))) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 4 * n))
      = q ^ thetaExponent (n * 3) * z ^ (n * 3) *
        qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) := by
    rw [mul_assoc (q ^ thetaExponent (n * 3) * z ^ (n * 3)), hshift]
  have hR : qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * q ^ pentagonalExponent n * z ^ (n * 3)) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 4 * n))
      = q ^ thetaExponent (n * 3) * z ^ (n * 3) *
        qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) := by
    rw [← hq3]
    have hre : qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * q ^ pentagonalExponent n * z ^ (n * 3)) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 4 * n))
        = ((-1 : 𝕜) ^ n * (-1 : 𝕜) ^ n) *
          (q ^ pentagonalExponent n * q ^ (3 * n ^ 2 + 3 * n - 4 * n) * z ^ (n * 3) *
            qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2)) := by ring
    rw [hre, hone, one_mul]
  exact hL.trans hR.symm

/-- The class `m = 3n+1`: `quintupleCoeff q z (3n+1) = (q²;q²)_∞ (-1)^n q^{p(-n)} z^{3n+1}`.
The TeX asserts this case without proof. -/
theorem quintupleCoeff_three_mul_add_one {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (z : 𝕜)
    (n : ℤ) :
    quintupleCoeff q z (n * 3 + 1)
      = qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1)) := by
  have hne1 : (-1 : 𝕜) ≠ 0 := neg_ne_zero.mpr (one_ne_zero : (1 : 𝕜) ≠ 0)
  have hone : ((-1 : 𝕜)) ^ n * (-1 : 𝕜) ^ n = 1 := by
    rw [← zpow_add₀ hne1]
    exact Even.neg_one_zpow ⟨n, rfl⟩
  have hU : ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 2 * n)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero n hne1) (zpow_ne_zero _ hq0)
  have hshift := bilateralTheta_pow_six_shift hq hq0 2 n
  rw [bilateralTheta_pow_six_neg_two hq hq0] at hshift
  have hq3 : (q : 𝕜) ^ pentagonalExponent (-n) * q ^ (3 * n ^ 2 + 3 * n - 2 * n)
      = q ^ thetaExponent (n * 3 + 1) := by
    rw [← zpow_natCast q (pentagonalExponent (-n)), ← zpow_add₀ hq0,
      ← zpow_natCast q (thetaExponent (n * 3 + 1)), thetaExponent_three_mul_add_one_eq n]
  have hval : quintupleCoeff q z (n * 3 + 1)
      = q ^ thetaExponent (n * 3 + 1) * z ^ (n * 3 + 1) *
        bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (2 - 6 * n))) := by
    rw [quintupleCoeff_def, show (4 : ℤ) - 2 * (n * 3 + 1) = 2 - 6 * n by ring]
  refine mul_right_cancel₀ hU ?_
  rw [hval]
  have hL : q ^ thetaExponent (n * 3 + 1) * z ^ (n * 3 + 1) *
        bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (2 - 6 * n))) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 2 * n))
      = q ^ thetaExponent (n * 3 + 1) * z ^ (n * 3 + 1) *
        qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) := by
    rw [mul_assoc (q ^ thetaExponent (n * 3 + 1) * z ^ (n * 3 + 1)), hshift]
  have hR : qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1)) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 2 * n))
      = q ^ thetaExponent (n * 3 + 1) * z ^ (n * 3 + 1) *
        qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) := by
    rw [← hq3]
    have hre : qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1)) *
        ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 2 * n))
        = ((-1 : 𝕜) ^ n * (-1 : 𝕜) ^ n) *
          (q ^ pentagonalExponent (-n) * q ^ (3 * n ^ 2 + 3 * n - 2 * n) * z ^ (n * 3 + 1) *
            qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2)) := by ring
    rw [hre, hone, one_mul]
  exact hL.trans hR.symm

/-- The class `m = 3n+2`: `quintupleCoeff q z (3n+2) = 0`, uniformly in `n`.  The inner theta is
evaluated at `-(q⁶)^{-n}`, a point of its zero set. -/
theorem quintupleCoeff_three_mul_add_two {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (z : 𝕜)
    (n : ℤ) :
    quintupleCoeff q z (n * 3 + 2) = 0 := by
  have hne1 : (-1 : 𝕜) ≠ 0 := neg_ne_zero.mpr (one_ne_zero : (1 : 𝕜) ≠ 0)
  have hU : ((-1 : 𝕜) ^ n * q ^ (3 * n ^ 2 + 3 * n - 0 * n)) ≠ 0 :=
    mul_ne_zero (zpow_ne_zero n hne1) (zpow_ne_zero _ hq0)
  have hshift := bilateralTheta_pow_six_shift hq hq0 0 n
  rw [bilateralTheta_pow_six_neg_one hq hq0] at hshift
  have hzero : bilateralTheta ((q : 𝕜) ^ 6) (-(q ^ (0 - 6 * n))) = 0 := by
    rcases mul_eq_zero.mp hshift with h | h
    · exact h
    · exact absurd h hU
  rw [quintupleCoeff_def, show (4 : ℤ) - 2 * (n * 3 + 2) = 0 - 6 * n by ring, hzero, mul_zero]

/-! ## Watson's quintuple product -/

/-- **Watson's quintuple product identity**, paired form.  For `‖q‖ < 1`, `q ≠ 0` and `z ≠ 0`
in a complete normed field,

`∑_{n ∈ ℤ} (-1)^n (q^{n(3n-1)/2} z^{3n} + q^{n(3n+1)/2} z^{3n+1})
    = (q;q)_∞ (-z;q)_∞ (-q/z;q)_∞ (qz²;q²)_∞ (q/z²;q²)_∞`.

Pairing the two half-terms keeps every exponent of `q` a natural number.  The literal shape of
the monograph is `hasSum_quintuple_product'`. -/
theorem hasSum_quintuple_product {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) :
    HasSum (fun n : ℤ => (-1 : 𝕜) ^ n *
        (q ^ pentagonalExponent n * z ^ (n * 3) +
          q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1)))
      (qPochhammerInfIn q q * qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2))) := by
  have hq2 : ‖(q : 𝕜) ^ 2‖ < 1 := norm_pow_lt_one_of_norm_lt_one hq (by norm_num)
  have hC : qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) ≠ 0 := qPochhammerInfIn_self_ne_zero hq2
  have hcoeff := hasSum_quintupleCoeff hq hq0 hz
  have hsymm : ∀ p : ℤ × Fin 3,
      ((Int.divModEquiv 3).symm p) = p.1 * 3 + (p.2 : ℤ) := by
    intro p
    show p.1 * ((3 : ℕ) : ℤ) + (p.2 : ℤ) = p.1 * 3 + (p.2 : ℤ)
    norm_num
  have hdiss : HasSum (fun p : ℤ × Fin 3 => quintupleCoeff q z (p.1 * 3 + (p.2 : ℤ)))
      ((qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q) *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2) *
          qPochhammerInfIn (q ^ 2) (q ^ 2))) := by
    refine (((Int.divModEquiv 3).symm.hasSum_iff).mpr hcoeff).congr_fun fun p => ?_
    show quintupleCoeff q z (p.1 * 3 + (p.2 : ℤ))
      = quintupleCoeff q z ((Int.divModEquiv 3).symm p)
    rw [hsymm p]
  have hfib : ∀ n : ℤ, HasSum (fun i : Fin 3 => quintupleCoeff q z (n * 3 + (i : ℤ)))
      (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
        ((-1 : 𝕜) ^ n * (q ^ pentagonalExponent n * z ^ (n * 3) +
          q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1)))) := by
    intro n
    have c0 : ((0 : Fin 3) : ℤ) = 0 := by simp
    have c1 : ((1 : Fin 3) : ℤ) = 1 := by simp
    have c2 : ((2 : Fin 3) : ℤ) = 2 := by simp
    have hval : (∑ i : Fin 3, quintupleCoeff q z (n * 3 + (i : ℤ)))
        = qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
          ((-1 : 𝕜) ^ n * (q ^ pentagonalExponent n * z ^ (n * 3) +
            q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1))) := by
      rw [Fin.sum_univ_three, c0, c1, c2, add_zero, quintupleCoeff_three_mul hq hq0 z n,
        quintupleCoeff_three_mul_add_one hq hq0 z n,
        quintupleCoeff_three_mul_add_two hq hq0 z n, add_zero]
      ring
    rw [← hval]
    exact hasSum_fintype _
  have hprod := hdiss.prod_fiberwise hfib
  have hpt : ∀ x : 𝕜, (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2))⁻¹ *
      (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) * x) = x := fun x => by
    rw [← mul_assoc, inv_mul_cancel₀ hC, one_mul]
  have hvalue : (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2))⁻¹ *
      ((qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q) *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2) *
          qPochhammerInfIn (q ^ 2) (q ^ 2)))
      = qPochhammerInfIn q q * qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2)) := by
    have hrw : (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2))⁻¹ *
        ((qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q * qPochhammerInfIn q q) *
          (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2) *
            qPochhammerInfIn (q ^ 2) (q ^ 2)))
        = (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2))⁻¹ * qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2) *
          (qPochhammerInfIn q q * qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q *
            (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2))) := by
      ring
    rw [hrw, inv_mul_cancel₀ hC, one_mul]
  have hfin := hprod.mul_left (qPochhammerInfIn ((q : 𝕜) ^ 2) (q ^ 2))⁻¹
  rw [hvalue] at hfin
  exact hfin.congr_fun fun n => (hpt _).symm

/-- **Watson's quintuple product identity**, in the shape printed in the monograph:

`∑_{n ∈ ℤ} (-1)^n q^{n(3n-1)/2} z^{3n} (1 + z q^n)
    = (q,-z,-q/z;q)_∞ (qz², q/z²;q²)_∞`.

Here `q^n` is an integer power, so `q ≠ 0` is genuinely needed for the summand to be defined as
written; the paired form `hasSum_quintuple_product` avoids negative exponents. -/
theorem hasSum_quintuple_product' {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) :
    HasSum (fun n : ℤ =>
        (-1 : 𝕜) ^ n * q ^ pentagonalExponent n * z ^ (n * 3) * (1 + z * q ^ n))
      (qPochhammerInfIn q q * qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2))) := by
  refine (hasSum_quintuple_product hq hq0 hz).congr_fun fun n => ?_
  have hexp : (q : 𝕜) ^ pentagonalExponent n * q ^ n = q ^ pentagonalExponent (-n) := by
    rw [← zpow_natCast q (pentagonalExponent n), ← zpow_add₀ hq0,
      pentagonalExponent_add_self_eq n, zpow_natCast]
  have hz1 : (z : 𝕜) ^ (n * 3) * z = z ^ (n * 3 + 1) := (zpow_add_one₀ hz (n * 3)).symm
  calc (-1 : 𝕜) ^ n * q ^ pentagonalExponent n * z ^ (n * 3) * (1 + z * q ^ n)
      = (-1 : 𝕜) ^ n * (q ^ pentagonalExponent n * z ^ (n * 3)
          + q ^ pentagonalExponent n * q ^ n * (z ^ (n * 3) * z)) := by ring
    _ = (-1 : 𝕜) ^ n * (q ^ pentagonalExponent n * z ^ (n * 3)
          + q ^ pentagonalExponent (-n) * z ^ (n * 3 + 1)) := by rw [hexp, hz1]

/-- Watson's quintuple product as an equation between a `tsum` and the product. -/
theorem tsum_quintuple_product {q : 𝕜} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) {z : 𝕜} (hz : z ≠ 0) :
    ∑' n : ℤ, (-1 : 𝕜) ^ n * q ^ pentagonalExponent n * z ^ (n * 3) * (1 + z * q ^ n)
      = qPochhammerInfIn q q * qPochhammerInfIn (-z) q * qPochhammerInfIn (-(q / z)) q *
        (qPochhammerInfIn (q * z ^ 2) (q ^ 2) * qPochhammerInfIn (q / z ^ 2) (q ^ 2)) :=
  (hasSum_quintuple_product' hq hq0 hz).tsum_eq

end

end Fabius

import FabiusFunction.GeometricLagrangeQBinomial
import FabiusFunction.GeometricQBinomialLagrange
import Mathlib.Algebra.BigOperators.Intervals

/-!
# All power moments and exact conditioning of geometric Lagrange weights

For the Lagrange weights on the geometric nodes

`1, q, ..., q^p`,

this module evaluates every power moment

`S_(p,m)(q) = sum_(j=0)^p lambda_(p,j)(q) q^(j m)`.

The full rational identity is

`S_(p,m)(q) = q^(p m) (q / q^m; q)_p / (q; q)_p`.

For nonzero `q`, the first q-Pochhammer argument `q / q^m` is the
division-only form of the integer power `q^(1-m)`, so this is exactly the
formula conventionally written

`q^(p m) (q^(1-m); q)_p / (q; q)_p`.

The proof does not duplicate interpolation or develop a second Gaussian
polynomial.  It evaluates the coefficient polynomial already supplied by
`GeometricLagrangeWeights`, identifies it with the normalized forward
Richardson polynomial, and clears the common signed geometric product from
its numerator and denominator.  The positive-index form is routed through
the generic denominator-free Gaussian moment theorem from
`GeometricQBinomialLagrange`:

`S_(p,m)(q) = (-1)^p q^choose(p+1,2)
  (q^(m-p); q)_p / (q; q)_p`

when `p < m`.  Hence, for `0 < q < 1`, multiplication by `(-1)^p` makes
every residual moment strictly positive.  This is a statement about the sign
at one fixed Richardson level.  It deliberately makes no comparison between
two levels of the same parity: the corrected frontier report gives explicit
admissible counterexamples to such monotonicity.

The second half computes the exact total variation directly from the same
forward Richardson polynomial:

`sum_j |lambda_(p,j)(q)| = (-q; q)_p / (q; q)_p
  = product_(r=1)^p (1+q^r)/(1-q^r)`.

The denominator-free finite q-binomial theorem remains centralized in
`FiniteQBinomialCore`; no second q-Pascal induction is developed here.

All results here are finite algebraic identities.  There are no analytic
convergence, sinc-tail, bracketing, or asymptotic claims.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

/-! ## Sign bookkeeping

Two facts about `(-1)^k` that the weight computations below use a dozen
times.  Both hold in any monoid with a distributive negation, so they are
stated there rather than over `ℚ`. -/

/-- `(-1)^p · (-1)^p = 1`. -/
theorem neg_one_pow_mul_self {R : Type*} [Monoid R] [HasDistribNeg R]
    (p : ℕ) : (-1 : R) ^ p * (-1 : R) ^ p = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨p, rfl⟩

/-- `(-1)^(p-k) = (-1)^p · (-1)^k` for `k ≤ p`: the two copies of
`(-1)^k` cancel. -/
theorem neg_one_pow_sub {R : Type*} [Monoid R] [HasDistribNeg R]
    {p k : ℕ} (hk : k ≤ p) :
    (-1 : R) ^ (p - k) = (-1 : R) ^ p * (-1 : R) ^ k := by
  have h : (-1 : R) ^ (p - k) * ((-1 : R) ^ k * (-1 : R) ^ k) =
      (-1 : R) ^ p * (-1 : R) ^ k := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hk]
  rwa [neg_one_pow_mul_self, mul_one] at h

/-! ## The moment functional and its Richardson-polynomial realization -/

/-- The `m`-th power moment of the evaluation-at-zero Lagrange weights on
the `p + 1` geometric nodes `1, q, ..., q^p`. -/
noncomputable def geometricLagrangeQMoment
    (q : ℚ) (p m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (p + 1),
    geometricLagrangeWeight q p j * (q ^ j) ^ m

/-- The geometric moment is evaluation of the canonical weight-coefficient
polynomial at the corresponding geometric node. -/
theorem geometricLagrangeQMoment_eq_weightPolynomial_eval
    (q : ℚ) (p m : ℕ) :
    geometricLagrangeQMoment q p m =
      (geometricLagrangeWeightPolynomial q p).eval (q ^ m) := by
  rw [geometricLagrangeQMoment,
    geometricLagrangeWeightPolynomial_eval]
  calc
    (∑ j ∈ Finset.range (p + 1),
        geometricLagrangeWeight q p j * (q ^ j) ^ m) =
        ∑ j ∈ Finset.range (p + 1),
          geometricLagrangeWeight q p j * (q ^ m) ^ j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = ∑ k : Fin (p + 1),
        geometricLagrangeWeight q p (k : ℕ) *
          (q ^ m) ^ (k : ℕ) :=
      (Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ geometricLagrangeWeight q p j * (q ^ m) ^ j)
        (p + 1)).symm

/-- Under sufficient finite noncollision hypotheses, every geometric moment
is an evaluation of the normalized forward Richardson polynomial. -/
theorem geometricLagrangeQMoment_eq_forwardRichardson_eval
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) :
    geometricLagrangeQMoment q p m =
      (forwardGeometricRichardsonPolynomial q p).eval (q ^ m) := by
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  rw [geometricLagrangeQMoment_eq_weightPolynomial_eval,
    geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
      q hq p hnodes]

/-! ## Clearing the inverse-base normalization -/

/-- Multiplying the inverse-base numerator at `q^m` by the common signed
geometric product gives the division-free numerator
`q^(p*m) (q/q^m;q)_p` of the full moment formula.

The quotient `q / q^m` is intentional: for nonzero `q` it represents the
integer power `q^(1-m)` uniformly, including the boundary case `m = 0`. -/
theorem geometricRootPolynomial_inv_eval_pow_mul_signedPowers
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ) :
    (geometricRootPolynomial q⁻¹ p).eval (q ^ m) *
        (∏ r ∈ Finset.range p, (-(q ^ (r + 1)))) =
      q ^ (p * m) * qPochhammer (q / q ^ m) q p := by
  rw [geometricRootPolynomial_eval, ← Finset.prod_mul_distrib]
  calc
    (∏ r ∈ Finset.range p,
        (1 - (q⁻¹) ^ (r + 1) * q ^ m) * (-(q ^ (r + 1)))) =
        ∏ r ∈ Finset.range p,
          (q ^ m * (1 - (q / q ^ m) * q ^ r)) := by
      apply Finset.prod_congr rfl
      intro r _hr
      have hpowNe (n : ℕ) : q ^ n ≠ 0 := pow_ne_zero n hq
      simp only [inv_pow, pow_succ]
      field_simp [hpowNe]
      all_goals ring
    _ = q ^ (p * m) * qPochhammer (q / q ^ m) q p := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_range]
      rw [← pow_mul, Nat.mul_comm m p]
      rfl

/-- Closed triangular-power version of
`geometricRootPolynomial_inv_eval_pow_mul_signedPowers`. -/
theorem geometricRootPolynomial_inv_eval_pow_mul_triangular
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ) :
    (geometricRootPolynomial q⁻¹ p).eval (q ^ m) *
        ((-1 : ℚ) ^ p * q ^ (p + 1).choose 2) =
      q ^ (p * m) * qPochhammer (q / q ^ m) q p := by
  rw [← prod_neg_geometric_powers q p]
  exact geometricRootPolynomial_inv_eval_pow_mul_signedPowers q hq p m

/-- The same signed triangular product clears the inverse-base normalizer
and leaves the ordinary denominator `(q;q)_p`. -/
theorem geometricRootPolynomial_inv_eval_one_mul_triangular
    (q : ℚ) (hq : q ≠ 0) (p : ℕ) :
    (geometricRootPolynomial q⁻¹ p).eval 1 *
        ((-1 : ℚ) ^ p * q ^ (p + 1).choose 2) =
      qPochhammer q q p := by
  rw [← prod_neg_geometric_powers q p,
    geometricRootPolynomial_inv_eval_one_mul_signedPowers q hq p,
    geometricRootPolynomial_eval_one]
  simpa only [geometricQPochhammer] using
    geometricQPochhammer_rat_eq_qPochhammer q p

/-! ## All rational power moments -/

/-- Full q-Pochhammer formula for every power moment:

`S_(p,m)(q) = q^(p*m) (q/q^m;q)_p / (q;q)_p`.

The hypotheses ensure that `q` and the finite Gaussian denominator are
nonzero.  In particular, the nodes `1,q,...,q^p` are distinct and the
quotient presentation is legitimate; no converse boundary-case
characterization is claimed. -/
theorem geometricLagrangeQMoment_eq_qPochhammer
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) :
    geometricLagrangeQMoment q p m =
      q ^ (p * m) * qPochhammer (q / q ^ m) q p /
        qPochhammer q q p := by
  rw [geometricLagrangeQMoment_eq_forwardRichardson_eval
    q hq p m hPochhammer,
    forwardGeometricRichardsonPolynomial_eval]
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  have hden : (geometricRootPolynomial q⁻¹ p).eval 1 ≠ 0 :=
    geometricRootPolynomial_inv_eval_one_ne_zero_of_nodes_injective
      q hq p hnodes
  apply (div_eq_div_iff hden hPochhammer).2
  rw [← geometricRootPolynomial_inv_eval_one_mul_triangular q hq p,
    ← geometricRootPolynomial_inv_eval_pow_mul_triangular q hq p m]
  ring

/-- The degree-zero moment is one.  This is recorded separately because the
cancelled positive moments have value zero, whereas Lean correctly interprets
the interpolated boundary as `0^0 = 1`. -/
theorem geometricLagrangeQMoment_zero
    (q : ℚ) (hq : q ≠ 0) (p : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) :
    geometricLagrangeQMoment q p 0 = 1 := by
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  simpa [geometricLagrangeQMoment] using
    sum_geometricLagrangeWeight q p hnodes

/-- Every positive moment through degree `p` is cancelled exactly. -/
theorem geometricLagrangeQMoment_eq_zero
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0)
    (hmpos : 0 < m) (hmp : m ≤ p) :
    geometricLagrangeQMoment q p m = 0 := by
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  exact sum_geometricLagrangeWeight_mul_pow_eq_zero
    q p m hnodes hmpos hmp

/-- Above the cancelled range, the raw inverse-base numerator reverses to
the positive-index q-Pochhammer product `(q^(m-p);q)_p`. -/
theorem geometricRootPolynomial_inv_eval_pow_eq_qPochhammer_of_le
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ) (hpm : p ≤ m) :
    (geometricRootPolynomial q⁻¹ p).eval (q ^ m) =
      qPochhammer (q ^ (m - p)) q p := by
  rw [geometricRootPolynomial_eval]
  calc
    (∏ r ∈ Finset.range p, (1 - (q⁻¹) ^ (r + 1) * q ^ m)) =
        ∏ r ∈ Finset.range p, (1 - q ^ (m - (r + 1))) := by
      apply Finset.prod_congr rfl
      intro r hr
      have hrm : r + 1 ≤ m := by
        have hrp : r < p := Finset.mem_range.mp hr
        omega
      apply congrArg (fun x : ℚ ↦ 1 - x)
      calc
        (q⁻¹) ^ (r + 1) * q ^ m =
            (q ^ (r + 1))⁻¹ * q ^ m := by rw [inv_pow]
        _ = (q ^ (r + 1))⁻¹ *
              (q ^ (r + 1) * q ^ (m - (r + 1))) := by
            congr 1
            rw [← pow_add, Nat.add_sub_of_le hrm]
        _ = q ^ (m - (r + 1)) := by
            rw [inv_mul_cancel_left₀ (pow_ne_zero _ hq)]
    _ = ∏ r ∈ Finset.range p, (1 - q ^ (m - p + r)) := by
      calc
        (∏ r ∈ Finset.range p, (1 - q ^ (m - (r + 1)))) =
            ∏ r ∈ Finset.range p,
              (1 - q ^ (m - p + (p - 1 - r))) := by
            apply Finset.prod_congr rfl
            intro r hr
            have hrp : r < p := Finset.mem_range.mp hr
            rw [show m - (r + 1) = m - p + (p - 1 - r) by omega]
        _ = ∏ r ∈ Finset.range p, (1 - q ^ (m - p + r)) :=
          Finset.prod_range_reflect (fun r ↦ 1 - q ^ (m - p + r)) p
    _ = qPochhammer (q ^ (m - p)) q p := by
      unfold qPochhammer finiteQPochhammer
      apply Finset.prod_congr rfl
      intro r _hr
      rw [← pow_add]

/-- Positive-index residual product.  For `p < m`,

`S_(p,m)(q) = (-1)^p q^choose(p+1,2)
  (q^(m-p);q)_p / (q;q)_p`.

Unlike the full formula, this orientation contains only natural powers. -/
theorem geometricLagrangeQMoment_eq_residual_qPochhammer
    (q : ℚ) (hq : q ≠ 0) (p m : ℕ)
    (hPochhammer : qPochhammer q q p ≠ 0) (hpm : p < m) :
    geometricLagrangeQMoment q p m =
      ((-1 : ℚ) ^ p * q ^ (p + 1).choose 2) *
        qPochhammer (q ^ (m - p)) q p / qPochhammer q q p := by
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  have hmoment :=
    sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial
      q p m hnodes (by omega : 0 < m)
  have hgauss :
      qPochhammer q q p * gaussianBinomial q (m - 1) p =
        qPochhammer (q ^ (m - p)) q p := by
    simpa only [finiteQPochhammerIn_rat_eq,
      show m - 1 - p + 1 = m - p by omega] using
      (finiteQPochhammerIn_self_mul_gaussianBinomial
        q (n := m - 1) (k := p) (by omega : p ≤ m - 1))
  have htri : p * (p + 1) / 2 = (p + 1).choose 2 := by
    rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]
  calc
    geometricLagrangeQMoment q p m =
        (-1 : ℚ) ^ p * q ^ (p * (p + 1) / 2) *
          gaussianBinomial q (m - 1) p := by
      simpa only [geometricLagrangeQMoment] using hmoment
    _ = ((-1 : ℚ) ^ p * q ^ (p + 1).choose 2) *
          qPochhammer (q ^ (m - p)) q p /
            qPochhammer q q p := by
      rw [htri]
      apply (eq_div_iff hPochhammer).2
      rw [← hgauss]
      ring

/-- Splitting a self q-Pochhammer product after its first `a` factors:

`(q;q)_(a+p) = (q;q)_a (q^(a+1);q)_p`.

This finite identity is valid for every rational `q`; no nonvanishing or
order hypothesis is needed. -/
theorem qPochhammer_self_add (q : ℚ) (a p : ℕ) :
    qPochhammer q q (a + p) =
      qPochhammer q q a * qPochhammer (q ^ (a + 1)) q p := by
  simpa only [finiteQPochhammerIn_rat_eq] using
    (finiteQPochhammerIn_self_add q a p)

/-! ## Positivity infrastructure for `0 < q < 1` -/

/-- Every finite self q-Pochhammer product is positive when `0 < q < 1`. -/
theorem qPochhammer_self_pos_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (n : ℕ) :
    0 < qPochhammer q q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qPochhammer_succ]
      apply mul_pos ih
      have hpow : q ^ (n + 1) < 1 :=
        pow_lt_one₀ hqpos.le hqone (by omega)
      have hfactor : q * q ^ n = q ^ (n + 1) := by
        rw [pow_succ]
        ring
      rw [hfactor]
      linarith

/-- In the admissible range, a rational Gaussian coefficient is positive
for every `0 < q < 1`. -/
theorem qBinomial_pos_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    {n k : ℕ} (hk : k ≤ n) :
    0 < qBinomial n k q := by
  rw [qBinomial_eq_quotient q hk]
  exact div_pos
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone n)
    (mul_pos
      (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone k)
      (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone (n - k)))

/-- **The three-way non-root-of-unity criterion.**  For a nonzero `q` in a
field, the `n+1` geometric nodes `1, q, …, qⁿ` are distinct exactly when the
finite q-Pochhammer symbol `(q;q)_n` does not vanish, exactly when no
`q^(r+1)` with `r < n` is a root of unity.  The two implications were
available separately (`finiteQPochhammerIn_self_ne_zero_of_injOn` needs no
side condition; the converse needs `q ≠ 0`, and indeed at `q = 0` the nodes
`1,0,0,…` collide while `(0;0)_n = 1`), but the equivalence the docstrings
advertise was never stated. -/
theorem injOn_pow_range_iff_finiteQPochhammerIn_self_ne_zero
    {F : Type*} [Field F] (q : F) (hq : q ≠ 0) (n : ℕ) :
    Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)) ↔
      finiteQPochhammerIn q q n ≠ 0 :=
  ⟨finiteQPochhammerIn_self_ne_zero_of_injOn q n,
    fun h => pow_injOn_range_of_geometricQPochhammer_ne_zero q hq n
      (by rwa [geometricQPochhammer_eq_finiteQPochhammerIn])⟩

/-- The same criterion in its root-of-unity form: distinct geometric nodes
are exactly the absence of an `(r+1)`-th root of unity among the powers,
`r < n`. -/
theorem injOn_pow_range_iff_forall_pow_ne_one
    {F : Type*} [Field F] (q : F) (hq : q ≠ 0) (n : ℕ) :
    Set.InjOn (fun k : ℕ => q ^ k) (Finset.range (n + 1)) ↔
      ∀ r < n, q ^ (r + 1) ≠ 1 := by
  rw [injOn_pow_range_iff_finiteQPochhammerIn_self_ne_zero q hq n,
    ← geometricQPochhammer_eq_finiteQPochhammerIn]
  exact geometricQPochhammer_ne_zero_iff q n

/-- Nonvanishing of `(q;q)_n` passes to every prefix: the criterion
`∀ r < n, q^(r+1) ≠ 1` is monotone in `n`. -/
theorem qPochhammer_self_ne_zero_of_le {q : ℚ} {m n : ℕ} (hmn : m ≤ n)
    (h : qPochhammer q q n ≠ 0) : qPochhammer q q m ≠ 0 :=
  (qPochhammer_self_ne_zero_iff q m).2 fun r hr =>
    (qPochhammer_self_ne_zero_iff q n).1 h r (lt_of_lt_of_le hr hmn)

/-- **The Gaussian and rational q-binomial coefficients agree whenever
`(q;q)_n ≠ 0`** — the exact hypothesis, replacing the interval
`0 < q < 1`.  Only two denominators have to be nonzero, `(q;q)_k` and
`(q;q)_{n−k}`, and both are prefixes of `(q;q)_n`.  The identity therefore
holds at every negative `q`, every `q > 1`, and every non-root-of-unity
`q`, not merely inside the unit interval.

The proof uses the denominator-free q-factorial identity and one legitimate
cancellation; it does not replay q-Pascal. -/
theorem gaussianBinomial_eq_qBinomial_of_qPochhammer_ne_zero
    (q : ℚ) {n : ℕ} (hq : qPochhammer q q n ≠ 0) (k : ℕ) :
    gaussianBinomial q n k = qBinomial n k q := by
  by_cases hk : k ≤ n
  · have hkNe : qPochhammer q q k ≠ 0 :=
      qPochhammer_self_ne_zero_of_le hk hq
    have hnkNe : qPochhammer q q (n - k) ≠ 0 :=
      qPochhammer_self_ne_zero_of_le (Nat.sub_le n k) hq
    have hfactorial :
        qPochhammer q q k * gaussianBinomial q n k =
          qPochhammer (q ^ (n - k + 1)) q k := by
      simpa only [finiteQPochhammerIn_rat_eq] using
        (finiteQPochhammerIn_self_mul_gaussianBinomial q hk)
    have hsplit :
        qPochhammer q q n =
          qPochhammer q q (n - k) *
            qPochhammer (q ^ (n - k + 1)) q k := by
      simpa only [Nat.sub_add_cancel hk] using
        (qPochhammer_self_add q (n - k) k)
    rw [qBinomial_eq_quotient q hk, hsplit, ← hfactorial]
    field_simp [hkNe, hnkNe]
  · have hkn : n < k := Nat.lt_of_not_ge hk
    rw [gaussianBinomial_eq_zero_of_lt q hkn,
      qBinomial_eq_zero_of_lt q hkn]

/-- The interval form of
`gaussianBinomial_eq_qBinomial_of_qPochhammer_ne_zero`, kept so that
existing call sites are untouched: on `0 < q < 1` the symbol `(q;q)_n` is
positive, hence nonzero. -/
theorem gaussianBinomial_eq_qBinomial_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (n k : ℕ) :
    gaussianBinomial q n k = qBinomial n k q :=
  gaussianBinomial_eq_qBinomial_of_qPochhammer_ne_zero q
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone n).ne' k

/-- If `d` is positive, then `(q^d;q)_n` is positive for `0 < q < 1`.
This is the positivity input for every factor in the residual moment. -/
theorem qPochhammer_pow_pos_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (d : ℕ) (hd : 0 < d) (n : ℕ) :
    0 < qPochhammer (q ^ d) q n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [qPochhammer_succ]
      apply mul_pos ih
      have hpow : q ^ (d + n) < 1 :=
        pow_lt_one₀ hqpos.le hqone (by omega)
      rw [← pow_add]
      linarith

/-- A finite positive-index q-Pochhammer tail divided by `(q;q)_p` is a
Gaussian coefficient:

`(q^(a+1);q)_p / (q;q)_p = [a+p choose p]_q`.

This is the quotient bridge between the report's residual-product and
Gaussian-binomial presentations. -/
theorem qPochhammer_tail_div_self_eq_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (a p : ℕ) :
    qPochhammer (q ^ (a + 1)) q p / qPochhammer q q p =
      qBinomial (a + p) p q := by
  rw [qBinomial_eq_quotient q (by omega : p ≤ a + p),
    qPochhammer_self_add q a p, Nat.add_sub_cancel]
  have ha : qPochhammer q q a ≠ 0 :=
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone a).ne'
  have hp : qPochhammer q q p ≠ 0 :=
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne'
  field_simp [ha, hp]

/-- Report-facing Gaussian form of every residual power moment.  For
`0 < q < 1` and `p < m`,

`S_(p,m)(q) = (-1)^p q^choose(p+1,2) [m-1 choose p]_q`.

The proof is the positive-index residual q-Pochhammer formula followed by
`qPochhammer_tail_div_self_eq_qBinomial`; it does not invoke a second
interpolation argument. -/
theorem geometricLagrangeQMoment_eq_residual_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p m : ℕ) (hpm : p < m) :
    geometricLagrangeQMoment q p m =
      (-1 : ℚ) ^ p * q ^ (p + 1).choose 2 *
        qBinomial (m - 1) p q := by
  rw [geometricLagrangeQMoment_eq_residual_qPochhammer
    q hqpos.ne' p m
      (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne' hpm,
    mul_div_assoc]
  have hstart : m - p = (m - p - 1) + 1 := by omega
  have htop : m - p - 1 + p = m - 1 := by omega
  rw [hstart,
    qPochhammer_tail_div_self_eq_qBinomial
      q hqpos hqone (m - p - 1) p,
    htop]

/-- The first uncancelled geometric moment is the signed triangular power
`(-1)^p q^choose(p+1,2)`.  Only finite-node injectivity is needed. -/
theorem geometricLagrangeQMoment_firstUncancelled
    (q : ℚ) (p : ℕ)
    (hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1))) :
    geometricLagrangeQMoment q p (p + 1) =
      (-1 : ℚ) ^ p * q ^ (p + 1).choose 2 := by
  simpa only [geometricLagrangeQMoment, ← pow_mul, Nat.mul_comm] using
    sum_geometricLagrangeWeight_firstUncancelled q p hnodes

/-- Exact adjusted-sign identity for residual moments at `0 < q < 1`.
Multiplication by `(-1)^p` produces a strictly positive quotient.

This theorem records the parity content that is actually valid.  It does
not assert that two levels having the same parity are ordered. -/
theorem negOnePow_mul_geometricLagrangeQMoment_eq_positiveResidual
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p m : ℕ) (hpm : p < m) :
    (-1 : ℚ) ^ p * geometricLagrangeQMoment q p m =
      q ^ (p + 1).choose 2 * qPochhammer (q ^ (m - p)) q p /
        qPochhammer q q p := by
  have hsign : (-1 : ℚ) ^ p * (-1 : ℚ) ^ p = 1 :=
    neg_one_pow_mul_self p
  rw [geometricLagrangeQMoment_eq_residual_qPochhammer q hqpos.ne'
    p m (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne' hpm]
  calc
    (-1 : ℚ) ^ p *
        (((-1 : ℚ) ^ p * q ^ (p + 1).choose 2) *
          qPochhammer (q ^ (m - p)) q p /
            qPochhammer q q p) =
        (((-1 : ℚ) ^ p * (-1 : ℚ) ^ p) *
          q ^ (p + 1).choose 2 * qPochhammer (q ^ (m - p)) q p) /
            qPochhammer q q p := by ring
    _ = q ^ (p + 1).choose 2 * qPochhammer (q ^ (m - p)) q p /
          qPochhammer q q p := by rw [hsign, one_mul]

/-- Every residual moment has the exact sign `(-1)^p` when `0 < q < 1`:
after multiplication by that sign, it is strictly positive. -/
theorem negOnePow_mul_geometricLagrangeQMoment_pos
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p m : ℕ) (hpm : p < m) :
    0 < (-1 : ℚ) ^ p * geometricLagrangeQMoment q p m := by
  rw [negOnePow_mul_geometricLagrangeQMoment_eq_positiveResidual
    q hqpos hqone p m hpm]
  exact div_pos
    (mul_pos (pow_pos hqpos _)
      (qPochhammer_pow_pos_of_pos_of_lt_one
        q hqpos hqone (m - p) (by omega) p))
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p)

/-! ## A rational finite q-binomial theorem -/

/-- The self q-Pochhammer recurrence with its factor written as
`1 - q^(n+1)`. -/
theorem qPochhammer_self_succ (q : ℚ) (n : ℕ) :
    qPochhammer q q (n + 1) =
      qPochhammer q q n * (1 - q ^ (n + 1)) := by
  rw [qPochhammer_succ, pow_succ]
  ring

/-- Symmetric q-Pascal recurrence, in the orientation used by the finite
q-binomial theorem. -/
theorem qBinomial_succ_succ_of_pos_of_lt_one'
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (n k : ℕ) :
    qBinomial (n + 1) (k + 1) q =
      qBinomial n (k + 1) q + q ^ (n - k) * qBinomial n k q := by
  simpa only [gaussianBinomial_eq_qBinomial_of_pos_of_lt_one
      q hqpos hqone] using
    (gaussianBinomial_succ_succ q n k)

/-- The complementary q-Pascal recurrence for the quotient-defined Gaussian
coefficient.  It is the symmetric reflection of
`qBinomial_succ_succ_of_pos_of_lt_one'`. -/
theorem qBinomial_succ_succ_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (n k : ℕ) :
    qBinomial (n + 1) (k + 1) q =
      qBinomial n k q + q ^ (k + 1) * qBinomial n (k + 1) q := by
  by_cases hkn : k < n
  · have hk1n : k + 1 ≤ n := hkn
    have hk1n1 : k + 1 ≤ n + 1 := by omega
    calc
      qBinomial (n + 1) (k + 1) q =
          qBinomial (n + 1) ((n + 1) - (k + 1)) q :=
        (qBinomial_symm q hk1n1).symm
      _ = qBinomial (n + 1) ((n - (k + 1)) + 1) q := by
        rw [show (n + 1) - (k + 1) = (n - (k + 1)) + 1 by omega]
      _ = qBinomial n ((n - (k + 1)) + 1) q +
          q ^ (n - (n - (k + 1))) *
            qBinomial n (n - (k + 1)) q :=
        qBinomial_succ_succ_of_pos_of_lt_one'
          q hqpos hqone n (n - (k + 1))
      _ = qBinomial n k q +
          q ^ (k + 1) * qBinomial n (k + 1) q := by
        rw [show n - (k + 1) + 1 = n - k by omega,
          qBinomial_symm q hkn.le,
          Nat.sub_sub_self hk1n,
          qBinomial_symm q hk1n]
  · have hnk : n ≤ k := Nat.le_of_not_gt hkn
    have hPochhammerNe (r : ℕ) : qPochhammer q q r ≠ 0 :=
      (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone r).ne'
    rcases hnk.eq_or_lt with rfl | hnk
    · rw [qBinomial_eq_quotient q (le_refl (n + 1)),
        qBinomial_eq_quotient q (le_refl n),
        qBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
      simp [hPochhammerNe]
    · rw [qBinomial_eq_zero_of_lt q (by omega),
        qBinomial_eq_zero_of_lt q hnk,
        qBinomial_eq_zero_of_lt q (by omega)]
      ring

/-- **The finite q-binomial theorem at every non-root-of-unity `q`**:

`sum_(k=0)^n (-1)^k q^choose(k,2) [n choose k]_q z^k = (z;q)_n`

whenever `(q;q)_n ≠ 0`.  The interval `0 < q < 1` of the earlier statement
was used only to make the quotient denominators nonzero, and that is
exactly what `(q;q)_n ≠ 0` says; the identity is therefore available at
negative `q`, at `q > 1`, and at every `q` no power of which is a root of
unity.  No limiting or analytic argument appears. -/
theorem qBinomial_theorem_of_qPochhammer_ne_zero
    (q : ℚ) {n : ℕ} (hq : qPochhammer q q n ≠ 0) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * q ^ (k.choose 2) * qBinomial n k q * z ^ k) =
      qPochhammer z q n := by
  simpa only [gaussianBinomial_eq_qBinomial_of_qPochhammer_ne_zero q hq,
      finiteQPochhammerIn_rat_eq] using
    (finite_qBinomial_theorem q z n)

/-- Finite q-binomial theorem over the rational interval `0 < q < 1`, the
interval instance of `qBinomial_theorem_of_qPochhammer_ne_zero`. -/
theorem qBinomial_theorem_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * q ^ (k.choose 2) * qBinomial n k q * z ^ k) =
      qPochhammer z q n :=
  qBinomial_theorem_of_qPochhammer_ne_zero q
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone n).ne' z

/-- The positive triangular Gaussian sum is the numerator `(-q;q)_p` of
the exact condition number. -/
theorem sum_qBinomial_triangular_succ_eq_neg_qPochhammer
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (p : ℕ) :
    (∑ k ∈ Finset.range (p + 1),
      q ^ (k + 1).choose 2 * qBinomial p k q) =
      qPochhammer (-q) q p := by
  calc
    (∑ k ∈ Finset.range (p + 1),
        q ^ (k + 1).choose 2 * qBinomial p k q) =
        ∑ k ∈ Finset.range (p + 1),
          (-1 : ℚ) ^ k * q ^ (k.choose 2) *
            qBinomial p k q * (-q) ^ k := by
      apply Finset.sum_congr rfl
      intro k _hk
      have hsign : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 :=
        neg_one_pow_mul_self k
      have hneg : (-q) ^ k = (-1 : ℚ) ^ k * q ^ k := by
        rw [neg_pow]
      rw [choose_succ_two, pow_add, hneg]
      calc
        q ^ (k.choose 2) * q ^ k * qBinomial p k q =
            1 * q ^ (k.choose 2) * q ^ k * qBinomial p k q := by ring
        _ = ((-1 : ℚ) ^ k * (-1 : ℚ) ^ k) *
            q ^ (k.choose 2) * q ^ k * qBinomial p k q := by rw [hsign]
        _ = (-1 : ℚ) ^ k * q ^ (k.choose 2) *
            qBinomial p k q * ((-1 : ℚ) ^ k * q ^ k) := by ring
    _ = qPochhammer (-q) q p :=
      qBinomial_theorem_of_pos_of_lt_one q hqpos hqone p (-q)

/-! ## Exact total variation -/

private theorem
    geometricRootPolynomial_inv_eval_neg_one_mul_triangular
    (q : ℚ) (hq : q ≠ 0) (p : ℕ) :
    (geometricRootPolynomial q⁻¹ p).eval (-1) *
        q ^ (p + 1).choose 2 =
      qPochhammer (-q) q p := by
  rw [geometricRootPolynomial_eval]
  unfold qPochhammer finiteQPochhammer
  have hpow :
      q ^ (p + 1).choose 2 =
        ∏ r ∈ Finset.range p, q ^ (r + 1) := by
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    symm
    calc
      (∑ r ∈ Finset.range p, (r + 1)) =
          (∑ r ∈ Finset.range p, r) + p := by
        simp [Finset.sum_add_distrib]
      _ = p.choose 2 + p := by
        rw [Finset.sum_range_id, Nat.choose_two_right]
      _ = (p + 1).choose 2 := by
        rw [show p + 1 = p.succ by omega,
          show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp [Nat.choose_one_right, add_comm]
  rw [hpow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro r _hr
  simp only [inv_pow, pow_succ]
  field_simp [pow_ne_zero _ hq]
  all_goals ring

/-- Absolute value of one geometric weight in Gaussian form. -/
theorem abs_geometricLagrangeWeight_eq_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p k : ℕ) (hk : k ≤ p) :
    |geometricLagrangeWeight q p k| =
      q ^ (p - k + 1).choose 2 / qPochhammer q q p *
        qBinomial p k q := by
  rw [geometricLagrangeWeight_eq_qBinomial q hqpos.ne' p k hk
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne']
  rw [abs_mul, abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (pow_pos hqpos _),
    abs_of_pos (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p),
    abs_of_pos (qBinomial_pos_of_pos_of_lt_one q hqpos hqone hk)]
  ring

/-- The sign of the `k`th geometric Lagrange weight is exactly
`(-1)^(p-k)` in the conditioning range `0 < q < 1`. -/
theorem abs_geometricLagrangeWeight_eq_sign_mul
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p k : ℕ) (hk : k ≤ p) :
    |geometricLagrangeWeight q p k| =
      (-1 : ℚ) ^ (p - k) * geometricLagrangeWeight q p k := by
  have hPochhammer :=
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne'
  have hsign :
      (-1 : ℚ) ^ (p - k) * (-1 : ℚ) ^ (p - k) = 1 :=
    neg_one_pow_mul_self (p - k)
  rw [abs_geometricLagrangeWeight_eq_qBinomial q hqpos hqone p k hk,
    geometricLagrangeWeight_eq_qBinomial
      q hqpos.ne' p k hk hPochhammer]
  calc
    q ^ (p - k + 1).choose 2 / qPochhammer q q p *
        qBinomial p k q =
        1 * (q ^ (p - k + 1).choose 2 /
          qPochhammer q q p * qBinomial p k q) := by rw [one_mul]
    _ = ((-1 : ℚ) ^ (p - k) * (-1 : ℚ) ^ (p - k)) *
        (q ^ (p - k + 1).choose 2 /
          qPochhammer q q p * qBinomial p k q) := by rw [hsign]
    _ = (-1 : ℚ) ^ (p - k) *
        (((-1 : ℚ) ^ (p - k) * q ^ (p - k + 1).choose 2) /
          qPochhammer q q p * qBinomial p k q) := by ring

/-- Complement-index form of the absolute weight. -/
theorem abs_geometricLagrangeWeight_complement_eq_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p k : ℕ) (hk : k ≤ p) :
    |geometricLagrangeWeight q p (p - k)| =
      q ^ (k + 1).choose 2 / qPochhammer q q p *
        qBinomial p k q := by
  rw [abs_geometricLagrangeWeight_eq_qBinomial
    q hqpos hqone p (p - k) (Nat.sub_le p k),
    Nat.sub_sub_self hk, qBinomial_symm q hk]

/-- Exact finite `l1` norm of the geometric Lagrange weights:

`sum_(j=0)^p |lambda_(p,j)(q)| = (-q;q)_p / (q;q)_p`.

The only assumptions are the natural conditioning regime `0 < q < 1`. -/
theorem sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1),
      |geometricLagrangeWeight q p j|) =
      qPochhammer (-q) q p / qPochhammer q q p := by
  have hPochhammer : qPochhammer q q p ≠ 0 :=
    (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne'
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hqpos.ne' p hPochhammer'
  have hden : (geometricRootPolynomial q⁻¹ p).eval 1 ≠ 0 :=
    geometricRootPolynomial_inv_eval_one_ne_zero_of_nodes_injective
      q hqpos.ne' p hnodes
  have hsignSq : (-1 : ℚ) ^ p * (-1 : ℚ) ^ p = 1 :=
    neg_one_pow_mul_self p
  have hsubSign (k : ℕ) (hk : k ≤ p) :
      (-1 : ℚ) ^ (p - k) = (-1 : ℚ) ^ p * (-1 : ℚ) ^ k :=
    neg_one_pow_sub hk
  calc
    (∑ j ∈ Finset.range (p + 1),
        |geometricLagrangeWeight q p j|) =
        ∑ j ∈ Finset.range (p + 1),
          (-1 : ℚ) ^ (p - j) * geometricLagrangeWeight q p j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact abs_geometricLagrangeWeight_eq_sign_mul
        q hqpos hqone p j
          (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
    _ = (-1 : ℚ) ^ p *
        ∑ j ∈ Finset.range (p + 1),
          geometricLagrangeWeight q p j * (-1 : ℚ) ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [hsubSign j
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj))]
      ring
    _ = (-1 : ℚ) ^ p *
        (geometricLagrangeWeightPolynomial q p).eval (-1) := by
      rw [geometricLagrangeWeightPolynomial_eval]
      congr 1
      exact (Fin.sum_univ_eq_sum_range
        (fun j : ℕ ↦ geometricLagrangeWeight q p j * (-1 : ℚ) ^ j)
        (p + 1)).symm
    _ = (-1 : ℚ) ^ p *
        (forwardGeometricRichardsonPolynomial q p).eval (-1) := by
      rw [geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
        q hqpos.ne' p hnodes]
    _ = qPochhammer (-q) q p / qPochhammer q q p := by
      rw [forwardGeometricRichardsonPolynomial_eval]
      apply (eq_div_iff hPochhammer).2
      calc
        (-1 : ℚ) ^ p *
            ((geometricRootPolynomial q⁻¹ p).eval (-1) /
              (geometricRootPolynomial q⁻¹ p).eval 1) *
              qPochhammer q q p =
            (-1 : ℚ) ^ p *
              ((geometricRootPolynomial q⁻¹ p).eval (-1) /
                (geometricRootPolynomial q⁻¹ p).eval 1) *
              ((geometricRootPolynomial q⁻¹ p).eval 1 *
                ((-1 : ℚ) ^ p * q ^ (p + 1).choose 2)) := by
          rw [geometricRootPolynomial_inv_eval_one_mul_triangular
            q hqpos.ne' p]
        _ = ((-1 : ℚ) ^ p * (-1 : ℚ) ^ p) *
              ((geometricRootPolynomial q⁻¹ p).eval (-1) *
                q ^ (p + 1).choose 2) := by
          rw [div_eq_mul_inv]
          calc
            _ = (((-1 : ℚ) ^ p * (-1 : ℚ) ^ p) *
                  ((geometricRootPolynomial q⁻¹ p).eval (-1) *
                    q ^ (p + 1).choose 2)) *
                ((geometricRootPolynomial q⁻¹ p).eval 1 *
                  ((geometricRootPolynomial q⁻¹ p).eval 1)⁻¹) := by
              ring
            _ = _ := by rw [mul_inv_cancel₀ hden, mul_one]
        _ = (geometricRootPolynomial q⁻¹ p).eval (-1) *
              q ^ (p + 1).choose 2 := by rw [hsignSq, one_mul]
        _ = qPochhammer (-q) q p :=
          geometricRootPolynomial_inv_eval_neg_one_mul_triangular
            q hqpos.ne' p

/-- Product form of the exact condition number. -/
theorem neg_qPochhammer_div_self_eq_prod
    (q : ℚ) (p : ℕ) :
    qPochhammer (-q) q p / qPochhammer q q p =
      ∏ r ∈ Finset.range p,
        (1 + q ^ (r + 1)) / (1 - q ^ (r + 1)) := by
  rw [Finset.prod_div_distrib]
  unfold qPochhammer finiteQPochhammer
  congr 1
  · apply Finset.prod_congr rfl
    intro r _hr
    rw [pow_succ]
    ring
  · apply Finset.prod_congr rfl
    intro r _hr
    rw [pow_succ]
    ring

/-- Exact product formula for the `l1` norm of the geometric weights. -/
theorem sum_abs_geometricLagrangeWeight_eq_prod
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1),
      |geometricLagrangeWeight q p j|) =
      ∏ r ∈ Finset.range p,
        (1 + q ^ (r + 1)) / (1 - q ^ (r + 1)) := by
  rw [sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio
    q hqpos hqone p, neg_qPochhammer_div_self_eq_prod]

/-! ## The quarter-base specialization -/

/-- Full residual moment formula for the dyadic sinc-tail base `q = 1/4`. -/
theorem quarterGeometricLagrangeQMoment_eq_qPochhammer
    (p m : ℕ) :
    geometricLagrangeQMoment (1 / 4 : ℚ) p m =
      (1 / 4 : ℚ) ^ (p * m) *
          qPochhammer ((1 / 4 : ℚ) / (1 / 4 : ℚ) ^ m)
            (1 / 4 : ℚ) p /
        qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) p := by
  exact geometricLagrangeQMoment_eq_qPochhammer
    (1 / 4 : ℚ) (by norm_num) p m (quarter_qPochhammer_self_ne_zero p)

/-- Every positive dyadic q-moment through degree `p` vanishes. -/
theorem quarterGeometricLagrangeQMoment_eq_zero
    (p m : ℕ) (hmpos : 0 < m) (hmp : m ≤ p) :
    geometricLagrangeQMoment (1 / 4 : ℚ) p m = 0 := by
  exact geometricLagrangeQMoment_eq_zero
    (1 / 4 : ℚ) (by norm_num) p m
      (quarter_qPochhammer_self_ne_zero p) hmpos hmp

/-- Positive-index residual product for the dyadic base `q = 1/4`. -/
theorem quarterGeometricLagrangeQMoment_eq_residual_qPochhammer
    (p m : ℕ) (hpm : p < m) :
    geometricLagrangeQMoment (1 / 4 : ℚ) p m =
      ((-1 : ℚ) ^ p * (1 / 4 : ℚ) ^ (p + 1).choose 2) *
          qPochhammer ((1 / 4 : ℚ) ^ (m - p)) (1 / 4 : ℚ) p /
        qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) p := by
  exact geometricLagrangeQMoment_eq_residual_qPochhammer
    (1 / 4 : ℚ) (by norm_num) p m
      (quarter_qPochhammer_self_ne_zero p) hpm

/-- Report-facing Gaussian-binomial residual formula at `q = 1/4`. -/
theorem quarterGeometricLagrangeQMoment_eq_residual_qBinomial
    (p m : ℕ) (hpm : p < m) :
    geometricLagrangeQMoment (1 / 4 : ℚ) p m =
      (-1 : ℚ) ^ p * (1 / 4 : ℚ) ^ (p + 1).choose 2 *
        qBinomial (m - 1) p (1 / 4 : ℚ) := by
  exact geometricLagrangeQMoment_eq_residual_qBinomial
    (1 / 4 : ℚ) (by norm_num) (by norm_num) p m hpm

/-- The first uncancelled quarter-base moment. -/
theorem quarterGeometricLagrangeQMoment_firstUncancelled (p : ℕ) :
    geometricLagrangeQMoment (1 / 4 : ℚ) p (p + 1) =
      (-1 : ℚ) ^ p * (1 / 4 : ℚ) ^ (p + 1).choose 2 := by
  exact geometricLagrangeQMoment_firstUncancelled
    (1 / 4 : ℚ) p (quarter_pow_injOn p)

/-- Exact `l1` norm of the dyadic geometric weights. -/
theorem sum_abs_quarterGeometricLagrangeWeight_eq_qPochhammer_ratio
    (p : ℕ) :
    (∑ j ∈ Finset.range (p + 1),
      |geometricLagrangeWeight (1 / 4 : ℚ) p j|) =
      qPochhammer (-1 / 4 : ℚ) (1 / 4 : ℚ) p /
        qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) p := by
  simpa only [neg_div] using
    sum_abs_geometricLagrangeWeight_eq_qPochhammer_ratio
      (1 / 4 : ℚ) (by norm_num) (by norm_num) p

end Fabius

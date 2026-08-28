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

The all-index q-Pochhammer formula evaluates the coefficient polynomial from
`GeometricLagrangeWeights` and clears its common signed geometric product.
For positive indices, the canonical denominator-free theorem from
`GeometricQBinomialLagrange` gives the Gaussian coefficient directly; the
q-factorial identity then recovers the equivalent positive-index form

`S_(p,m)(q) = (-1)^p q^choose(p+1,2)
  (q^(m-p); q)_p / (q; q)_p`

when `p < m`.  Hence, for `0 < q < 1`, multiplication by `(-1)^p` makes
every residual moment strictly positive.  This is a statement about the sign
at one fixed Richardson level.  It deliberately makes no comparison between
two levels of the same parity: the corrected frontier report gives explicit
admissible counterexamples to such monotonicity.

The second half specializes the ring-generic finite q-binomial theorem to
the repository's quotient-defined rational coefficient for every
`0 < q < 1`, extending the existing `q = 1/2` specialization in
`HalfQBinomial`.  It is then used to compute the exact total variation

`sum_j |lambda_(p,j)(q)| = (-q; q)_p / (q; q)_p
  = product_(r=1)^p (1+q^r)/(1-q^r)`.

All results here are finite algebraic identities.  There are no analytic
convergence, sinc-tail, bracketing, or asymptotic claims.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

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
    geometricLagrangeWeightPolynomial_eval,
    Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [pow_mul, pow_mul, Nat.mul_comm]

/-- Under the exact finite noncollision hypotheses, every geometric moment
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
      <;> ring
    _ = q ^ (p * m) * qPochhammer (q / q ^ m) q p := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_range]
      rw [pow_mul, Nat.mul_comm m p]
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
    geometricRootPolynomial_inv_eval_one_mul_signedPowers q hq p]
  rw [← geometricQPochhammer_rat_eq_qPochhammer]
  rfl

/-! ## All rational power moments -/

/-- Full q-Pochhammer formula for every power moment:

`S_(p,m)(q) = q^(p*m) (q/q^m;q)_p / (q;q)_p`.

The hypotheses say exactly that `q` is nonzero and the finite Gaussian
denominator does not vanish.  Equivalently, the nodes `1,q,...,q^p` are
distinct and the quotient presentation is legitimate. -/
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
  exact sum_geometricLagrangeWeight q p hnodes

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
  rw [geometricLagrangeQMoment,
    sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial
      q p m hnodes hmpos,
    gaussianBinomial_eq_zero_of_lt q (by omega : m - 1 < p)]
  ring

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
  have hfactorial :
      qPochhammer q q p * gaussianBinomial q (m - 1) p =
        qPochhammer (q ^ (m - p)) q p := by
    simpa only [finiteQPochhammerIn_rat_eq,
      show m - 1 - p + 1 = m - p by omega] using
      (finiteQPochhammerIn_self_mul_gaussianBinomial
        q (n := m - 1) (k := p) (by omega : p ≤ m - 1))
  have hgaussian :
      gaussianBinomial q (m - 1) p =
        qPochhammer (q ^ (m - p)) q p / qPochhammer q q p := by
    apply (eq_div_iff hPochhammer).2
    rw [← hfactorial]
    ring
  have htriangular :
      p * (p + 1) / 2 = (p + 1).choose 2 := by
    simp [Nat.choose_two_right, Nat.mul_comm]
  rw [geometricLagrangeQMoment,
    sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial
      q p m hnodes (by omega),
    htriangular, hgaussian]
  ring

/-- Splitting a self q-Pochhammer product after its first `a` factors:

`(q;q)_(a+p) = (q;q)_a (q^(a+1);q)_p`.

This finite identity is valid for every rational `q`; no nonvanishing or
order hypothesis is needed. -/
theorem qPochhammer_self_add (q : ℚ) (a p : ℕ) :
    qPochhammer q q (a + p) =
      qPochhammer q q a * qPochhammer (q ^ (a + 1)) q p := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Nat.add_succ, qPochhammer_succ q q (a + p), ih,
        qPochhammer_succ (q ^ (a + 1)) q p]
      have hfactor : q * q ^ (a + p) = q ^ (a + 1) * q ^ p := by
        calc
          q * q ^ (a + p) = q ^ 1 * q ^ (a + p) := by rw [pow_one]
          _ = q ^ (1 + (a + p)) := by rw [← pow_add]
          _ = q ^ ((a + 1) + p) := by
            congr 1
            omega
          _ = q ^ (a + 1) * q ^ p := by rw [pow_add]
      rw [hfactor]
      ring

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

/-- On `0 < q < 1`, the repository's quotient-defined rational
`qBinomial` agrees with the denominator-free Gaussian coefficient from the
finite q-binomial core.

The proof is the denominator-free q-factorial identity followed by one
legitimate cancellation.  In particular, it does not replay q-Pascal. -/
theorem gaussianBinomial_eq_qBinomial_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (n k : ℕ) :
    gaussianBinomial q n k = qBinomial n k q := by
  by_cases hk : k ≤ n
  · have hkNe : qPochhammer q q k ≠ 0 :=
      (qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone k).ne'
    have hnkNe : qPochhammer q q (n - k) ≠ 0 :=
      (qPochhammer_self_pos_of_pos_of_lt_one
        q hqpos hqone (n - k)).ne'
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
    field_simp [hkNe, hnkNe] <;> ring
  · have hkn : n < k := Nat.lt_of_not_ge hk
    rw [gaussianBinomial_eq_zero_of_lt q hkn,
      qBinomial_eq_zero_of_lt q hkn]

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
  field_simp [ha, hp] <;> ring

/-- Report-facing Gaussian form of every residual power moment.  For
`0 < q < 1` and `p < m`,

`S_(p,m)(q) = (-1)^p q^choose(p+1,2) [m-1 choose p]_q`.

This is a direct rational specialization of the canonical denominator-free
Gaussian/Lagrange residual theorem. -/
theorem geometricLagrangeQMoment_eq_residual_qBinomial
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (p m : ℕ) (hpm : p < m) :
    geometricLagrangeQMoment q p m =
      (-1 : ℚ) ^ p * q ^ (p + 1).choose 2 *
        qBinomial (m - 1) p q := by
  have hPochhammer : geometricQPochhammer q p ≠ 0 := by
    rw [geometricQPochhammer_rat_eq_qPochhammer]
    exact (qPochhammer_self_pos_of_pos_of_lt_one
      q hqpos hqone p).ne'
  have hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hqpos.ne' p hPochhammer
  have htriangular :
      p * (p + 1) / 2 = (p + 1).choose 2 := by
    simp [Nat.choose_two_right, Nat.mul_comm]
  rw [geometricLagrangeQMoment,
    sum_geometricLagrangeWeight_mul_pow_eq_gaussianBinomial
      q p m hnodes (by omega),
    htriangular,
    gaussianBinomial_eq_qBinomial_of_pos_of_lt_one
      q hqpos hqone (m - 1) p]

/-- The first uncancelled geometric moment is the signed triangular power
`(-1)^p q^choose(p+1,2)`. -/
theorem geometricLagrangeQMoment_firstUncancelled
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1) (p : ℕ) :
    geometricLagrangeQMoment q p (p + 1) =
      (-1 : ℚ) ^ p * q ^ (p + 1).choose 2 := by
  rw [geometricLagrangeQMoment_eq_residual_qBinomial
    q hqpos hqone p (p + 1) (Nat.lt_succ_self p)]
  rw [show p + 1 - 1 = p by omega,
    qBinomial_eq_quotient q (le_refl p)]
  simp [(qPochhammer_self_pos_of_pos_of_lt_one q hqpos hqone p).ne']

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
  have hsign : (-1 : ℚ) ^ p * (-1 : ℚ) ^ p = 1 := by
    rw [← mul_pow]
    norm_num
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

/-- The complementary q-Pascal recurrence for the repository's
quotient-defined Gaussian coefficient.  It is the symmetric reflection of
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

/-- Finite q-binomial theorem over the rational interval `0 < q < 1`:

`sum_(k=0)^n (-1)^k q^choose(k,2) [n choose k]_q z^k = (z;q)_n`.

The interval hypothesis is used only to make every quotient denominator
nonzero; no limiting or analytic argument appears. -/
theorem qBinomial_theorem_of_pos_of_lt_one
    (q : ℚ) (hqpos : 0 < q) (hqone : q < 1)
    (n : ℕ) (z : ℚ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ k * q ^ (k.choose 2) * qBinomial n k q * z ^ k) =
      qPochhammer z q n := by
  simpa only [gaussianBinomial_eq_qBinomial_of_pos_of_lt_one
      q hqpos hqone, finiteQPochhammerIn_rat_eq] using
    (finite_qBinomial_theorem q z n)

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
      have hsign : (-1 : ℚ) ^ k * (-1 : ℚ) ^ k = 1 := by
        rw [← mul_pow]
        norm_num
      rw [choose_succ_two, pow_add, neg_pow]
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

/-- Complement-index form of the absolute weight, prepared for the finite
q-binomial theorem. -/
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
  calc
    (∑ j ∈ Finset.range (p + 1),
        |geometricLagrangeWeight q p j|) =
        ∑ k ∈ Finset.range (p + 1),
          |geometricLagrangeWeight q p (p - k)| := by
      rw [← Finset.sum_range_reflect
        (fun j ↦ |geometricLagrangeWeight q p j|) (p + 1)]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [show p + 1 - 1 - k = p - k by omega]
    _ = ∑ k ∈ Finset.range (p + 1),
          (q ^ (k + 1).choose 2 / qPochhammer q q p *
            qBinomial p k q) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact abs_geometricLagrangeWeight_complement_eq_qBinomial
        q hqpos hqone p k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = (1 / qPochhammer q q p) *
          ∑ k ∈ Finset.range (p + 1),
            (q ^ (k + 1).choose 2 * qBinomial p k q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      ring
    _ = qPochhammer (-q) q p / qPochhammer q q p := by
      rw [sum_qBinomial_triangular_succ_eq_neg_qPochhammer
        q hqpos hqone p]
      ring

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
    (1 / 4 : ℚ) (by norm_num) (by norm_num) p

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

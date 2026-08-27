import FabiusFunction.GeometricLagrangeWeights
import FabiusFunction.HalfQBinomial
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Explicit Gaussian formulas for geometric Lagrange weights

The canonical geometric Lagrange weights from `GeometricLagrange`, and the
coefficient-polynomial bridge in `GeometricLagrangeWeights`, are defined
intrinsically from cardinal interpolation on the nodes

`1, q, ..., q^p`.

This module computes those weights.  If

`(q;q)_n = product_{r=1}^n (1 - q^r)`,

then the weight at `q^j` is

`(-1)^(p-j) q^choose(p-j+1,2) / ((q;q)_j (q;q)_(p-j))`.

The proof is direct and explains every part of the answer.  Factors below
the chosen node reverse to `(q;q)_j`; factors above it contribute the sign
and triangular power of `q`, together with `(q;q)_(p-j)`.  This product
argument is valid over every field as soon as `q` is nonzero.  It does not
pretend that a quotient-defined Gaussian binomial has a polynomial
continuation at roots of unity.

Over `Q`, when `(q;q)_p` is nonzero, cancellation gives the equivalent
Gaussian form

`weight_j = (-1)^(p-j) q^choose(p-j+1,2) / (q;q)_p * QBinomial[p,j,q]`.

The nonvanishing hypothesis is characterized exactly by the absence of a
root of unity among `q, ..., q^p`.  At `q = 1/4` it is automatic, so both the
Lagrange weights and the coefficients of the forward Richardson polynomial
have unconditional closed forms.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Fabius

section FieldPochhammer

variable {K : Type*} [Field K]

/-- The field-valued finite product `(q;q)_n = product_{r=1}^n (1-q^r)`.

Unlike the rational `qPochhammer` from `HalfQBinomial`, this definition is
available over an arbitrary field. -/
noncomputable def geometricQPochhammer (q : K) (n : ℕ) : K :=
  ∏ r ∈ Finset.range n, (1 - q ^ (r + 1))

/-- The empty geometric q-Pochhammer product is one. -/
@[simp] theorem geometricQPochhammer_zero (q : K) :
    geometricQPochhammer q 0 = 1 := by
  simp [geometricQPochhammer]

/-- Peeling the last factor from `(q;q)_(n+1)`. -/
theorem geometricQPochhammer_succ (q : K) (n : ℕ) :
    geometricQPochhammer q (n + 1) =
      geometricQPochhammer q n * (1 - q ^ (n + 1)) := by
  simp [geometricQPochhammer, Finset.prod_range_succ]

/-- The finite product `(q;q)_n` is nonzero exactly when none of
`q, q^2, ..., q^n` is one.  This is the precise finite non-root-of-unity
condition needed for Gaussian-quotient cancellation. -/
theorem geometricQPochhammer_ne_zero_iff (q : K) (n : ℕ) :
    geometricQPochhammer q n ≠ 0 ↔
      ∀ r < n, q ^ (r + 1) ≠ 1 := by
  unfold geometricQPochhammer
  rw [Finset.prod_ne_zero_iff]
  constructor
  · intro h r hr hpow
    exact h r (Finset.mem_range.mpr hr) (sub_eq_zero.mpr hpow.symm)
  · intro h r hr
    exact sub_ne_zero.mpr (h r (Finset.mem_range.mp hr)).symm

/-- A nonzero base with `(q;q)_p != 0` has distinct powers
`1, q, ..., q^p`.  Thus the finite Pochhammer denominator is not merely an
algebraic side condition: it directly supplies the regularity needed by
geometric interpolation. -/
theorem pow_injOn_range_of_geometricQPochhammer_ne_zero
    (q : K) (hq : q ≠ 0) (p : ℕ)
    (hPochhammer : geometricQPochhammer q p ≠ 0) :
    Set.InjOn (fun j : ℕ ↦ q ^ j) (Finset.range (p + 1)) := by
  have hroot : ∀ d : ℕ, 0 < d → d ≤ p → q ^ d ≠ 1 := by
    intro d hd hdp
    have hne := (geometricQPochhammer_ne_zero_iff q p).mp hPochhammer
      (d - 1) (by omega)
    have hexponent : d - 1 + 1 = d := by omega
    rwa [hexponent] at hne
  intro i hi j hj hij
  have hip : i ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hjp : j ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hijlt | hjilt
  · have hfactor :
        q ^ i * q ^ (j - i) = q ^ i * 1 := by
      calc
        q ^ i * q ^ (j - i) = q ^ j := by
          rw [← pow_add, Nat.add_sub_of_le hijlt.le]
        _ = q ^ i := hij.symm
        _ = q ^ i * 1 := by ring
    have hone : q ^ (j - i) = 1 :=
      mul_left_cancel₀ (pow_ne_zero i hq) hfactor
    exact hroot (j - i) (by omega) (by omega) hone
  · have hfactor :
        q ^ j * q ^ (i - j) = q ^ j * 1 := by
      calc
        q ^ j * q ^ (i - j) = q ^ i := by
          rw [← pow_add, Nat.add_sub_of_le hjilt.le]
        _ = q ^ j := hij
        _ = q ^ j * 1 := by ring
    have hone : q ^ (i - j) = 1 :=
      mul_left_cancel₀ (pow_ne_zero j hq) hfactor
    exact hroot (i - j) (by omega) (by omega) hone

private theorem lower_geometric_lagrange_factor
    (q : K) (hq : q ≠ 0) {a b : ℕ} (hab : a < b) :
    (-(q ^ a)) / (q ^ b - q ^ a) =
      1 / (1 - q ^ (b - a)) := by
  have ha0 : q ^ a ≠ 0 := pow_ne_zero a hq
  have hpow : q ^ b = q ^ a * q ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab.le]
  calc
    (-(q ^ a)) / (q ^ b - q ^ a) =
        (q ^ a * (-1)) / (q ^ a * (q ^ (b - a) - 1)) := by
          rw [hpow]
          congr 1 <;> ring
    _ = (-1) / (q ^ (b - a) - 1) :=
      mul_div_mul_left (-1) (q ^ (b - a) - 1) ha0
    _ = 1 / (1 - q ^ (b - a)) := by
      rw [show q ^ (b - a) - 1 = -(1 - q ^ (b - a)) by ring]
      simp

private theorem upper_geometric_lagrange_factor
    (q : K) (hq : q ≠ 0) {a b : ℕ} (hab : a < b) :
    (-(q ^ b)) / (q ^ a - q ^ b) =
      (-(q ^ (b - a))) / (1 - q ^ (b - a)) := by
  have ha0 : q ^ a ≠ 0 := pow_ne_zero a hq
  have hpow : q ^ b = q ^ a * q ^ (b - a) := by
    rw [← pow_add, Nat.add_sub_of_le hab.le]
  calc
    (-(q ^ b)) / (q ^ a - q ^ b) =
        (q ^ a * (-(q ^ (b - a)))) /
          (q ^ a * (1 - q ^ (b - a))) := by
            rw [hpow]
            congr 1 <;> ring
    _ = (-(q ^ (b - a))) / (1 - q ^ (b - a)) :=
      mul_div_mul_left (-(q ^ (b - a))) (1 - q ^ (b - a)) ha0

private theorem prod_range_geometric_lagrange_factor
    (q : K) (hq : q ≠ 0) (k : ℕ) :
    (∏ l ∈ Finset.range k,
        (-(q ^ l)) / (q ^ k - q ^ l)) =
      (geometricQPochhammer q k)⁻¹ := by
  calc
    (∏ l ∈ Finset.range k,
        (-(q ^ l)) / (q ^ k - q ^ l)) =
        ∏ l ∈ Finset.range k, (1 - q ^ (k - l))⁻¹ := by
          apply Finset.prod_congr rfl
          intro l hl
          rw [← one_div]
          exact lower_geometric_lagrange_factor q hq
            (Finset.mem_range.mp hl)
    _ = (∏ l ∈ Finset.range k, (1 - q ^ (k - l)))⁻¹ := by
      rw [Finset.prod_inv_distrib]
    _ = (geometricQPochhammer q k)⁻¹ := by
      congr 1
      unfold geometricQPochhammer
      calc
        (∏ l ∈ Finset.range k, (1 - q ^ (k - l))) =
            ∏ l ∈ Finset.range k,
              (1 - q ^ ((k - 1 - l) + 1)) := by
                apply Finset.prod_congr rfl
                intro l hl
                have hlk : l < k := Finset.mem_range.mp hl
                have hexponent : k - l = (k - 1 - l) + 1 := by omega
                rw [hexponent]
        _ = ∏ l ∈ Finset.range k, (1 - q ^ (l + 1)) :=
          Finset.prod_range_reflect (fun l ↦ 1 - q ^ (l + 1)) k

private theorem prod_Ico_geometric_lagrange_factor
    (q : K) (hq : q ≠ 0) (p k : ℕ) (hk : k ≤ p) :
    (∏ l ∈ Finset.Ico (k + 1) (p + 1),
        (-(q ^ l)) / (q ^ k - q ^ l)) =
      ((-1 : K) ^ (p - k) * q ^ (p - k + 1).choose 2) /
        geometricQPochhammer q (p - k) := by
  calc
    (∏ l ∈ Finset.Ico (k + 1) (p + 1),
        (-(q ^ l)) / (q ^ k - q ^ l)) =
        ∏ l ∈ Finset.Ico (k + 1) (p + 1),
          (-(q ^ (l - k))) / (1 - q ^ (l - k)) := by
          apply Finset.prod_congr rfl
          intro l hl
          have hkl : k + 1 ≤ l := (Finset.mem_Ico.mp hl).1
          exact upper_geometric_lagrange_factor q hq
            (by omega : k < l)
    _ = ∏ r ∈ Finset.range (p - k),
          (-(q ^ (r + 1))) / (1 - q ^ (r + 1)) := by
      rw [Finset.prod_Ico_eq_prod_range]
      have hlength : p + 1 - (k + 1) = p - k := by omega
      rw [hlength]
      apply Finset.prod_congr rfl
      intro r _hr
      have hexponent : k + 1 + r - k = r + 1 := by omega
      rw [hexponent]
    _ = (∏ r ∈ Finset.range (p - k), -(q ^ (r + 1))) /
          ∏ r ∈ Finset.range (p - k), (1 - q ^ (r + 1)) := by
      rw [Finset.prod_div_distrib]
    _ = ((-1 : K) ^ (p - k) * q ^ (p - k + 1).choose 2) /
        geometricQPochhammer q (p - k) := by
      rw [prod_neg_geometric_powers]
      rfl

/-- Explicit q-Pochhammer formula for the Lagrange weight on
`1, q, ..., q^p`:

`lambda_(p,j) = (-1)^(p-j) q^choose(p-j+1,2) /
  ((q;q)_j (q;q)_(p-j))`.

Only `q != 0` is needed.  In particular, this raw quotient identity remains
valid at roots of unity; no cancellation of a vanishing `(q;q)_p` is made.
When powers of `q` collide, however, this describes Lean's totalized basis
expression only: interpolation exactness still requires distinct nodes. -/
theorem geometricLagrangeWeight_eq_geometricQPochhammer
    (q : K) (hq : q ≠ 0) (p k : ℕ) (hk : k ≤ p) :
    geometricLagrangeWeight q p k =
      ((-1 : K) ^ (p - k) * q ^ (p - k + 1).choose 2) /
        (geometricQPochhammer q k * geometricQPochhammer q (p - k)) := by
  rw [geometricLagrangeWeight_eq_product]
  have herase :
      (Finset.range (p + 1)).erase k =
        Finset.range k ∪ Finset.Ico (k + 1) (p + 1) := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union,
      Finset.mem_Ico]
    omega
  have hdis :
      Disjoint (Finset.range k) (Finset.Ico (k + 1) (p + 1)) := by
    rw [Finset.disjoint_left]
    intro l hlower hupper
    have hlk : l < k := Finset.mem_range.mp hlower
    have hkl : k + 1 ≤ l := (Finset.mem_Ico.mp hupper).1
    omega
  rw [herase, Finset.prod_union hdis,
    prod_range_geometric_lagrange_factor q hq k,
    prod_Ico_geometric_lagrange_factor q hq p k hk]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- Coefficient extraction for the geometric-weight generating polynomial:
its coefficient of `X^j` is exactly the `j`-th Lagrange weight. -/
@[simp] theorem geometricLagrangeWeightPolynomial_coeff
    (q : K) (p : ℕ) (j : Fin (p + 1)) :
    (geometricLagrangeWeightPolynomial q p).coeff (j : ℕ) =
      geometricLagrangeWeight q p (j : ℕ) := by
  classical
  unfold geometricLagrangeWeightPolynomial
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _hi hij
    have hval : (j : ℕ) ≠ (i : ℕ) := by
      intro h
      exact hij (Fin.ext h.symm)
    simp [hval]
  · simp

/-- Field-generic coefficient formula for the forward Richardson polynomial.
The distinct-node hypothesis is exactly what identifies its coefficients
with the Lagrange weights. -/
theorem forwardGeometricRichardsonPolynomial_coeff_eq_geometricQPochhammer
    (q : K) (hq : q ≠ 0) (p : ℕ)
    (hnodes : Set.InjOn (fun j : ℕ ↦ q ^ j) (Finset.range (p + 1)))
    (j : Fin (p + 1)) :
    (forwardGeometricRichardsonPolynomial q p).coeff (j : ℕ) =
      ((-1 : K) ^ (p - (j : ℕ)) *
          q ^ (p - (j : ℕ) + 1).choose 2) /
        (geometricQPochhammer q (j : ℕ) *
          geometricQPochhammer q (p - (j : ℕ))) := by
  rw [← geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
    q hq p hnodes, geometricLagrangeWeightPolynomial_coeff]
  exact geometricLagrangeWeight_eq_geometricQPochhammer
    q hq p (j : ℕ) (Nat.le_of_lt_succ j.isLt)

end FieldPochhammer

section RationalGaussian

/-- Over the rationals, the field-generic product `(q;q)_n` is exactly the
repository's Wolfram-notation-compatible `qPochhammer q q n`. -/
theorem geometricQPochhammer_rat_eq_qPochhammer (q : ℚ) (n : ℕ) :
    geometricQPochhammer q n = qPochhammer q q n := by
  change (∏ r ∈ Finset.range n, (1 - q ^ (r + 1))) =
    ∏ r ∈ Finset.range n, (1 - q * q ^ r)
  apply Finset.prod_congr rfl
  intro r _hr
  rw [pow_succ]
  ring

/-- Exact finite non-root-of-unity criterion for the rational denominator
`(q;q)_n`. -/
theorem qPochhammer_self_ne_zero_iff (q : ℚ) (n : ℕ) :
    qPochhammer q q n ≠ 0 ↔
      ∀ r < n, q ^ (r + 1) ≠ 1 := by
  rw [← geometricQPochhammer_rat_eq_qPochhammer]
  exact geometricQPochhammer_ne_zero_iff q n

/-- Rational q-Pochhammer form of the explicit geometric Lagrange weight. -/
theorem geometricLagrangeWeight_eq_qPochhammer
    (q : ℚ) (hq : q ≠ 0) (p k : ℕ) (hk : k ≤ p) :
    geometricLagrangeWeight q p k =
      ((-1 : ℚ) ^ (p - k) * q ^ (p - k + 1).choose 2) /
        (qPochhammer q q k * qPochhammer q q (p - k)) := by
  simpa only [geometricQPochhammer_rat_eq_qPochhammer] using
    geometricLagrangeWeight_eq_geometricQPochhammer q hq p k hk

/-- Gaussian-binomial form of the geometric Lagrange weight.  The explicit
hypothesis `(q;q)_p != 0` is essential: `qBinomial` in this repository is a
quotient, not its polynomial continuation at roots of unity. -/
theorem geometricLagrangeWeight_eq_qBinomial
    (q : ℚ) (hq : q ≠ 0) (p k : ℕ) (hk : k ≤ p)
    (hPochhammer : qPochhammer q q p ≠ 0) :
    geometricLagrangeWeight q p k =
      (((-1 : ℚ) ^ (p - k) * q ^ (p - k + 1).choose 2) /
        qPochhammer q q p) * qBinomial p k q := by
  rw [geometricLagrangeWeight_eq_qPochhammer q hq p k hk]
  rw [qBinomial_eq_quotient q hk]
  rw [← mul_div_assoc, div_mul_cancel₀ _ hPochhammer]

/-- Rational Gaussian-binomial coefficient formula for the forward
Richardson polynomial.  Distinct geometric nodes identify the Richardson
coefficients with Lagrange weights, while `(q;q)_p != 0` justifies the
Gaussian quotient cancellation. -/
theorem forwardGeometricRichardsonPolynomial_coeff_eq_qBinomial
    (q : ℚ) (hq : q ≠ 0) (p : ℕ) (j : Fin (p + 1))
    (hPochhammer : qPochhammer q q p ≠ 0) :
    (forwardGeometricRichardsonPolynomial q p).coeff (j : ℕ) =
      (((-1 : ℚ) ^ (p - (j : ℕ)) *
          q ^ (p - (j : ℕ) + 1).choose 2) /
        qPochhammer q q p) * qBinomial p (j : ℕ) q := by
  have hPochhammer' : geometricQPochhammer q p ≠ 0 := by
    rwa [geometricQPochhammer_rat_eq_qPochhammer]
  have hnodes : Set.InjOn (fun i : ℕ ↦ q ^ i)
      (Finset.range (p + 1)) :=
    pow_injOn_range_of_geometricQPochhammer_ne_zero
      q hq p hPochhammer'
  rw [← geometricLagrangeWeightPolynomial_eq_forwardGeometricRichardsonPolynomial
    q hq p hnodes, geometricLagrangeWeightPolynomial_coeff]
  exact geometricLagrangeWeight_eq_qBinomial
    q hq p (j : ℕ) (Nat.le_of_lt_succ j.isLt) hPochhammer

/-- At `q = 1/4`, every finite Gaussian denominator `(q;q)_n` is nonzero. -/
theorem quarter_qPochhammer_self_ne_zero (n : ℕ) :
    qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) n ≠ 0 := by
  rw [qPochhammer_self_ne_zero_iff]
  intro r _hr
  exact ne_of_lt (pow_lt_one₀
    (by norm_num : (0 : ℚ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℚ) < 1)
    (by omega : r + 1 ≠ 0))

/-- Unconditional q-Pochhammer formula for the Lagrange weights on the
quarter-geometric nodes `1, 1/4, ..., (1/4)^p`. -/
theorem quarterLagrangeWeight_eq_qPochhammer
    (p k : ℕ) (hk : k ≤ p) :
    geometricLagrangeWeight (1 / 4 : ℚ) p k =
      ((-1 : ℚ) ^ (p - k) *
          (1 / 4 : ℚ) ^ (p - k + 1).choose 2) /
        (qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) k *
          qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) (p - k)) := by
  exact geometricLagrangeWeight_eq_qPochhammer
    (1 / 4 : ℚ) (by norm_num) p k hk

/-- Unconditional Gaussian-binomial formula for the Lagrange weights on the
quarter-geometric nodes. -/
theorem quarterLagrangeWeight_eq_qBinomial
    (p k : ℕ) (hk : k ≤ p) :
    geometricLagrangeWeight (1 / 4 : ℚ) p k =
      (((-1 : ℚ) ^ (p - k) *
          (1 / 4 : ℚ) ^ (p - k + 1).choose 2) /
        qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) p) *
          qBinomial p k (1 / 4 : ℚ) := by
  exact geometricLagrangeWeight_eq_qBinomial
    (1 / 4 : ℚ) (by norm_num) p k hk
      (quarter_qPochhammer_self_ne_zero p)

/-- The coefficients of the quarter-base forward Richardson polynomial are
the explicit q-Pochhammer weights. -/
theorem quarterForwardRichardsonPolynomial_coeff_eq_qPochhammer
    (p : ℕ) (j : Fin (p + 1)) :
    (forwardGeometricRichardsonPolynomial (1 / 4 : ℚ) p).coeff (j : ℕ) =
      ((-1 : ℚ) ^ (p - (j : ℕ)) *
          (1 / 4 : ℚ) ^ (p - (j : ℕ) + 1).choose 2) /
        (qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) (j : ℕ) *
          qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) (p - (j : ℕ))) := by
  simpa only [geometricQPochhammer_rat_eq_qPochhammer] using
    forwardGeometricRichardsonPolynomial_coeff_eq_geometricQPochhammer
      (1 / 4 : ℚ) (by norm_num) p (quarter_pow_injOn p) j

/-- The coefficients of the quarter-base forward Richardson polynomial in
Gaussian-binomial form. -/
theorem quarterForwardRichardsonPolynomial_coeff_eq_qBinomial
    (p : ℕ) (j : Fin (p + 1)) :
    (forwardGeometricRichardsonPolynomial (1 / 4 : ℚ) p).coeff (j : ℕ) =
      (((-1 : ℚ) ^ (p - (j : ℕ)) *
          (1 / 4 : ℚ) ^ (p - (j : ℕ) + 1).choose 2) /
        qPochhammer (1 / 4 : ℚ) (1 / 4 : ℚ) p) *
          qBinomial p (j : ℕ) (1 / 4 : ℚ) := by
  exact forwardGeometricRichardsonPolynomial_coeff_eq_qBinomial
    (1 / 4 : ℚ) (by norm_num) p j (quarter_qPochhammer_self_ne_zero p)

end RationalGaussian

end Fabius

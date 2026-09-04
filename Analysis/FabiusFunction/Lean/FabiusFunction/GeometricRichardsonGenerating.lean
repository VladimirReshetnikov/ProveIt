import FabiusFunction.FormalQBinomial
import FabiusFunction.GeometricLagrangeQBinomial
import FabiusFunction.RatioExpansion

/-!
# The generating function of the geometric Richardson triangle

For nonzero `q` in a field, Lean's totalized evaluation-at-zero Lagrange
coefficient on the nodes `1, q, ..., q^n` is

`(-1)^(n-j) q^choose(n-j+1, 2) / ((q;q)_j (q;q)_(n-j))`,

with ordinary field division.  These coefficients are genuine interpolation
weights when the nodes are distinct.  At a root of unity the same algebraic
formula still describes the totalized Lagrange-basis expression, but no
interpolation exactness is asserted.  The excluded base `q = 0` already has
repeated nodes once `n >= 2` and does not satisfy this closed formula.

Consequently, if `r_n` is the corresponding weighted sum of data
`y_0, ..., y_n`, then its ordinary generating series factors as

`sum_n r_n X^n = (qX;q)_infinity * sum_j y_j X^j / (q;q)_j`.

The first half of this module proves a stronger purely formal statement over
an arbitrary commutative ring.  The factors called `(qX;q)_infinity` are the
Euler-coefficient series `qPochhammerSeries`; no topology or convergence is
involved.  The field-valued theorem then identifies the convolution
coefficients with the canonical Lagrange weights already used throughout the
Richardson API.  Finally, over a complete normed field, the same factorization
is recorded as a `HasSum` theorem whenever the normalized data series is
absolutely summable.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius

noncomputable section

private theorem choose_two_succ_eq_add (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  simpa [Nat.add_comm] using Nat.choose_succ_succ n 1

/-! ## Formal convolution over a commutative ring -/

section Formal

variable {A : Type*} [CommRing A]

/-- The `n`th Euler coefficient of `(qX;q)_infinity`:

`(-1)^n q^choose(n+1,2) / (q;q)_n`.

`Ring.inverse` makes the definition meaningful over every commutative ring;
no regularity hypothesis on `q` is required for the convolution identity. -/
noncomputable def geometricRichardsonKernel (q : A) (n : ℕ) : A :=
  (-1 : A) ^ n * q ^ (n + 1).choose 2 *
    Ring.inverse (finiteQPochhammerIn q q n)

/-- The normalized data series `sum_n y_n X^n / (q;q)_n`, with division
interpreted by `Ring.inverse` over a general commutative ring. -/
noncomputable def qPochhammerNormalizedDataSeries
    (q : A) (y : ℕ → A) : A⟦X⟧ :=
  PowerSeries.mk fun n ↦
    Ring.inverse (finiteQPochhammerIn q q n) * y n

/-- The geometric Richardson transform as a lower-triangular convolution of
the Euler kernel with q-Pochhammer-normalized data. -/
noncomputable def geometricRichardsonTransform
    (q : A) (y : ℕ → A) (n : ℕ) : A :=
  ∑ k ∈ Finset.range (n + 1),
    geometricRichardsonKernel q k *
      (Ring.inverse (finiteQPochhammerIn q q (n - k)) * y (n - k))

/-- The Richardson kernel is coefficientwise exactly the rescaled formal
q-Pochhammer series `(qX;q)_infinity`. -/
theorem coeff_rescale_qPochhammerSeries_eq_geometricRichardsonKernel
    (q : A) (n : ℕ) :
    PowerSeries.coeff n
        (PowerSeries.rescale q (qPochhammerSeries q)) =
      geometricRichardsonKernel q n := by
  rw [PowerSeries.coeff_rescale, coeff_qPochhammerSeries,
    geometricRichardsonKernel, choose_two_succ_eq_add, pow_add]
  ring

/-- Coefficients of the q-Pochhammer-normalized data series. -/
@[simp] theorem coeff_qPochhammerNormalizedDataSeries
    (q : A) (y : ℕ → A) (n : ℕ) :
    PowerSeries.coeff n (qPochhammerNormalizedDataSeries q y) =
      Ring.inverse (finiteQPochhammerIn q q n) * y n := by
  rw [qPochhammerNormalizedDataSeries, PowerSeries.coeff_mk]

/-- **Formal Euler factorization of the geometric Richardson triangle.**
For arbitrary data over any commutative ring,

`sum_n R_n(q,y) X^n = (qX;q)_infinity * sum_j y_j X^j/(q;q)_j`.

This version is unconditional: it is an identity of formal power series and
uses `Ring.inverse` at possibly nonunit denominators. -/
theorem geometricRichardsonTransform_generating
    (q : A) (y : ℕ → A) :
    PowerSeries.mk (geometricRichardsonTransform q y) =
      PowerSeries.rescale q (qPochhammerSeries q) *
        qPochhammerNormalizedDataSeries q y := by
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_rescale_qPochhammerSeries_eq_geometricRichardsonKernel,
    coeff_qPochhammerNormalizedDataSeries]
  rfl

end Formal

/-! ## Identification with geometric Lagrange extrapolation -/

section Lagrange

variable {K : Type*} [Field K]

/-- Over a field with nonzero base, the formal convolution coefficient is
the canonical evaluation-at-zero Lagrange sum on `1, q, ..., q^n`.

No root-of-unity hypothesis is needed for this algebraic identity.  At
colliding nodes, both sides retain Lean's totalized inverse convention;
interpolation exactness itself still requires distinct nodes. -/
theorem geometricRichardsonTransform_eq_sum_lagrange
    (q : K) (hq : q ≠ 0) (y : ℕ → K) (n : ℕ) :
    geometricRichardsonTransform q y n =
      ∑ j ∈ Finset.range (n + 1),
        geometricLagrangeWeight q n j * y j := by
  rw [geometricRichardsonTransform]
  calc
    (∑ k ∈ Finset.range (n + 1),
        geometricRichardsonKernel q k *
          (Ring.inverse (finiteQPochhammerIn q q (n - k)) * y (n - k))) =
        ∑ k ∈ Finset.range (n + 1),
          geometricLagrangeWeight q n (n - k) * y (n - k) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hback : n - (n - k) = k := by omega
      rw [geometricLagrangeWeight_eq_geometricQPochhammer
          q hq n (n - k) (Nat.sub_le n k),
        hback]
      simp only [geometricRichardsonKernel,
        geometricQPochhammer_eq_finiteQPochhammerIn,
        Ring.inverse_eq_inv, div_eq_mul_inv, mul_inv]
      ring
    _ = ∑ j ∈ Finset.range (n + 1),
          geometricLagrangeWeight q n j * y j := by
      simpa only [Nat.add_sub_cancel] using
        (Finset.sum_range_reflect
          (fun j ↦ geometricLagrangeWeight q n j * y j) (n + 1))

/-- **The manuscript's formal generating-function identity**, stated with
the repository's canonical geometric Lagrange weights:

`sum_n (sum_{j=0}^n lambda_{j,n} y_j) X^n
  = (qX;q)_infinity * sum_j y_j X^j/(q;q)_j`.

It holds over every field for every nonzero `q`, as a formal power-series
identity; analytic convergence is neither assumed nor needed. -/
theorem geometricLagrangeRichardson_generating
    (q : K) (hq : q ≠ 0) (y : ℕ → K) :
    PowerSeries.mk (fun n ↦
        ∑ j ∈ Finset.range (n + 1),
          geometricLagrangeWeight q n j * y j) =
      PowerSeries.rescale q (qPochhammerSeries q) *
        qPochhammerNormalizedDataSeries q y := by
  rw [← geometricRichardsonTransform_generating q y]
  ext n
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    geometricRichardsonTransform_eq_sum_lagrange q hq y n]

end Lagrange

/-! ## Analytic realization -/

section Analytic

variable {K : Type*} [NormedField K] [CompleteSpace K]

omit [CompleteSpace K] in
/-- A term of Euler's analytic product series at `qz` is the formal
Richardson kernel times `z^n`. -/
private theorem eulerProductTerm_q_mul_eq_geometricRichardsonKernel_mul_pow
    (q z : K) (n : ℕ) :
    (-1 : K) ^ n * q ^ n.choose 2 /
          finiteQPochhammerIn q q n * (q * z) ^ n =
      geometricRichardsonKernel q n * z ^ n := by
  rw [geometricRichardsonKernel, Ring.inverse_eq_inv,
    choose_two_succ_eq_add, pow_add, mul_pow, div_eq_mul_inv]
  ring

/-- **Analytic Euler factorization for the algebraic Richardson transform.**
If the normalized data series is absolutely summable at `z`, then the
Richardson-output series converges and sums to the product of
`(qz;q)_infinity` with the normalized data sum. -/
theorem hasSum_geometricRichardsonTransform_mul_pow
    {q z : K} (hq : ‖q‖ < 1) (y : ℕ → K)
    (hdata : Summable fun j : ℕ ↦
      ‖Ring.inverse (finiteQPochhammerIn q q j) * y j * z ^ j‖) :
    HasSum (fun n : ℕ ↦ geometricRichardsonTransform q y n * z ^ n)
      (qPochhammerInfIn (q * z) q *
        ∑' j : ℕ,
          Ring.inverse (finiteQPochhammerIn q q j) * y j * z ^ j) := by
  let e : ℕ → K := fun k ↦
    (-1 : K) ^ k * q ^ k.choose 2 /
      finiteQPochhammerIn q q k * (q * z) ^ k
  let d : ℕ → K := fun j ↦
    Ring.inverse (finiteQPochhammerIn q q j) * y j * z ^ j
  have heNorm : Summable fun k : ℕ ↦ ‖e k‖ := by
    simpa only [e] using summable_norm_euler_product_term hq (q * z)
  have hdNorm : Summable fun j : ℕ ↦ ‖d j‖ := by
    simpa only [d] using hdata
  have he : HasSum e (qPochhammerInfIn (q * z) q) := by
    simpa only [e] using hasSum_euler_product hq (q * z)
  have hconv := hasSum_sum_range_mul_of_summable_norm heNorm hdNorm
  rw [he.tsum_eq] at hconv
  change HasSum
    (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), e k * d (n - k))
    (qPochhammerInfIn (q * z) q * ∑' j : ℕ, d j) at hconv
  refine hconv.congr_fun fun n ↦ ?_
  rw [geometricRichardsonTransform, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  symm
  dsimp only [e, d]
  rw [eulerProductTerm_q_mul_eq_geometricRichardsonKernel_mul_pow]
  calc
    (geometricRichardsonKernel q k * z ^ k) *
          (Ring.inverse (finiteQPochhammerIn q q (n - k)) *
            y (n - k) * z ^ (n - k)) =
        (geometricRichardsonKernel q k *
          (Ring.inverse (finiteQPochhammerIn q q (n - k)) * y (n - k))) *
            (z ^ k * z ^ (n - k)) := by ring
    _ = (geometricRichardsonKernel q k *
          (Ring.inverse (finiteQPochhammerIn q q (n - k)) * y (n - k))) *
            z ^ n := by rw [← pow_add, Nat.add_sub_of_le hkn]

/-- The analytic factorization in the report-facing Lagrange-weight form.
The only extra hypothesis beyond `‖q‖ < 1` and absolute convergence of the
normalized data is `q ≠ 0`, needed to identify the convolution row with the
geometric Lagrange basis. -/
theorem hasSum_geometricLagrangeRichardson_mul_pow
    {q z : K} (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (y : ℕ → K)
    (hdata : Summable fun j : ℕ ↦
      ‖Ring.inverse (finiteQPochhammerIn q q j) * y j * z ^ j‖) :
    HasSum
      (fun n : ℕ ↦
        (∑ j ∈ Finset.range (n + 1),
          geometricLagrangeWeight q n j * y j) * z ^ n)
      (qPochhammerInfIn (q * z) q *
        ∑' j : ℕ,
          Ring.inverse (finiteQPochhammerIn q q j) * y j * z ^ j) := by
  refine (hasSum_geometricRichardsonTransform_mul_pow hq y hdata).congr_fun fun n ↦ ?_
  rw [geometricRichardsonTransform_eq_sum_lagrange q hq0 y n]

end Analytic

end

end Fabius

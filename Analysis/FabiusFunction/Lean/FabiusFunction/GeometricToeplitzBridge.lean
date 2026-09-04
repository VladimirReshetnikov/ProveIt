import FabiusFunction.GeneralQConditionNumber
import FabiusFunction.GeometricLagrangeQBinomial

/-!
# The geometric Lagrange row IS the general-`q` Toeplitz row

Two developments in this corpus compute the same row of coefficients from
different starting points:

* `GeometricLagrange` builds the Lagrange evaluation weights
  `λ_{p,k}(q)` of the nodes `1, q, …, q^p` at the point `0`, and
  `GeometricLagrangeQBinomial` evaluates them as
  `λ_{p,k} = (-1)^{p-k} q^{C(p-k+1,2)} / ((q;q)_k (q;q)_{p-k})`;
* `GeneralQConditionNumber` defines the Fabius Toeplitz weight
  `w_{n,j}(q) = (-1)^j [n choose j]_q q^{C(j+1,2)} / (q;q)_n`
  and develops its mass, sign, modulus and total variation over an
  arbitrary field.

They are the same numbers read in opposite order:

`λ_{p,k}(q) = w_{p, p-k}(q)`,

because `[p choose p-k]_q (q;q)_k (q;q)_{p-k} = (q;q)_p`.  This module
records the identification, so that the general-field, hypothesis-light
Toeplitz theorems apply verbatim to the geometric Lagrange weights.

* `geometricLagrangeWeight_eq_qToeplitzWeight` — the bridge.
* `qToeplitzWeight_eq_geometricLagrangeWeight` — the reflected form.
* `sum_geometricLagrangeWeight_eq_one` — mass one, transported.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **The geometric Lagrange weight is the reflected Toeplitz weight.**
For `k ≤ p` and `(q;q)_p ≠ 0`,

`λ_{p,k}(q) = w_{p, p-k}(q)`.

The two explicit formulas differ exactly by the q-factorial identity
`(q;q)_p = (q;q)_{p-k} (q;q)_k [p choose p-k]_q`. -/
theorem geometricLagrangeWeight_eq_qToeplitzWeight (q : ℚ) (hq : q ≠ 0)
    {p k : ℕ} (hk : k ≤ p) (hP : qPochhammer q q p ≠ 0) :
    geometricLagrangeWeight q p k = qToeplitzWeight q p (p - k) := by
  have hPf : finiteQPochhammerIn q q p ≠ 0 := by
    rwa [finiteQPochhammerIn_rat_eq]
  have hsub : p - (p - k) = k := by omega
  have hfac :=
    finiteQPochhammerIn_self_eq_mul_mul_gaussianBinomial q (Nat.sub_le p k)
  rw [hsub] at hfac
  have hne : finiteQPochhammerIn q q (p - k) * finiteQPochhammerIn q q k *
      gaussianBinomial q p (p - k) ≠ 0 := by
    rw [← hfac]
    exact hPf
  have hg : gaussianBinomial q p (p - k) ≠ 0 := right_ne_zero_of_mul hne
  have hbc : finiteQPochhammerIn q q (p - k) *
      finiteQPochhammerIn q q k ≠ 0 := left_ne_zero_of_mul hne
  have hpk : finiteQPochhammerIn q q (p - k) ≠ 0 := left_ne_zero_of_mul hbc
  have hkk : finiteQPochhammerIn q q k ≠ 0 := right_ne_zero_of_mul hbc
  rw [geometricLagrangeWeight_eq_qPochhammer q hq p k hk, qToeplitzWeight,
    hfac]
  simp only [← finiteQPochhammerIn_rat_eq]
  field_simp

/-- The reflected form of the bridge: the Toeplitz weight at index `j` is
the geometric Lagrange weight at the complementary index. -/
theorem qToeplitzWeight_eq_geometricLagrangeWeight (q : ℚ) (hq : q ≠ 0)
    {p j : ℕ} (hj : j ≤ p) (hP : qPochhammer q q p ≠ 0) :
    qToeplitzWeight q p j = geometricLagrangeWeight q p (p - j) := by
  have hsub : p - (p - j) = j := by omega
  rw [geometricLagrangeWeight_eq_qToeplitzWeight q hq (Nat.sub_le p j) hP,
    hsub]

/-- **Row mass one from nonvanishing alone.**  `sum_qToeplitzWeight`
assumes `0 ≤ q < 1`, but the generating identity
`sum_qToeplitzWeight_mul_pow` has no hypothesis at all, and at `z = 1` it
already gives `(q;q)_n / (q;q)_n`.  So the exact hypothesis is
`(q;q)_n ≠ 0` — which by `sum_qToeplitzWeight_one_ne_one` cannot be
dropped. -/
theorem sum_qToeplitzWeight_of_ne_zero {K : Type*} [Field K] {q : K}
    (n : ℕ) (hq : finiteQPochhammerIn q q n ≠ 0) :
    (∑ j ∈ Finset.range (n + 1), qToeplitzWeight q n j) = 1 := by
  have h := sum_qToeplitzWeight_mul_pow q 1 n
  simp only [one_pow, mul_one] at h
  rw [h]
  exact div_self hq

/-- **Mass one for the geometric Lagrange weights, transported from the
Toeplitz side** under the single hypothesis `(q;q)_p ≠ 0`. -/
theorem sum_geometricLagrangeWeight_eq_one (q : ℚ) (hq : q ≠ 0) (p : ℕ)
    (hP : qPochhammer q q p ≠ 0) :
    (∑ k ∈ Finset.range (p + 1), geometricLagrangeWeight q p k) = 1 := by
  have hPf : finiteQPochhammerIn q q p ≠ 0 := by
    rwa [finiteQPochhammerIn_rat_eq]
  have hcongr : ∀ k ∈ Finset.range (p + 1),
      geometricLagrangeWeight q p k = qToeplitzWeight q p (p - k) := by
    intro k hkmem
    exact geometricLagrangeWeight_eq_qToeplitzWeight q hq
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hkmem)) hP
  rw [Finset.sum_congr rfl hcongr]
  have hreflect :
      (∑ k ∈ Finset.range (p + 1), qToeplitzWeight q p (p + 1 - 1 - k)) =
        ∑ k ∈ Finset.range (p + 1), qToeplitzWeight q p k :=
    Finset.sum_range_reflect (fun k : ℕ => qToeplitzWeight q p k) (p + 1)
  simp only [Nat.add_sub_cancel] at hreflect
  rw [hreflect]
  exact sum_qToeplitzWeight_of_ne_zero p hPf

end Fabius

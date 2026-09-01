import FabiusFunction.QPascalSummation
import FabiusFunction.QPochhammerElementaryIdentities
import FabiusFunction.QBinomialTheoremInfinite
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Rogers–Szegő polynomials

The Rogers–Szegő polynomial `H_n(z;q) = ∑_k [n,k]_q z^k` is the generating
polynomial of a row of Gaussian coefficients.  Its two-term recurrence
`H_{n+1}(z) = z H_n(z) + H_n(qz)` is the second `q`-Pascal summation; its
dilation law `H_n(qz) = H_n(z) - z(1 - q^n) H_{n-1}(z)` is the column-adjacent
cross identity `(1 - q^{k}) [n,k]_q = (1 - q^n) [n-1,k-1]_q` read
coefficientwise; and the classical three-term recurrence is the sum of the
two.  All of this is finite algebra over a commutative (semi)ring.

The generating function

`∑_n H_n(z;q) t^n / (q;q)_n = 1 / ((t;q)_∞ (zt;q)_∞)`

is the Cauchy product of two copies of Euler's reciprocal expansion, valid in
every complete normed field for `‖q‖ < 1`, `‖t‖ < 1`, `‖zt‖ < 1`.

## Main declarations

* `rogersSzego`: the polynomial `H_n(z;q)`.
* `rogersSzego_succ`: `H_{n+1}(z) = z H_n(z) + H_n(qz)`.
* `rogersSzego_dilation`: `H_{n+1}(qz) = H_{n+1}(z) - z(1 - q^{n+1}) H_n(z)`.
* `rogersSzego_three_term`: the three-term recurrence.
* `hasSum_rogersSzego_generating`: the generating function.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- The Rogers–Szegő polynomial `H_n(z;q) = ∑_{k=0}^{n} [n,k]_q z^k`. -/
def rogersSzego {R : Type*} [CommSemiring R] (q : R) (n : ℕ) (z : R) : R :=
  ∑ k ∈ range (n + 1), gaussianBinomial q n k * z ^ k

/-- `H_0 = 1`. -/
@[simp] theorem rogersSzego_zero {R : Type*} [CommSemiring R] (q z : R) :
    rogersSzego q 0 z = 1 := by
  simp [rogersSzego]

/-- `H_n(1;q)` is the row sum of Gaussian coefficients (the Galois number). -/
theorem rogersSzego_one {R : Type*} [CommSemiring R] (q : R) (n : ℕ) :
    rogersSzego q n 1 = ∑ k ∈ range (n + 1), gaussianBinomial q n k := by
  simp [rogersSzego]

/-- **The basic recurrence** `H_{n+1}(z) = z H_n(z) + H_n(qz)`. -/
theorem rogersSzego_succ {R : Type*} [CommSemiring R] (q : R) (n : ℕ) (z : R) :
    rogersSzego q (n + 1) z = z * rogersSzego q n z + rogersSzego q n (q * z) := by
  have h1 : ∑ k ∈ range (n + 1), q ^ k * gaussianBinomial q n k * z ^ k =
      rogersSzego q n (q * z) := by
    unfold rogersSzego
    refine sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    ring
  have h2 : ∑ k ∈ range (n + 1), gaussianBinomial q n k * z ^ (k + 1) =
      z * rogersSzego q n z := by
    unfold rogersSzego
    rw [Finset.mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  show ∑ k ∈ range (n + 1 + 1), gaussianBinomial q (n + 1) k * z ^ k = _
  rw [sum_gaussianBinomial_succ_mul' q n, h1, h2]
  exact add_comm _ _

/-- The column-adjacent cross identity
`(1 - q^{k+1}) [n+1,k+1]_q = (1 - q^{n+1}) [n,k]_q`, the `q`-analogue of
`k C(n,k) = n C(n-1,k-1)`, total in `n` and `k`. -/
theorem one_sub_pow_succ_mul_gaussianBinomial_succ_succ {R : Type*} [CommRing R] (q : R)
    (n k : ℕ) :
    (1 - q ^ (k + 1)) * gaussianBinomial q (n + 1) (k + 1) =
      (1 - q ^ (n + 1)) * gaussianBinomial q n k := by
  rw [gaussianBinomial_adjacent_mul, gaussianBinomial_row_adjacent_mul, Nat.add_sub_cancel]

/-- **The dilation formula** `H_{n+1}(qz) = H_{n+1}(z) - z (1 - q^{n+1}) H_n(z)`. -/
theorem rogersSzego_dilation {R : Type*} [CommRing R] (q : R) (n : ℕ) (z : R) :
    rogersSzego q (n + 1) (q * z) =
      rogersSzego q (n + 1) z - z * (1 - q ^ (n + 1)) * rogersSzego q n z := by
  have h : rogersSzego q (n + 1) z - rogersSzego q (n + 1) (q * z) =
      z * (1 - q ^ (n + 1)) * rogersSzego q n z := by
    unfold rogersSzego
    rw [← Finset.sum_sub_distrib, Finset.sum_range_succ' _ (n + 1), Finset.mul_sum]
    simp only [pow_zero, mul_one, sub_self, add_zero]
    refine sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    calc gaussianBinomial q (n + 1) (k + 1) * z ^ (k + 1) -
          gaussianBinomial q (n + 1) (k + 1) * (q ^ (k + 1) * z ^ (k + 1))
        = (1 - q ^ (k + 1)) * gaussianBinomial q (n + 1) (k + 1) * z ^ (k + 1) := by ring
      _ = (1 - q ^ (n + 1)) * gaussianBinomial q n k * z ^ (k + 1) := by
        rw [one_sub_pow_succ_mul_gaussianBinomial_succ_succ]
      _ = z * (1 - q ^ (n + 1)) * (gaussianBinomial q n k * z ^ k) := by ring
  linear_combination -h

/-- **The three-term recurrence**
`H_{n+2}(z) = (1 + z) H_{n+1}(z) - z (1 - q^{n+1}) H_n(z)`. -/
theorem rogersSzego_three_term {R : Type*} [CommRing R] (q : R) (n : ℕ) (z : R) :
    rogersSzego q (n + 2) z =
      (1 + z) * rogersSzego q (n + 1) z - z * (1 - q ^ (n + 1)) * rogersSzego q n z := by
  have h1 := rogersSzego_succ q (n + 1) z
  have h2 := rogersSzego_dilation q n z
  linear_combination h1 + h2

/-! ## The generating function -/

section GeneratingElementary

variable {𝕜 : Type*} [NormedField 𝕜]

/-- Euler's reciprocal expansion is absolutely convergent. -/
theorem summable_norm_pow_div_finiteQPochhammerIn_self {q : 𝕜} (hq : ‖q‖ < 1) {z : 𝕜}
    (hz : ‖z‖ < 1) :
    Summable fun k : ℕ => ‖z ^ k / finiteQPochhammerIn q q k‖ := by
  have hμ : 0 < qPochhammerInfIn ‖q‖ ‖q‖ :=
    qPochhammerInfIn_pos_of_lt_one (norm_nonneg q) hq (norm_nonneg q) hq
  have hgeom : Summable fun k : ℕ => ‖z‖ ^ k * (qPochhammerInfIn ‖q‖ ‖q‖)⁻¹ :=
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right _
  refine hgeom.of_nonneg_of_le (fun k => norm_nonneg _) fun k => ?_
  rw [norm_div, norm_pow, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg z) k)
  exact inv_anti₀ hμ (qPochhammerInfIn_norm_le_norm_finiteQPochhammerIn q hq.le hq k)

/-- The Cauchy-product coefficient of two Euler expansions is a Rogers–Szegő
polynomial: `∑_{j+k=n} t^j/(q;q)_j · (zt)^k/(q;q)_k = H_n(z;q) t^n / (q;q)_n`. -/
theorem sum_antidiagonal_euler_mul_euler {q : 𝕜} (hq : ‖q‖ < 1) (z t : 𝕜) (n : ℕ) :
    ∑ jk ∈ antidiagonal n,
        t ^ jk.1 / finiteQPochhammerIn q q jk.1 * ((z * t) ^ jk.2 / finiteQPochhammerIn q q jk.2) =
      rogersSzego q n z / finiteQPochhammerIn q q n * t ^ n := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun j k => t ^ j / finiteQPochhammerIn q q j * ((z * t) ^ k / finiteQPochhammerIn q q k)) n,
    ← Finset.sum_range_reflect]
  unfold rogersSzego
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hidx : n + 1 - 1 - j = n - j := by omega
  rw [hidx, Nat.sub_sub_self hjn, gaussianBinomial_eq_div hq hjn]
  have h1 : finiteQPochhammerIn q q j ≠ 0 := finiteQPochhammerIn_self_ne_zero hq j
  have h2 : finiteQPochhammerIn q q (n - j) ≠ 0 := finiteQPochhammerIn_self_ne_zero hq (n - j)
  have h3 : finiteQPochhammerIn q q n ≠ 0 := finiteQPochhammerIn_self_ne_zero hq n
  have hpow : t ^ n = t ^ (n - j) * t ^ j := by rw [← pow_add, Nat.sub_add_cancel hjn]
  rw [hpow, mul_pow]
  field_simp

end GeneratingElementary

section Generating

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The generating function of the Rogers–Szegő polynomials:**
`∑_n H_n(z;q) t^n / (q;q)_n = 1 / ((t;q)_∞ (zt;q)_∞)` for `‖q‖ < 1`, `‖t‖ < 1`,
`‖zt‖ < 1`. -/
theorem hasSum_rogersSzego_generating {q : 𝕜} (hq : ‖q‖ < 1) {z t : 𝕜} (ht : ‖t‖ < 1)
    (hzt : ‖z * t‖ < 1) :
    HasSum (fun n : ℕ => rogersSzego q n z / finiteQPochhammerIn q q n * t ^ n)
      ((qPochhammerInfIn t q)⁻¹ * (qPochhammerInfIn (z * t) q)⁻¹) := by
  have hf := hasSum_euler_reciprocal hq ht
  have hg := hasSum_euler_reciprocal hq hzt
  have hfn := summable_norm_pow_div_finiteQPochhammerIn_self hq ht
  have hgn := summable_norm_pow_div_finiteQPochhammerIn_self hq hzt
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hgn
  rw [hf.tsum_eq, hg.tsum_eq] at hprod
  have hsum : Summable fun n : ℕ => ∑ jk ∈ antidiagonal n,
      t ^ jk.1 / finiteQPochhammerIn q q jk.1 *
        ((z * t) ^ jk.2 / finiteQPochhammerIn q q jk.2) :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hgn).of_norm
  have h := hsum.hasSum
  rw [← hprod] at h
  refine h.congr_fun fun n => ?_
  exact (sum_antidiagonal_euler_mul_euler hq z t n).symm

end Generating

end Fabius

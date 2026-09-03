import FabiusFunction.QBinomialVandermonde
import FabiusFunction.QBinomialTheoremInfinite
import FabiusFunction.JacobiTripleProduct
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The Durfee decomposition of all partitions

`1/(q;q)_∞ = ∑_{r ≥ 0} q^{r²}/(q;q)_r²` for `‖q‖ < 1`.

The finite version is the `q`-Vandermonde convolution read at `k = n`:
`[m+n, n]_q = ∑_{j ≤ n} q^{j²} [m,j]_q [n,j]_q` (a partition in an `n × m` box with Durfee
square of side `j` is the square, a partition in a `j × (m-j)` box and one in an `(n-j) × j`
box).  Letting `m = n = N → ∞`, the central coefficients `[2N, N]_q` tend to `1/(q;q)_∞`
(`tendsto_gaussianBinomialInt_central`), each term tends to `q^{j²}/(q;q)_j²`
(`tendsto_gaussianBinomial_atTop`), and Tannery's theorem with the dominating series
`‖q‖^{j²} · gaussianMajorant q ^ 2` exchanges the limits.

## Main declarations

* `gaussianBinomial_add_eq_sum_sq`: the finite Durfee identity.
* `hasSum_durfee`: `∑_r q^{r²}/(q;q)_r² = 1/(q;q)_∞`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- **The finite Durfee identity**: `[m+n, n]_q = ∑_{j ≤ n} q^{j²} [m,j]_q [n,j]_q`. -/
theorem gaussianBinomial_add_eq_sum_sq {R : Type*} [CommSemiring R] (q : R) (m n : ℕ) :
    gaussianBinomial q (m + n) n =
      ∑ j ∈ range (n + 1), q ^ (j * j) * gaussianBinomial q m j * gaussianBinomial q n j := by
  rw [gaussianBinomial_add_vandermonde' q m n n]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [show n - (n - j) = j by omega, gaussianBinomial_symm q hj']

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Durfee decomposition of all partitions**: `∑_{r ≥ 0} q^{r²}/(q;q)_r² = 1/(q;q)_∞`
for `‖q‖ < 1`. -/
theorem hasSum_durfee {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun r : ℕ => q ^ (r * r) / finiteQPochhammerIn q q r ^ 2)
      (qPochhammerInfIn q q)⁻¹ := by
  set M := gaussianMajorant q with hM
  have hM0 : 0 ≤ M := gaussianMajorant_nonneg hq
  let f : ℕ → ℕ → 𝕜 := fun N j =>
    if j ≤ N then q ^ (j * j) * gaussianBinomial q N j * gaussianBinomial q N j else 0
  -- the finite Durfee sums
  have hfin : ∀ N, ∑' j, f N j = gaussianBinomial q (2 * N) N := by
    intro N
    rw [tsum_eq_sum (s := range (N + 1)) (fun j hj => by
      simp only [f]
      rw [mem_range] at hj
      rw [if_neg (by omega)])]
    rw [show 2 * N = N + N by ring, gaussianBinomial_add_eq_sum_sq]
    refine sum_congr rfl fun j hj => ?_
    simp only [f]
    rw [if_pos (Nat.lt_succ_iff.mp (mem_range.mp hj))]
  -- the dominating series
  have hbound : Summable fun j : ℕ => ‖q‖ ^ (j * j) * (M * M) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right (M * M))
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_mul_self j)) (by positivity)
  have hb : ∀ N j, ‖f N j‖ ≤ ‖q‖ ^ (j * j) * (M * M) := by
    intro N j
    simp only [f]
    split_ifs with hj
    · rw [norm_mul, norm_mul, norm_pow, mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul (norm_gaussianBinomial_le hq N j) (norm_gaussianBinomial_le hq N j)
        (norm_nonneg _) hM0
    · rw [norm_zero]
      positivity
  -- pointwise limits
  have hpt : ∀ j, Tendsto (fun N => f N j) atTop
      (𝓝 (q ^ (j * j) / finiteQPochhammerIn q q j ^ 2)) := by
    intro j
    have h1 := tendsto_gaussianBinomial_atTop hq j
    have h2 := (h1.mul h1).const_mul (q ^ (j * j))
    rw [show q ^ (j * j) * ((finiteQPochhammerIn q q j)⁻¹ * (finiteQPochhammerIn q q j)⁻¹) =
        q ^ (j * j) / finiteQPochhammerIn q q j ^ 2 by ring] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop j] with N hN
    simp only [f]
    rw [if_pos hN, mul_assoc]
  have hlim1 : Tendsto (fun N => ∑' j, f N j) atTop (𝓝 (qPochhammerInfIn q q)⁻¹) := by
    simp_rw [hfin]
    have := tendsto_gaussianBinomialInt_central hq 0
    simpa [gaussianBinomialInt_ofNat] using this
  have hlim2 : Tendsto (fun N => ∑' j, f N j) atTop
      (𝓝 (∑' j, q ^ (j * j) / finiteQPochhammerIn q q j ^ 2)) :=
    tendsto_tsum_of_dominated_convergence hbound hpt (Eventually.of_forall hb)
  have hsum : Summable fun j : ℕ => q ^ (j * j) / finiteQPochhammerIn q q j ^ 2 :=
    Summable.of_norm_bounded hbound fun j =>
      le_of_tendsto' (hpt j).norm fun N => hb N j
  have heq := tendsto_nhds_unique hlim2 hlim1
  rw [← heq]
  exact hsum.hasSum

end Fabius

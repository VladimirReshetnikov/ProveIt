import FabiusFunction.JacobiTripleProduct

/-!
# The infinite central `q`-Vandermonde identity

For `‖q‖ < 1` and every shift `k ∈ ℕ`,

`∑_{ℓ ≥ 0} q^{ℓ(ℓ+k)} / ((q;q)_ℓ (q;q)_{ℓ+k}) = 1 / (q;q)_∞`.

This is the `N → ∞` limit of the finite shifted-central `q`-Vandermonde
convolution (`gaussianBinomial_two_mul_add_shifted_central`)

`[2N, N+k]_q = ∑_{ℓ ≤ N} q^{ℓ(ℓ+k)} [N,ℓ]_q [N,ℓ+k]_q`,

taken with Tannery's theorem (`hasSum_of_tendsto_of_dominated`): the
left side tends to `1/(q;q)_∞` (`tendsto_gaussianBinomialInt_central`),
each summand tends to `q^{ℓ(ℓ+k)}/((q;q)_ℓ (q;q)_{ℓ+k})`
(`tendsto_gaussianBinomial_atTop`), and the summands are dominated by
`‖q‖^ℓ · M²` with `M = gaussianMajorant q` (`norm_gaussianBinomial_le`),
since `ℓ ≤ ℓ(ℓ+k)`.  The case `k = 0` is the Durfee-square identity
`DurfeeAll.hasSum_durfee`.

## Main declarations

* `tendsto_gaussianBinomial_two_mul_add_central`:
  `[2N, N+k]_q → 1/(q;q)_∞` in natural indices.
* `hasSum_central_qVandermonde`, `summable_central_qVandermonde`,
  `tsum_central_qVandermonde`.
-/

set_option autoImplicit false

open Filter Topology
open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **The central limit in natural indices**: `[2N, N+k]_q → 1/(q;q)_∞`
as `N → ∞`, for every `k : ℕ`.  This is
`tendsto_gaussianBinomialInt_central` read through
`gaussianBinomialInt_ofNat`. -/
theorem tendsto_gaussianBinomial_two_mul_add_central {q : 𝕜}
    (hq : ‖q‖ < 1) (k : ℕ) :
    Tendsto (fun N : ℕ => gaussianBinomial q (2 * N) (N + k)) atTop
      (𝓝 (qPochhammerInfIn q q)⁻¹) := by
  refine (tendsto_gaussianBinomialInt_central hq (k : ℤ)).congr
    fun N => ?_
  show gaussianBinomialInt q (2 * N) ((N : ℤ) + (k : ℤ)) =
    gaussianBinomial q (2 * N) (N + k)
  rw [← Nat.cast_add, gaussianBinomialInt_ofNat]

/-- **The infinite central `q`-Vandermonde identity.**  For `‖q‖ < 1`
and every shift `k`,

`∑_{ℓ ≥ 0} q^{ℓ(ℓ+k)} / ((q;q)_ℓ (q;q)_{ℓ+k}) = 1/(q;q)_∞`. -/
theorem hasSum_central_qVandermonde {q : 𝕜} (hq : ‖q‖ < 1) (k : ℕ) :
    HasSum (fun ℓ : ℕ => q ^ (ℓ * (ℓ + k)) /
        (finiteQPochhammerIn q q ℓ * finiteQPochhammerIn q q (ℓ + k)))
      (qPochhammerInfIn q q)⁻¹ := by
  set M : ℝ := gaussianMajorant q
  have hgm : 0 ≤ M := gaussianMajorant_nonneg hq
  have hmain : HasSum
      (fun ℓ : ℕ => q ^ (ℓ * (ℓ + k)) * (finiteQPochhammerIn q q ℓ)⁻¹ *
        (finiteQPochhammerIn q q (ℓ + k))⁻¹)
      (qPochhammerInfIn q q)⁻¹ := by
    refine hasSum_of_tendsto_of_dominated
      (f := fun N ℓ => q ^ (ℓ * (ℓ + k)) * gaussianBinomial q N ℓ *
        gaussianBinomial q N (ℓ + k))
      (bound := fun ℓ => ‖q‖ ^ ℓ * M * M)
      (S := fun N => gaussianBinomial q (2 * N) (N + k)) ?_ ?_ ?_ ?_ ?_
    · exact ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_right
        M).mul_right M
    · intro ℓ
      exact ((tendsto_gaussianBinomial_atTop hq ℓ).const_mul
        (q ^ (ℓ * (ℓ + k)))).mul
          (tendsto_gaussianBinomial_atTop hq (ℓ + k))
    · intro N ℓ
      have h1 : ‖gaussianBinomial q N ℓ‖ ≤ M :=
        norm_gaussianBinomial_le hq N ℓ
      have h2 : ‖gaussianBinomial q N (ℓ + k)‖ ≤ M :=
        norm_gaussianBinomial_le hq N (ℓ + k)
      have hpow : ‖q‖ ^ (ℓ * (ℓ + k)) ≤ ‖q‖ ^ ℓ :=
        pow_le_pow_of_le_one (norm_nonneg q) hq.le
          ((Nat.le_mul_self ℓ).trans
            (Nat.mul_le_mul_left ℓ (Nat.le_add_right ℓ k)))
      rw [norm_mul, norm_mul, norm_pow]
      calc ‖q‖ ^ (ℓ * (ℓ + k)) * ‖gaussianBinomial q N ℓ‖ *
            ‖gaussianBinomial q N (ℓ + k)‖
          ≤ ‖q‖ ^ (ℓ * (ℓ + k)) * M * M :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2
              (norm_nonneg _) (by positivity)
        _ ≤ ‖q‖ ^ ℓ * M * M :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hpow hgm) hgm
    · intro N
      rw [gaussianBinomial_two_mul_add_shifted_central q N k]
      refine hasSum_sum_of_ne_finset_zero fun ℓ hℓ => ?_
      rw [Finset.mem_range, not_lt] at hℓ
      rw [gaussianBinomial_eq_zero_of_lt q (show N < ℓ by omega),
        mul_zero, zero_mul]
    · exact tendsto_gaussianBinomial_two_mul_add_central hq k
  refine hmain.congr_fun fun ℓ => ?_
  show q ^ (ℓ * (ℓ + k)) /
      (finiteQPochhammerIn q q ℓ * finiteQPochhammerIn q q (ℓ + k)) =
    q ^ (ℓ * (ℓ + k)) * (finiteQPochhammerIn q q ℓ)⁻¹ *
      (finiteQPochhammerIn q q (ℓ + k))⁻¹
  rw [div_eq_mul_inv, mul_inv, mul_assoc]

/-- The summands of the infinite central `q`-Vandermonde identity are
summable. -/
theorem summable_central_qVandermonde {q : 𝕜} (hq : ‖q‖ < 1) (k : ℕ) :
    Summable (fun ℓ : ℕ => q ^ (ℓ * (ℓ + k)) /
      (finiteQPochhammerIn q q ℓ * finiteQPochhammerIn q q (ℓ + k))) :=
  (hasSum_central_qVandermonde hq k).summable

/-- The summed form of the infinite central `q`-Vandermonde identity:
`∑' ℓ, q^{ℓ(ℓ+k)} / ((q;q)_ℓ (q;q)_{ℓ+k}) = 1/(q;q)_∞`. -/
theorem tsum_central_qVandermonde {q : 𝕜} (hq : ‖q‖ < 1) (k : ℕ) :
    ∑' ℓ : ℕ, q ^ (ℓ * (ℓ + k)) /
        (finiteQPochhammerIn q q ℓ * finiteQPochhammerIn q q (ℓ + k)) =
      (qPochhammerInfIn q q)⁻¹ :=
  (hasSum_central_qVandermonde hq k).tsum_eq

end Fabius

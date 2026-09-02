import FabiusFunction.PartitionMultiplicity
import FabiusFunction.GeometricSimplexSum
import FabiusFunction.QBinomialTheoremInfinite
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The generating function of the partition numbers

With `p(n) = #(Nat.Partition n)`, for `‖q‖ < 1` in a complete normed field,

`∑_{n ≥ 0} p(n) q^n = 1 / (q;q)_∞`.

The proof follows Euler: `∏_{k<N} (1 - q^{k+1})^{-1} = ∏_{k<N} ∑_m q^{(k+1)m}` is a product of
absolutely convergent geometric series (`hasSum_prod_fin_pi`); regrouping by the weighted
degree `∑_k (k+1) m_k` (`hasSum_regroup`) writes it as `∑_n c_N(n) q^n`, where `c_N(n)` counts
the multiplicity vectors of weight `n` on the alphabet `{1, …, N}`, i.e. the partitions of `n`
with parts at most `N` (`PartitionMultiplicity`).  As `N → ∞` the coefficients stabilize to
`p(n)`, the finite products tend to `1/(q;q)_∞`, and Tannery's theorem (dominated convergence
for series, with the dominating series `∑ p(n) ‖q‖^n`, summable by the uniform bound
`∑_n c_N(n) ‖q‖^n ≤ 1/(‖q‖;‖q‖)_∞`) lets the two limits be exchanged.

## Main declarations

* `hasSum_regroup`: regrouping a convergent series by an `ℕ`-valued degree with finite fibres.
* `hasSum_card_multiplicityVectors`: `∑_n c_N(n) q^n = ∏_{k<N} (1 - q^{k+1})^{-1}`.
* `partitionCount`, `summable_partitionCount_mul_pow`, `hasSum_partitionCount_mul_pow`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Regrouping by degree**: a convergent series over `ι` may be summed fibrewise over the
finite fibres `T n = {i | d i = n}` of an `ℕ`-valued degree `d`. -/
theorem hasSum_regroup {ι : Type*} {F : ι → 𝕜} {S : 𝕜} (hF : HasSum F S) (d : ι → ℕ)
    (T : ℕ → Finset ι) (hT : ∀ n i, i ∈ T n ↔ d i = n) :
    HasSum (fun n => ∑ i ∈ T n, F i) S := by
  let e := Equiv.sigmaFiberEquiv d
  have h1 : HasSum (F ∘ e) S := e.hasSum_iff.mpr hF
  refine h1.sigma fun N => ?_
  have hs : HasSum ({i | d i = N}.indicator F) (∑ i ∈ T N, F i) := by
    have h3 : HasSum ({i | d i = N}.indicator F) (∑ b ∈ T N, {i | d i = N}.indicator F b) :=
      hasSum_sum_of_ne_finset_zero fun b hb =>
        Set.indicator_of_notMem (s := {i | d i = N}) (a := b) (fun h => hb ((hT N b).mpr h)) F
    rwa [Finset.sum_congr rfl fun b hb =>
      Set.indicator_of_mem (s := {i | d i = N}) (a := b) ((hT N b).mp hb) F] at h3
  have h5 := hasSum_subtype_iff_indicator.mpr hs
  exact h5.congr_fun fun c => rfl

/-- The partitions with parts at most `N`, by size:
`∑_n #{m : Fin N → ℕ | ∑ (k+1) m_k = n} q^n = ∏_{k<N} (1 - q^{k+1})^{-1}` for `‖q‖ < 1`. -/
theorem hasSum_card_multiplicityVectors {q : 𝕜} (hq : ‖q‖ < 1) (N : ℕ) :
    HasSum (fun n : ℕ => ((multiplicityVectors N n).card : 𝕜) * q ^ n)
      (∏ k : Fin N, (1 - q ^ ((k : ℕ) + 1))⁻¹) := by
  have hlt : ∀ k : Fin N, ‖q ^ ((k : ℕ) + 1)‖ < 1 := fun k => by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero _)
  have hg : ∀ k : Fin N, Summable fun n : ℕ => ‖(q ^ ((k : ℕ) + 1)) ^ n‖ := fun k =>
    (summable_geometric_of_lt_one (norm_nonneg _) (hlt k)).congr fun n => (norm_pow _ _).symm
  obtain ⟨h, -⟩ := hasSum_prod_fin_pi N (fun k n => (q ^ ((k : ℕ) + 1)) ^ n) hg
  have hval : ∀ k : Fin N, ∑' n : ℕ, (q ^ ((k : ℕ) + 1)) ^ n = (1 - q ^ ((k : ℕ) + 1))⁻¹ :=
    fun k => tsum_geometric_of_norm_lt_one (hlt k)
  rw [prod_congr rfl fun k _ => hval k] at h
  have h2 := hasSum_regroup h (fun m : Fin N → ℕ => ∑ k : Fin N, ((k : ℕ) + 1) * m k)
    (fun n => multiplicityVectors N n) (fun n m => mem_multiplicityVectors)
  refine h2.congr_fun fun n => ?_
  have hterm : ∀ m ∈ multiplicityVectors N n,
      (∏ k : Fin N, (q ^ ((k : ℕ) + 1)) ^ m k) = q ^ n := by
    intro m hm
    simp_rw [← pow_mul]
    rw [prod_pow_eq_pow_sum, mem_multiplicityVectors.mp hm]
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]

/-- `∏_{k<N} (1 - q^{k+1})^{-1} = 1/(q;q)_N`. -/
theorem prod_one_sub_pow_succ_inv (q : 𝕜) (N : ℕ) :
    ∏ k : Fin N, (1 - q ^ ((k : ℕ) + 1))⁻¹ = (finiteQPochhammerIn q q N)⁻¹ := by
  rw [finiteQPochhammerIn, ← Fin.prod_univ_eq_prod_range (fun j => 1 - q * q ^ j) N,
    prod_inv_distrib]
  congr 1
  exact prod_congr rfl fun k _ => by rw [pow_succ']

/-- The partition numbers `p(n) = #(Nat.Partition n)`. -/
def partitionCount (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The dominating series: `∑ p(n) r^n` converges for `0 ≤ r < 1`, with sum at most
`1/(r;r)_∞`. -/
theorem summable_partitionCount_mul_pow {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => (partitionCount n : ℝ) * r ^ n := by
  have hr : ‖r‖ < 1 := by rwa [Real.norm_of_nonneg hr0]
  refine summable_of_sum_range_le (c := (qPochhammerInfIn r r)⁻¹) (fun n => by positivity)
    fun M => ?_
  have hS := hasSum_card_multiplicityVectors hr M
  rw [prod_one_sub_pow_succ_inv] at hS
  calc ∑ i ∈ range M, (partitionCount i : ℝ) * r ^ i
      = ∑ i ∈ range M, ((multiplicityVectors M i).card : ℝ) * r ^ i := by
        refine sum_congr rfl fun i hi => ?_
        rw [partitionCount, card_partition_eq_card_multiplicityVectors (mem_range.mp hi).le]
    _ ≤ ∑' i, ((multiplicityVectors M i).card : ℝ) * r ^ i :=
        hS.summable.sum_le_tsum (range M) fun i _ => by positivity
    _ = (finiteQPochhammerIn r r M)⁻¹ := hS.tsum_eq
    _ ≤ (qPochhammerInfIn r r)⁻¹ :=
        inv_anti₀ (qPochhammerInfIn_pos_of_lt_one hr0 hr1 hr0 hr1)
          (qPochhammerInfIn_le_finiteQPochhammerIn hr0 hr1.le hr0 hr1 M)

/-- **The partition generating function**: `∑_{n≥0} p(n) q^n = 1/(q;q)_∞` for `‖q‖ < 1`. -/
theorem hasSum_partitionCount_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partitionCount n : 𝕜) * q ^ n) (qPochhammerInfIn q q)⁻¹ := by
  have hbound : Summable fun n : ℕ => (partitionCount n : ℝ) * ‖q‖ ^ n :=
    summable_partitionCount_mul_pow (norm_nonneg q) hq
  have hcast : ∀ n : ℕ, ‖(n : 𝕜)‖ ≤ n := fun n => by
    have := Nat.norm_cast_le (α := 𝕜) n
    rwa [norm_one, mul_one] at this
  have hsum : Summable fun n : ℕ => (partitionCount n : 𝕜) * q ^ n :=
    Summable.of_norm_bounded hbound fun n => by
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (hcast _) (by positivity)
  have hfin : ∀ N, HasSum (fun n : ℕ => ((multiplicityVectors N n).card : 𝕜) * q ^ n)
      (finiteQPochhammerIn q q N)⁻¹ := fun N => by
    have := hasSum_card_multiplicityVectors hq N
    rwa [prod_one_sub_pow_succ_inv] at this
  have hlim1 : Tendsto (fun N : ℕ => ∑' n : ℕ, ((multiplicityVectors N n).card : 𝕜) * q ^ n)
      atTop (𝓝 (qPochhammerInfIn q q)⁻¹) := by
    simp_rw [fun N => (hfin N).tsum_eq]
    exact (tendsto_finiteQPochhammerIn_qPochhammerInfIn q hq).inv₀
      (qPochhammerInfIn_ne_zero_of_norm_lt_one hq hq)
  have hlim2 : Tendsto (fun N : ℕ => ∑' n : ℕ, ((multiplicityVectors N n).card : 𝕜) * q ^ n)
      atTop (𝓝 (∑' n : ℕ, (partitionCount n : 𝕜) * q ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) (Eventually.of_forall
      fun N n => ?_)
    · refine tendsto_atTop_of_eventually_const (i₀ := n) fun N hN => ?_
      rw [partitionCount, card_partition_eq_card_multiplicityVectors hN]
    · rw [norm_mul, norm_pow]
      calc ‖((multiplicityVectors N n).card : 𝕜)‖ * ‖q‖ ^ n
          ≤ ((multiplicityVectors N n).card : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (hcast _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact card_multiplicityVectors_le N n
  have heq := tendsto_nhds_unique hlim2 hlim1
  rw [← heq]
  exact hsum.hasSum

end Fabius

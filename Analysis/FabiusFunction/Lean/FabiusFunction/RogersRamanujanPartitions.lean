import FabiusFunction.RogersRamanujan
import FabiusFunction.PartitionBoundedParts
import FabiusFunction.PartitionDistinctOdd
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The Rogers–Ramanujan identities as identities between partition counts

This module formalises the *product half* of the Rogers–Ramanujan partition corollary
(`qg:cor-rr-partitions` of the `q`-Pochhammer/`q`-binomial monograph, Corollary 18.7) and
replaces the gap condition of the printed statement by an explicitly summed Durfee-staircase
count.  Precisely, writing

`p_{1,4}(N)` for the number of partitions of `N` into parts `≡ 1, 4 (mod 5)` and
`p_{2,3}(N)` for the number of partitions of `N` into parts `≡ 2, 3 (mod 5)`,

the two final theorems are the coefficient identities

`p_{1,4}(N) = ∑_{k : k² ≤ N} p_{≤ k}(N - k²)`,
`p_{2,3}(N) = ∑_{k : k² + k ≤ N} p_{≤ k}(N - k² - k)`,

where `p_{≤ k}(m) = boundedCount k m` is the number of partitions of `m` with every part at
most `k`.  Both sides are genuine partition counts and both are computed here as Taylor
coefficients of the two Rogers–Ramanujan products, the analytic input being the already
sorry-free `Fabius.hasSum_rogersRamanujan_first` and `Fabius.hasSum_rogersRamanujan_second`.

## What is *not* covered relative to the printed statement

The printed Corollary 18.7 states its two clauses with

  "the number of partitions of `N` whose successive parts differ by at least `2`"
  (respectively, and whose smallest part is at least `2`)

on the left-hand side.  Identifying that gap count with the staircase sum
`∑_{k : k² ≤ N} p_{≤ k}(N - k²)` is the staircase bijection of the printed proof: subtract
`(2k-1, 2k-3, …, 3, 1)` from a gap partition with `k` parts and conjugate the remainder.  That
bijection is **not proved here** — Mathlib has no conjugation for `Nat.Partition`, and the
substitute encoding (send a multiplicity vector `m : Fin k → ℕ` to the partition with parts
`2i + 1 + ∑_{j ≥ k-1-i} m j`) is a module of its own.  Consequently this module does **not**
deliver clauses (i) and (ii) of `qg:cor-rr-partitions` as printed; it delivers them with the
gap count replaced by `staircaseCount`.  The register entry for `qg:cor-rr-partitions` must
therefore stay partial.

Two further gaps of the printed proof are closed here rather than assumed: the proof fixes the
number of parts, computes the generating function of that stratum and then sums over the
stratum index without comment — that interchange is `hasSum_staircaseCount` below (a fibrewise
summation over `ℕ × ℕ` followed by a regrouping by total degree); and the sentence "all these
products and series are holomorphic at `q = 0` throughout the open unit disk" is used here in
its intended form, holomorphy on the open unit disk, through `Fabius.eq_of_hasSum_pow_eq`.

## Generality

Everything except the two final coefficient identities is proved for an arbitrary complete
normed field `𝕜` and `‖q‖ < 1`, not just for `ℂ`; only the passage from equality of generating
functions to equality of counts needs `ℂ`.  Moreover the restricted-parts generating function
is proved here for an **arbitrary decidable predicate** `P : ℕ → Prop` on part sizes
(`hasSum_restrictedCount_mul_pow`), along an arbitrary exhausting alphabet sequence; this
subsumes `Fabius.hasSum_oddCount_mul_pow` (odd parts) and `Fabius.hasSum_boundedCount_mul_pow`
(parts at most `r`) as well as the two mod-`5` cases used below.  Likewise the staircase side
is proved for an arbitrary offset `e : ℕ → ℕ` with `k ≤ e k` (`hasSum_staircaseCount`), so that
the two Rogers–Ramanujan offsets `k²` and `k² + k` — and any Andrews–Gordon offset a later
module may need — are instances of one lemma.

## Main declarations

* `restrictedVectors`, `mem_restrictedVectors`, `card_restricted_eq`: partitions with all parts
  satisfying `P` as multiplicity vectors supported on `P`.
* `hasSum_card_restrictedVectors`: the finite-alphabet generating function.
* `hasSum_restrictedCount_mul_pow`: **the reusable payload** — the generating function of
  `Nat.Partition.restricted n P` as the limit of the finite products, along any alphabet
  sequence tending to infinity.
* `prod_mod5_14_inv`, `prod_mod5_23_inv`: the two mod-`5` finite products.
* `partsMod5_14`, `partsMod5_23`, `hasSum_partsMod5_14`, `hasSum_partsMod5_23`: the two
  mod-`5` partition counts and their product generating functions.
* `hasSum_partsMod5_14_rogersRamanujan`, `hasSum_partsMod5_23_rogersRamanujan`: the same two
  counts against the Rogers–Ramanujan series.
* `staircaseCount`, `hasSum_staircaseCount`, `hasSum_staircaseCount_sq`,
  `hasSum_staircaseCount_sq_add`: the Durfee-staircase side.
* `partsMod5_14_eq_staircaseCount`, `partsMod5_23_eq_staircaseCount`: the coefficient
  identities.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-! ### Multiplicity vectors restricted by a predicate on the part sizes -/

/-- The multiplicity vectors of weight `n` on the alphabet `{1, …, N}` that are supported on
the part sizes satisfying `P`: the multiplicity of a part size violating `P` is forced to be
`0`.  This is the pattern of `Fabius.oddVectors` (the case of the odd part sizes) with the
condition on the part sizes left free. -/
def restrictedVectors (P : ℕ → Prop) [DecidablePred P] (N n : ℕ) : Finset (Fin N → ℕ) :=
  (multiplicityVectors N n).filter
    fun m : Fin N → ℕ => ∀ k : Fin N, ¬ P ((k : ℕ) + 1) → m k = 0

theorem mem_restrictedVectors {P : ℕ → Prop} [DecidablePred P] {N n : ℕ} {m : Fin N → ℕ} :
    m ∈ restrictedVectors P N n ↔
      (∑ k : Fin N, ((k : ℕ) + 1) * m k = n) ∧
        ∀ k : Fin N, ¬ P ((k : ℕ) + 1) → m k = 0 := by
  rw [restrictedVectors, mem_filter, mem_multiplicityVectors]

/-- **Restricted partitions as restricted multiplicity vectors**: for `n ≤ N`, the partitions
of `n` all of whose parts satisfy `P` are in bijection with the multiplicity vectors of weight
`n` on `{1, …, N}` supported on `P`.  This is the general form of `Fabius.card_odds_eq`. -/
theorem card_restricted_eq (P : ℕ → Prop) [DecidablePred P] {n N : ℕ} (hN : n ≤ N) :
    (Nat.Partition.restricted n P).card = (restrictedVectors P N n).card := by
  refine Finset.card_bij (fun p _ => partMultiplicity N p) ?_ ?_ ?_
  · intro p hp
    rw [Nat.Partition.restricted, mem_filter] at hp
    rw [mem_restrictedVectors]
    refine ⟨sum_partMultiplicity hN p, fun k hk => ?_⟩
    exact Multiset.count_eq_zero.mpr fun h => hk (hp.2 _ h)
  · intro p _ p' _ h
    exact partMultiplicity_injective hN h
  · intro m hm
    rw [mem_restrictedVectors] at hm
    refine ⟨partitionOfMultiplicity n m hm.1, ?_,
      partMultiplicity_partitionOfMultiplicity n m hm.1⟩
    rw [Nat.Partition.restricted, mem_filter]
    refine ⟨mem_univ _, fun i hi => ?_⟩
    rw [partitionOfMultiplicity_parts] at hi
    unfold multisetOfMultiplicity at hi
    rw [Multiset.mem_sum] at hi
    obtain ⟨k, -, hk⟩ := hi
    rw [Multiset.mem_replicate] at hk
    obtain ⟨hk0, rfl⟩ := hk
    by_contra hP
    exact hk0 (hm.2 k hP)

theorem card_restricted_le_partitionCount (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    (Nat.Partition.restricted n P).card ≤ partitionCount n := card_le_univ _

theorem boundedCount_le (r n : ℕ) : boundedCount r n ≤ partitionCount n := card_le_univ _

/-! ### The finite-alphabet generating function -/

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- `∑_n #restrictedVectors P N n · q^n = ∏_{k<N, P (k+1)} (1 - q^{k+1})⁻¹` for `‖q‖ < 1`.
This generalises `Fabius.hasSum_card_oddVectors`. -/
theorem hasSum_card_restrictedVectors (P : ℕ → Prop) [DecidablePred P] {q : 𝕜} (hq : ‖q‖ < 1)
    (N : ℕ) :
    HasSum (fun n : ℕ => ((restrictedVectors P N n).card : 𝕜) * q ^ n)
      (∏ k : Fin N, if P ((k : ℕ) + 1) then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1) := by
  let g : Fin N → ℕ → 𝕜 := fun k m =>
    if P ((k : ℕ) + 1) then (q ^ ((k : ℕ) + 1)) ^ m else (if m = 0 then 1 else 0)
  have hlt : ∀ k : Fin N, ‖q ^ ((k : ℕ) + 1)‖ < 1 := fun k => by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero _)
  have hg : ∀ k, Summable fun m => ‖g k m‖ := fun k => by
    by_cases he : P ((k : ℕ) + 1)
    · have hgk : (fun m => ‖g k m‖) = fun m => ‖(q ^ ((k : ℕ) + 1)) ^ m‖ := by
        funext m
        simp only [g]
        rw [if_pos he]
      rw [hgk]
      exact (summable_geometric_of_lt_one (norm_nonneg _) (hlt k)).congr fun m =>
        (norm_pow _ _).symm
    · refine summable_of_ne_finset_zero (s := range 1) fun m hm => ?_
      rw [mem_range] at hm
      simp only [g]
      rw [if_neg he, if_neg (by omega), norm_zero]
  obtain ⟨h, -⟩ := hasSum_prod_fin_pi N g hg
  have hval : ∀ k : Fin N, ∑' m : ℕ, g k m =
      if P ((k : ℕ) + 1) then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1 := fun k => by
    by_cases he : P ((k : ℕ) + 1)
    · rw [if_pos he]
      have hgk : (fun m => g k m) = fun m => (q ^ ((k : ℕ) + 1)) ^ m := by
        funext m
        simp only [g]
        rw [if_pos he]
      rw [hgk]
      exact tsum_geometric_of_norm_lt_one (hlt k)
    · rw [if_neg he]
      have hgk : (fun m => g k m) = fun m => if m = 0 then (1 : 𝕜) else 0 := by
        funext m
        simp only [g]
        rw [if_neg he]
      rw [hgk]
      exact (hasSum_ite_eq 0 (1 : 𝕜)).tsum_eq
  rw [prod_congr rfl fun k _ => hval k] at h
  have h2 := hasSum_regroup h (fun m : Fin N → ℕ => ∑ k : Fin N, ((k : ℕ) + 1) * m k)
    (fun n => multiplicityVectors N n) (fun n m => mem_multiplicityVectors)
  refine h2.congr_fun fun n => ?_
  have hzero : ∀ m ∈ multiplicityVectors N n, (∏ k, g k (m k)) ≠ 0 →
      ∀ k : Fin N, ¬ P ((k : ℕ) + 1) → m k = 0 := by
    intro m _ hne k hk
    by_contra hmk
    apply hne
    exact prod_eq_zero (mem_univ k) (by simp only [g]; rw [if_neg hk, if_neg hmk])
  rw [← sum_filter_of_ne hzero]
  have hterm : ∀ m ∈ (multiplicityVectors N n).filter
      (fun m : Fin N → ℕ => ∀ k : Fin N, ¬ P ((k : ℕ) + 1) → m k = 0),
      (∏ k, g k (m k)) = q ^ n := by
    intro m hm
    rw [mem_filter] at hm
    have hfac : ∀ k, g k (m k) = (q ^ ((k : ℕ) + 1)) ^ m k := fun k => by
      simp only [g]
      by_cases he : P ((k : ℕ) + 1)
      · rw [if_pos he]
      · rw [if_neg he, if_pos (hm.2 k he), hm.2 k he, pow_zero]
    rw [prod_congr rfl fun k _ => hfac k]
    simp_rw [← pow_mul]
    rw [prod_pow_eq_pow_sum, mem_multiplicityVectors.mp hm.1]
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
  rfl

/-! ### The generating function of a restricted partition count -/

/-- **The generating function of partitions with all parts satisfying `P`.**  If the alphabet
sizes `N M` tend to infinity and the associated finite products converge to `L`, then
`∑_n #{partitions of n with all parts satisfying P} q^n = L` for `‖q‖ < 1`.

This is the general form of `Fabius.hasSum_oddCount_mul_pow` (take `P = (¬ Even ·)` and
`N M = 2 * M`) and of `Fabius.hasSum_boundedCount_mul_pow` (take `P = (· ≤ r)`); it is stated
for an arbitrary complete normed field. -/
theorem hasSum_restrictedCount_mul_pow (P : ℕ → Prop) [DecidablePred P] {q : 𝕜} (hq : ‖q‖ < 1)
    {L : 𝕜} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (hL : Tendsto (fun M : ℕ => ∏ k : Fin (N M),
        if P ((k : ℕ) + 1) then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1) atTop (𝓝 L)) :
    HasSum (fun n : ℕ => ((Nat.Partition.restricted n P).card : 𝕜) * q ^ n) L := by
  have hbound : Summable fun n : ℕ => (partitionCount n : ℝ) * ‖q‖ ^ n :=
    summable_partitionCount_mul_pow (norm_nonneg q) hq
  have hsum : Summable fun n : ℕ => ((Nat.Partition.restricted n P).card : 𝕜) * q ^ n :=
    Summable.of_norm_bounded hbound fun n => by
      rw [norm_mul, norm_pow]
      calc ‖((Nat.Partition.restricted n P).card : 𝕜)‖ * ‖q‖ ^ n
          ≤ ((Nat.Partition.restricted n P).card : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_natCast_le' _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact card_restricted_le_partitionCount P n
  have hlim1 : Tendsto (fun M : ℕ => ∑' n : ℕ, ((restrictedVectors P (N M) n).card : 𝕜) * q ^ n)
      atTop (𝓝 L) := by
    simp_rw [fun M : ℕ => (hasSum_card_restrictedVectors P hq (N M)).tsum_eq]
    exact hL
  have hlim2 : Tendsto (fun M : ℕ => ∑' n : ℕ, ((restrictedVectors P (N M) n).card : 𝕜) * q ^ n)
      atTop (𝓝 (∑' n : ℕ, ((Nat.Partition.restricted n P).card : 𝕜) * q ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_)
      (Eventually.of_forall fun M n => ?_)
    · obtain ⟨M₀, hM₀⟩ := Filter.eventually_atTop.mp (hN.eventually_ge_atTop n)
      refine tendsto_atTop_of_eventually_const (i₀ := M₀) fun M hM => ?_
      rw [card_restricted_eq P (hM₀ M hM)]
    · rw [norm_mul, norm_pow]
      calc ‖((restrictedVectors P (N M) n).card : 𝕜)‖ * ‖q‖ ^ n
          ≤ ((restrictedVectors P (N M) n).card : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_natCast_le' _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact (card_filter_le _ _).trans (card_multiplicityVectors_le (N M) n)
  have heq := tendsto_nhds_unique hlim2 hlim1
  rw [← heq]
  exact hsum.hasSum

/-! ### The two mod-`5` finite products -/

theorem tendsto_five_mul_atTop : Tendsto (fun M : ℕ => 5 * M) atTop atTop := by
  refine Filter.tendsto_atTop_atTop.mpr fun b => ⟨b, fun a ha => ?_⟩
  show b ≤ 5 * a
  omega

/-- The parts `≡ 1, 4 (mod 5)` below `5M`, as a reciprocal pair of finite `q`-Pochhammers. -/
theorem prod_range_mod5_14_inv (q : 𝕜) (M : ℕ) :
    (∏ k ∈ range (5 * M),
        if (k + 1) % 5 = 1 ∨ (k + 1) % 5 = 4 then (1 - q ^ (k + 1))⁻¹ else 1) =
      (finiteQPochhammerIn q (q ^ 5) M * finiteQPochhammerIn (q ^ 4) (q ^ 5) M)⁻¹ := by
  induction M with
  | zero => simp [finiteQPochhammerIn]
  | succ M ih =>
    have h5 : 5 * (M + 1) = 5 * M + 1 + 1 + 1 + 1 + 1 := by ring
    have c1 : (5 * M + 1) % 5 = 1 ∨ (5 * M + 1) % 5 = 4 := Or.inl (by omega)
    have c2 : ¬((5 * M + 1 + 1) % 5 = 1 ∨ (5 * M + 1 + 1) % 5 = 4) := by
      rintro (h | h) <;> omega
    have c3 : ¬((5 * M + 1 + 1 + 1) % 5 = 1 ∨ (5 * M + 1 + 1 + 1) % 5 = 4) := by
      rintro (h | h) <;> omega
    have c4 : (5 * M + 1 + 1 + 1 + 1) % 5 = 1 ∨ (5 * M + 1 + 1 + 1 + 1) % 5 = 4 :=
      Or.inr (by omega)
    have c5 : ¬((5 * M + 1 + 1 + 1 + 1 + 1) % 5 = 1 ∨
        (5 * M + 1 + 1 + 1 + 1 + 1) % 5 = 4) := by
      rintro (h | h) <;> omega
    rw [h5, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ,
      ih, finiteQPochhammerIn_succ, finiteQPochhammerIn_succ,
      if_pos c1, if_neg c2, if_neg c3, if_pos c4, if_neg c5,
      show q ^ (5 * M + 1) = q * (q ^ 5) ^ M by ring,
      show q ^ (5 * M + 1 + 1 + 1 + 1) = q ^ 4 * (q ^ 5) ^ M by ring]
    simp only [mul_one, mul_inv]
    ring

/-- The parts `≡ 2, 3 (mod 5)` below `5M`, as a reciprocal pair of finite `q`-Pochhammers. -/
theorem prod_range_mod5_23_inv (q : 𝕜) (M : ℕ) :
    (∏ k ∈ range (5 * M),
        if (k + 1) % 5 = 2 ∨ (k + 1) % 5 = 3 then (1 - q ^ (k + 1))⁻¹ else 1) =
      (finiteQPochhammerIn (q ^ 2) (q ^ 5) M * finiteQPochhammerIn (q ^ 3) (q ^ 5) M)⁻¹ := by
  induction M with
  | zero => simp [finiteQPochhammerIn]
  | succ M ih =>
    have h5 : 5 * (M + 1) = 5 * M + 1 + 1 + 1 + 1 + 1 := by ring
    have c1 : ¬((5 * M + 1) % 5 = 2 ∨ (5 * M + 1) % 5 = 3) := by
      rintro (h | h) <;> omega
    have c2 : (5 * M + 1 + 1) % 5 = 2 ∨ (5 * M + 1 + 1) % 5 = 3 := Or.inl (by omega)
    have c3 : (5 * M + 1 + 1 + 1) % 5 = 2 ∨ (5 * M + 1 + 1 + 1) % 5 = 3 := Or.inr (by omega)
    have c4 : ¬((5 * M + 1 + 1 + 1 + 1) % 5 = 2 ∨ (5 * M + 1 + 1 + 1 + 1) % 5 = 3) := by
      rintro (h | h) <;> omega
    have c5 : ¬((5 * M + 1 + 1 + 1 + 1 + 1) % 5 = 2 ∨
        (5 * M + 1 + 1 + 1 + 1 + 1) % 5 = 3) := by
      rintro (h | h) <;> omega
    rw [h5, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ,
      ih, finiteQPochhammerIn_succ, finiteQPochhammerIn_succ,
      if_neg c1, if_pos c2, if_pos c3, if_neg c4, if_neg c5,
      show q ^ (5 * M + 1 + 1) = q ^ 2 * (q ^ 5) ^ M by ring,
      show q ^ (5 * M + 1 + 1 + 1) = q ^ 3 * (q ^ 5) ^ M by ring]
    simp only [mul_one, mul_inv]
    ring

/-- `∏_{k < 5M, k+1 ≡ 1,4 (5)} (1 - q^{k+1})⁻¹ = 1/((q;q⁵)_M (q⁴;q⁵)_M)`. -/
theorem prod_mod5_14_inv (q : 𝕜) (M : ℕ) :
    (∏ k : Fin (5 * M), if ((k : ℕ) + 1) % 5 = 1 ∨ ((k : ℕ) + 1) % 5 = 4
        then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1) =
      (finiteQPochhammerIn q (q ^ 5) M * finiteQPochhammerIn (q ^ 4) (q ^ 5) M)⁻¹ := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if (k + 1) % 5 = 1 ∨ (k + 1) % 5 = 4
    then (1 - q ^ (k + 1))⁻¹ else 1) (5 * M)]
  exact prod_range_mod5_14_inv q M

/-- `∏_{k < 5M, k+1 ≡ 2,3 (5)} (1 - q^{k+1})⁻¹ = 1/((q²;q⁵)_M (q³;q⁵)_M)`. -/
theorem prod_mod5_23_inv (q : 𝕜) (M : ℕ) :
    (∏ k : Fin (5 * M), if ((k : ℕ) + 1) % 5 = 2 ∨ ((k : ℕ) + 1) % 5 = 3
        then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1) =
      (finiteQPochhammerIn (q ^ 2) (q ^ 5) M * finiteQPochhammerIn (q ^ 3) (q ^ 5) M)⁻¹ := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if (k + 1) % 5 = 2 ∨ (k + 1) % 5 = 3
    then (1 - q ^ (k + 1))⁻¹ else 1) (5 * M)]
  exact prod_range_mod5_23_inv q M

/-! ### The two mod-`5` partition counts -/

/-- `p_{1,4}(n)`: the number of partitions of `n` into parts congruent to `1` or `4` mod `5`. -/
def partsMod5_14 (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun i : ℕ => i % 5 = 1 ∨ i % 5 = 4)).card

/-- `p_{2,3}(n)`: the number of partitions of `n` into parts congruent to `2` or `3` mod `5`. -/
def partsMod5_23 (n : ℕ) : ℕ :=
  (Nat.Partition.restricted n (fun i : ℕ => i % 5 = 2 ∨ i % 5 = 3)).card

/-- **The product side of the first Rogers–Ramanujan identity as a partition count**:
`∑_n p_{1,4}(n) q^n = 1/((q;q⁵)_∞ (q⁴;q⁵)_∞)` for `‖q‖ < 1`. -/
theorem hasSum_partsMod5_14 {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partsMod5_14 n : 𝕜) * q ^ n)
      ((qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹) := by
  have h5 : ‖q ^ 5‖ < 1 := norm_pow_five_lt_one hq
  have hne1 : qPochhammerInfIn q (q ^ 5) ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one h5 hq
  have hne4 : qPochhammerInfIn (q ^ 4) (q ^ 5) ≠ 0 :=
    qPochhammerInfIn_pow_pow_five_ne_zero hq (by norm_num)
  have hprod : Tendsto (fun M : ℕ => ∏ k : Fin (5 * M),
      if ((k : ℕ) + 1) % 5 = 1 ∨ ((k : ℕ) + 1) % 5 = 4
        then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1) atTop
      (𝓝 ((qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹)) := by
    simp_rw [prod_mod5_14_inv]
    exact ((tendsto_finiteQPochhammerIn_qPochhammerInfIn q h5).mul
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn (q ^ 4) h5)).inv₀ (mul_ne_zero hne1 hne4)
  exact (hasSum_restrictedCount_mul_pow (fun i : ℕ => i % 5 = 1 ∨ i % 5 = 4) hq
    tendsto_five_mul_atTop hprod).congr_fun fun n => by rw [partsMod5_14]

/-- **The product side of the second Rogers–Ramanujan identity as a partition count**:
`∑_n p_{2,3}(n) q^n = 1/((q²;q⁵)_∞ (q³;q⁵)_∞)` for `‖q‖ < 1`. -/
theorem hasSum_partsMod5_23 {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partsMod5_23 n : 𝕜) * q ^ n)
      ((qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹) := by
  have h5 : ‖q ^ 5‖ < 1 := norm_pow_five_lt_one hq
  have hne2 : qPochhammerInfIn (q ^ 2) (q ^ 5) ≠ 0 :=
    qPochhammerInfIn_pow_pow_five_ne_zero hq (by norm_num)
  have hne3 : qPochhammerInfIn (q ^ 3) (q ^ 5) ≠ 0 :=
    qPochhammerInfIn_pow_pow_five_ne_zero hq (by norm_num)
  have hprod : Tendsto (fun M : ℕ => ∏ k : Fin (5 * M),
      if ((k : ℕ) + 1) % 5 = 2 ∨ ((k : ℕ) + 1) % 5 = 3
        then (1 - q ^ ((k : ℕ) + 1))⁻¹ else 1) atTop
      (𝓝 ((qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹)) := by
    simp_rw [prod_mod5_23_inv]
    exact ((tendsto_finiteQPochhammerIn_qPochhammerInfIn (q ^ 2) h5).mul
      (tendsto_finiteQPochhammerIn_qPochhammerInfIn (q ^ 3) h5)).inv₀ (mul_ne_zero hne2 hne3)
  exact (hasSum_restrictedCount_mul_pow (fun i : ℕ => i % 5 = 2 ∨ i % 5 = 3) hq
    tendsto_five_mul_atTop hprod).congr_fun fun n => by rw [partsMod5_23]

/-- The first Rogers–Ramanujan identity, read as a partition statement:
`∑_n p_{1,4}(n) q^n = ∑_n q^{n²}/(q;q)_n`. -/
theorem hasSum_partsMod5_14_rogersRamanujan {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partsMod5_14 n : 𝕜) * q ^ n)
      (∑' n : ℕ, q ^ (n * n) / finiteQPochhammerIn q q n) := by
  rw [(hasSum_rogersRamanujan_first hq).tsum_eq]
  exact hasSum_partsMod5_14 hq

/-- The second Rogers–Ramanujan identity, read as a partition statement:
`∑_n p_{2,3}(n) q^n = ∑_n q^{n(n+1)}/(q;q)_n`. -/
theorem hasSum_partsMod5_23_rogersRamanujan {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (partsMod5_23 n : 𝕜) * q ^ n)
      (∑' n : ℕ, q ^ (n * (n + 1)) / finiteQPochhammerIn q q n) := by
  rw [(hasSum_rogersRamanujan_second hq).tsum_eq]
  exact hasSum_partsMod5_23 hq

/-! ### The Durfee-staircase side -/

/-- The Durfee-staircase count with offset `e`:
`staircaseCount e n = ∑_{k : e k ≤ n} p_{≤ k}(n - e k)`.

For `e k = k²` this is the coefficient extracted from `∑_k q^{k²}/(q;q)_k`, and for
`e k = k² + k` the one extracted from `∑_k q^{k²+k}/(q;q)_k`.  The printed proof of
`qg:cor-rr-partitions` identifies it (after conjugating the remainder) with the number of
partitions of `n` whose successive parts differ by at least `2`; that identification is not
formalised in this module. -/
def staircaseCount (e : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => e k ≤ n), boundedCount k (n - e k)

/-- **The staircase generating function**: for an offset `e` with `k ≤ e k` and `‖q‖ < 1`, if
`∑_k q^{e k}/(q;q)_k = S` then `∑_n staircaseCount e n · q^n = S`.

This is the step the printed proof leaves implicit: it fixes the number `k` of parts, computes
the generating function `q^{e k}/(q;q)_k` of that stratum, and then sums over `k`.  Here the
interchange is a genuine fibrewise summation over `ℕ × ℕ` followed by a regrouping by the total
degree `e k + m`. -/
theorem hasSum_staircaseCount (e : ℕ → ℕ) (he : ∀ k : ℕ, k ≤ e k) {q : 𝕜} (hq : ‖q‖ < 1)
    {S : 𝕜} (hS : HasSum (fun k : ℕ => q ^ e k / finiteQPochhammerIn q q k) S) :
    HasSum (fun n : ℕ => (staircaseCount e n : 𝕜) * q ^ n) S := by
  obtain ⟨F, hFdef⟩ : ∃ F : ℕ × ℕ → 𝕜,
      F = fun p : ℕ × ℕ => (boundedCount p.1 p.2 : 𝕜) * q ^ (e p.1 + p.2) := ⟨_, rfl⟩
  -- the fibre over a fixed number `k` of staircase rows
  have hfib : ∀ k : ℕ, HasSum (fun m : ℕ => F (k, m))
      (q ^ e k / finiteQPochhammerIn q q k) := by
    intro k
    have h := (hasSum_boundedCount_mul_pow hq k).mul_left (q ^ e k)
    rw [← div_eq_mul_inv] at h
    refine h.congr_fun fun m => ?_
    have hval : F (k, m) = (boundedCount k m : 𝕜) * q ^ (e k + m) := by rw [hFdef]
    rw [hval, pow_add]
    ring
  -- absolute convergence of the double family
  have hdom : Summable fun p : ℕ × ℕ => ‖q‖ ^ p.1 * ((partitionCount p.2 : ℝ) * ‖q‖ ^ p.2) :=
    Summable.mul_of_nonneg (summable_geometric_of_lt_one (norm_nonneg q) hq)
      (summable_partitionCount_mul_pow (norm_nonneg q) hq)
      (fun k => pow_nonneg (norm_nonneg q) k)
      (fun m => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (norm_nonneg q) m))
  have hFsum : Summable F := by
    refine Summable.of_norm_bounded hdom fun p => ?_
    have hval : F p = (boundedCount p.1 p.2 : 𝕜) * q ^ (e p.1 + p.2) := by rw [hFdef]
    rw [hval, norm_mul, norm_pow, pow_add]
    have h1 : ‖((boundedCount p.1 p.2 : ℕ) : 𝕜)‖ ≤ (partitionCount p.2 : ℝ) :=
      (norm_natCast_le' _).trans (by exact_mod_cast boundedCount_le p.1 p.2)
    have h2 : ‖q‖ ^ e p.1 ≤ ‖q‖ ^ p.1 :=
      pow_le_pow_of_le_one (norm_nonneg q) hq.le (he p.1)
    calc ‖((boundedCount p.1 p.2 : ℕ) : 𝕜)‖ * (‖q‖ ^ e p.1 * ‖q‖ ^ p.2)
        ≤ (partitionCount p.2 : ℝ) * (‖q‖ ^ p.1 * ‖q‖ ^ p.2) :=
          mul_le_mul h1 (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
            (by positivity)
      _ = ‖q‖ ^ p.1 * ((partitionCount p.2 : ℝ) * ‖q‖ ^ p.2) := by ring
  have hFS : HasSum F S := by
    have h1 : HasSum (fun k : ℕ => q ^ e k / finiteQPochhammerIn q q k)
        (∑' p : ℕ × ℕ, F p) := hFsum.hasSum.prod_fiberwise hfib
    have h2 : S = ∑' p : ℕ × ℕ, F p := hS.unique h1
    rw [h2]
    exact hFsum.hasSum
  -- regroup by the total degree
  have hinj : ∀ m : ℕ, Function.Injective (fun k : ℕ => ((k, m - e k) : ℕ × ℕ)) := by
    intro m a b hab
    have h := congrArg Prod.fst hab
    simpa using h
  refine (hasSum_regroup hFS (fun p : ℕ × ℕ => e p.1 + p.2)
    (fun n : ℕ => ((range (n + 1)).filter (fun k : ℕ => e k ≤ n)).map
      ⟨fun k : ℕ => ((k, n - e k) : ℕ × ℕ), hinj n⟩) ?_).congr_fun ?_
  · intro n p
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_filter, mem_range]
    constructor
    · rintro ⟨k, ⟨-, hk2⟩, rfl⟩
      show e k + (n - e k) = n
      omega
    · intro hp
      have h1 := he p.1
      refine ⟨p.1, ⟨by omega, by omega⟩, ?_⟩
      have h2 : n - e p.1 = p.2 := by omega
      rw [h2]
  · intro n
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    rw [staircaseCount, Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun k hk => ?_
    rw [mem_filter] at hk
    have hval : F (k, n - e k) = (boundedCount k (n - e k) : 𝕜) * q ^ (e k + (n - e k)) := by
      rw [hFdef]
    rw [hval, show e k + (n - e k) = n by omega]

/-- The staircase side of the first Rogers–Ramanujan identity:
`∑_n (∑_{k : k² ≤ n} p_{≤ k}(n - k²)) q^n = 1/((q;q⁵)_∞ (q⁴;q⁵)_∞)`. -/
theorem hasSum_staircaseCount_sq {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (staircaseCount (fun k : ℕ => k * k) n : 𝕜) * q ^ n)
      ((qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹) :=
  hasSum_staircaseCount (fun k : ℕ => k * k) (fun k => Nat.le_mul_self k) hq
    (hasSum_rogersRamanujan_first hq)

/-- The staircase side of the second Rogers–Ramanujan identity:
`∑_n (∑_{k : k²+k ≤ n} p_{≤ k}(n - k² - k)) q^n = 1/((q²;q⁵)_∞ (q³;q⁵)_∞)`. -/
theorem hasSum_staircaseCount_sq_add {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (staircaseCount (fun k : ℕ => k * k + k) n : 𝕜) * q ^ n)
      ((qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹) :=
  hasSum_staircaseCount (fun k : ℕ => k * k + k) (fun k => Nat.le_add_left k (k * k)) hq
    ((hasSum_rogersRamanujan_second hq).congr_fun fun n => by
      rw [show n * (n + 1) = n * n + n by ring])

/-! ### The coefficient identities -/

/-- **The first Rogers–Ramanujan partition identity, product half.**  For every `N`, the number
of partitions of `N` into parts congruent to `1` or `4` mod `5` equals
`∑_{k : k² ≤ N} p_{≤ k}(N - k²)`.

Relative to clause (i) of `qg:cor-rr-partitions`, the gap count "partitions whose successive
parts differ by at least `2`" is replaced by the Durfee-staircase count; the staircase
bijection between the two is not formalised here. -/
theorem partsMod5_14_eq_staircaseCount (n : ℕ) :
    partsMod5_14 n = staircaseCount (fun k : ℕ => k * k) n := by
  have key : (fun n : ℕ => (partsMod5_14 n : ℂ)) =
      fun n : ℕ => (staircaseCount (fun k : ℕ => k * k) n : ℂ) :=
    eq_of_hasSum_pow_eq
      (f := fun z : ℂ => (qPochhammerInfIn z (z ^ 5) * qPochhammerInfIn (z ^ 4) (z ^ 5))⁻¹)
      one_pos (fun z hz => hasSum_partsMod5_14 hz) (fun z hz => hasSum_staircaseCount_sq hz)
  exact_mod_cast congrFun key n

/-- **The second Rogers–Ramanujan partition identity, product half.**  For every `N`, the number
of partitions of `N` into parts congruent to `2` or `3` mod `5` equals
`∑_{k : k²+k ≤ N} p_{≤ k}(N - k² - k)`.

Relative to clause (ii) of `qg:cor-rr-partitions`, the gap count "partitions whose successive
parts differ by at least `2` and whose smallest part is at least `2`" is replaced by the
Durfee-staircase count; the staircase bijection between the two is not formalised here. -/
theorem partsMod5_23_eq_staircaseCount (n : ℕ) :
    partsMod5_23 n = staircaseCount (fun k : ℕ => k * k + k) n := by
  have key : (fun n : ℕ => (partsMod5_23 n : ℂ)) =
      fun n : ℕ => (staircaseCount (fun k : ℕ => k * k + k) n : ℂ) :=
    eq_of_hasSum_pow_eq
      (f := fun z : ℂ => (qPochhammerInfIn (z ^ 2) (z ^ 5) * qPochhammerInfIn (z ^ 3) (z ^ 5))⁻¹)
      one_pos (fun z hz => hasSum_partsMod5_23 hz) (fun z hz => hasSum_staircaseCount_sq_add hz)
  exact_mod_cast congrFun key n

end Fabius

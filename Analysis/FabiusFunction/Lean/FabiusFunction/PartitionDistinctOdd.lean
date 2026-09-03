import FabiusFunction.PartitionGeneratingFunction
import FabiusFunction.PowerSeriesUniqueness

/-!
# Partitions into distinct parts and into odd parts

With `d(n) = #(Nat.Partition.distincts n)` and `o(n) = #(Nat.Partition.odds n)`, for `‖q‖ < 1`,

`∑_n d(n) q^n = (-q;q)_∞`,  `∑_n o(n) q^n = 1/(q;q^2)_∞`,  and `d(n) = o(n)` (Euler).

The two generating functions are obtained exactly as the partition generating function of
`PartitionGeneratingFunction`: through the restricted multiplicity vectors (entries at most `1`,
respectively supported on the odd parts), the Cauchy product of the corresponding finite or
geometric series, and Tannery's theorem.  The identity `(-q;q)_∞ = 1/(q;q^2)_∞` follows from
`(q^2;q^2)_∞ = (q;q)_∞ (-q;q)_∞` (termwise `(1-x)(1+x) = 1-x^2`) and the dissection
`(q;q)_∞ = (q;q^2)_∞ (q^2;q^2)_∞`, and the identity theorem for power series turns the equality
of the two generating functions into `d(n) = o(n)`.

## Main declarations

* `distinctVectors`, `oddVectors`, `card_distincts_eq`, `card_odds_eq`.
* `hasSum_card_distinctVectors`, `hasSum_card_oddVectors`.
* `qPochhammerInfIn_neg_self_eq`: `(-q;q)_∞ = 1/(q;q^2)_∞`.
* `hasSum_distinctCount_mul_pow`, `hasSum_oddCount_mul_pow`, `distinctCount_eq_oddCount`.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-! ### Restricted multiplicity vectors -/

/-- The multiplicity vectors of weight `n` with every multiplicity at most `1`. -/
def distinctVectors (N n : ℕ) : Finset (Fin N → ℕ) :=
  (multiplicityVectors N n).filter fun m => ∀ k : Fin N, m k ≤ 1

/-- The multiplicity vectors of weight `n` supported on the odd parts. -/
def oddVectors (N n : ℕ) : Finset (Fin N → ℕ) :=
  (multiplicityVectors N n).filter fun m => ∀ k : Fin N, Even ((k : ℕ) + 1) → m k = 0

/-- For `n ≤ N` a partition of `n` is determined by its multiplicity vector on `{1, …, N}`:
`partMultiplicity N` is injective.  This is the injectivity half of
`partitionEquivMultiplicity`, and it is what the `Finset.card_bij` proofs below need. -/
theorem partMultiplicity_injective {n N : ℕ} (hN : n ≤ N) :
    Function.Injective (partMultiplicity (n := n) N) := by
  intro p p' h
  exact (partitionEquivMultiplicity n N hN).injective (Subtype.ext h)

/-- Reading the multiplicities back off the partition built from `m` returns `m`:
`partitionOfMultiplicity` is a right inverse of `partMultiplicity N`.  This supplies the
surjectivity witness in `card_distincts_eq` and `card_odds_eq`. -/
theorem partMultiplicity_partitionOfMultiplicity (n : ℕ) {N : ℕ} (m : Fin N → ℕ)
    (h : ∑ k : Fin N, ((k : ℕ) + 1) * m k = n) :
    partMultiplicity N (partitionOfMultiplicity n m h) = m := by
  funext k
  show (partitionOfMultiplicity n m h).parts.count ((k : ℕ) + 1) = m k
  rw [partitionOfMultiplicity_parts, count_multisetOfMultiplicity]

/-- A vector `m : Fin N → ℕ` only ever produces parts `1, …, N`, so a part `j + 1` beyond the
alphabet occurs with multiplicity `0`.  This is the `j ≥ N` companion of
`count_multisetOfMultiplicity`; the `Nodup` check in `card_distincts_eq` runs over all part
sizes, not just those below `N`. -/
theorem count_multisetOfMultiplicity_of_ge {N : ℕ} (m : Fin N → ℕ) {j : ℕ} (hj : N ≤ j) :
    (multisetOfMultiplicity m).count (j + 1) = 0 := by
  rw [Multiset.count_eq_zero]
  intro h
  unfold multisetOfMultiplicity at h
  rw [Multiset.mem_sum] at h
  obtain ⟨k, -, hk⟩ := h
  rw [Multiset.mem_replicate] at hk
  omega

/-- `d(n) = #{m : Fin N → ℕ | ∑ (k+1) m_k = n, m_k ≤ 1}` for `n ≤ N`. -/
theorem card_distincts_eq {n N : ℕ} (hN : n ≤ N) :
    (Nat.Partition.distincts n).card = (distinctVectors N n).card := by
  refine Finset.card_bij (fun p _ => partMultiplicity N p) ?_ ?_ ?_
  · intro p hp
    rw [Nat.Partition.distincts, mem_filter] at hp
    rw [distinctVectors, mem_filter, mem_multiplicityVectors]
    exact ⟨sum_partMultiplicity hN p, fun k => Multiset.nodup_iff_count_le_one.mp hp.2 _⟩
  · intro p _ p' _ h
    exact partMultiplicity_injective hN h
  · intro m hm
    rw [distinctVectors, mem_filter, mem_multiplicityVectors] at hm
    refine ⟨partitionOfMultiplicity n m hm.1, ?_, partMultiplicity_partitionOfMultiplicity n m hm.1⟩
    rw [Nat.Partition.distincts, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    rw [Multiset.nodup_iff_count_le_one]
    intro i
    rw [partitionOfMultiplicity_parts]
    rcases i with _ | j
    · rw [Multiset.count_eq_zero.mpr fun h => (pos_of_mem_multisetOfMultiplicity h).ne' rfl]
      exact Nat.zero_le _
    · by_cases hj : j < N
      · have := count_multisetOfMultiplicity m ⟨j, hj⟩
        simp only [Fin.val_mk] at this
        rw [this]
        exact hm.2 _
      · rw [count_multisetOfMultiplicity_of_ge m (not_lt.mp hj)]
        exact Nat.zero_le _

/-- `o(n) = #{m : Fin N → ℕ | ∑ (k+1) m_k = n, m_k = 0 for k+1 even}` for `n ≤ N`. -/
theorem card_odds_eq {n N : ℕ} (hN : n ≤ N) :
    (Nat.Partition.odds n).card = (oddVectors N n).card := by
  refine Finset.card_bij (fun p _ => partMultiplicity N p) ?_ ?_ ?_
  · intro p hp
    unfold Nat.Partition.odds Nat.Partition.restricted at hp
    rw [mem_filter] at hp
    rw [oddVectors, mem_filter, mem_multiplicityVectors]
    exact ⟨sum_partMultiplicity hN p, fun k hk =>
      Multiset.count_eq_zero.mpr fun h => hp.2 _ h hk⟩
  · intro p _ p' _ h
    exact partMultiplicity_injective hN h
  · intro m hm
    rw [oddVectors, mem_filter, mem_multiplicityVectors] at hm
    refine ⟨partitionOfMultiplicity n m hm.1, ?_, partMultiplicity_partitionOfMultiplicity n m hm.1⟩
    unfold Nat.Partition.odds Nat.Partition.restricted
    rw [mem_filter]
    refine ⟨mem_univ _, fun i hi => ?_⟩
    rw [partitionOfMultiplicity_parts] at hi
    unfold multisetOfMultiplicity at hi
    rw [Multiset.mem_sum] at hi
    obtain ⟨k, -, hk⟩ := hi
    rw [Multiset.mem_replicate] at hk
    obtain ⟨hk0, rfl⟩ := hk
    exact fun heven => hk0 (hm.2 k heven)

/-! ### The generating functions with parts at most `N` -/

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- `∑_n #distinctVectors N n · q^n = ∏_{k<N} (1 + q^{k+1})`. -/
theorem hasSum_card_distinctVectors (q : 𝕜) (N : ℕ) :
    HasSum (fun n : ℕ => ((distinctVectors N n).card : 𝕜) * q ^ n)
      (∏ k : Fin N, (1 + q ^ ((k : ℕ) + 1))) := by
  let g : Fin N → ℕ → 𝕜 := fun k m => if m ≤ 1 then (q ^ ((k : ℕ) + 1)) ^ m else 0
  have hg0 : ∀ k : Fin N, ∀ m ∉ range 2, g k m = 0 := fun k m hm => by
    rw [mem_range] at hm
    simp only [g]
    rw [if_neg (by omega)]
  have hg : ∀ k, Summable fun m => ‖g k m‖ := fun k =>
    summable_of_ne_finset_zero (s := range 2) fun m hm => by rw [hg0 k m hm, norm_zero]
  obtain ⟨h, -⟩ := hasSum_prod_fin_pi N g hg
  have hval : ∀ k : Fin N, ∑' m : ℕ, g k m = 1 + q ^ ((k : ℕ) + 1) := fun k => by
    rw [tsum_eq_sum (s := range 2) (hg0 k)]
    simp [g, sum_range_succ]
  rw [prod_congr rfl fun k _ => hval k] at h
  have h2 := hasSum_regroup h (fun m : Fin N → ℕ => ∑ k : Fin N, ((k : ℕ) + 1) * m k)
    (fun n => multiplicityVectors N n) (fun n m => mem_multiplicityVectors)
  refine h2.congr_fun fun n => ?_
  have hzero : ∀ m ∈ multiplicityVectors N n, (∏ k, g k (m k)) ≠ 0 → ∀ k : Fin N, m k ≤ 1 := by
    intro m _ hne k
    by_contra hk
    apply hne
    exact prod_eq_zero (mem_univ k) (by simp only [g]; rw [if_neg hk])
  rw [← sum_filter_of_ne hzero]
  have hterm : ∀ m ∈ (multiplicityVectors N n).filter (fun m => ∀ k : Fin N, m k ≤ 1),
      (∏ k, g k (m k)) = q ^ n := by
    intro m hm
    rw [mem_filter] at hm
    have : ∀ k, g k (m k) = (q ^ ((k : ℕ) + 1)) ^ m k := fun k => by
      simp only [g]
      rw [if_pos (hm.2 k)]
    rw [prod_congr rfl fun k _ => this k]
    simp_rw [← pow_mul]
    rw [prod_pow_eq_pow_sum, mem_multiplicityVectors.mp hm.1]
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
  rfl

/-- `∑_n #oddVectors N n · q^n = ∏_{k<N, k+1 odd} (1 - q^{k+1})^{-1}`. -/
theorem hasSum_card_oddVectors {q : 𝕜} (hq : ‖q‖ < 1) (N : ℕ) :
    HasSum (fun n : ℕ => ((oddVectors N n).card : 𝕜) * q ^ n)
      (∏ k : Fin N, if Even ((k : ℕ) + 1) then 1 else (1 - q ^ ((k : ℕ) + 1))⁻¹) := by
  let g : Fin N → ℕ → 𝕜 := fun k m =>
    if Even ((k : ℕ) + 1) then (if m = 0 then 1 else 0) else (q ^ ((k : ℕ) + 1)) ^ m
  have hlt : ∀ k : Fin N, ‖q ^ ((k : ℕ) + 1)‖ < 1 := fun k => by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (Nat.succ_ne_zero _)
  have hg : ∀ k, Summable fun m => ‖g k m‖ := fun k => by
    by_cases he : Even ((k : ℕ) + 1)
    · refine summable_of_ne_finset_zero (s := range 1) fun m hm => ?_
      rw [mem_range] at hm
      simp only [g]
      rw [if_pos he, if_neg (by omega), norm_zero]
    · have : (fun m => ‖g k m‖) = fun m => ‖(q ^ ((k : ℕ) + 1)) ^ m‖ := by
        funext m
        simp only [g]
        rw [if_neg he]
      rw [this]
      exact (summable_geometric_of_lt_one (norm_nonneg _) (hlt k)).congr fun m =>
        (norm_pow _ _).symm
  obtain ⟨h, -⟩ := hasSum_prod_fin_pi N g hg
  have hval : ∀ k : Fin N, ∑' m : ℕ, g k m =
      if Even ((k : ℕ) + 1) then 1 else (1 - q ^ ((k : ℕ) + 1))⁻¹ := fun k => by
    by_cases he : Even ((k : ℕ) + 1)
    · rw [if_pos he]
      have : (fun m => g k m) = fun m => if m = 0 then (1 : 𝕜) else 0 := by
        funext m
        simp only [g]
        rw [if_pos he]
      rw [this]
      exact (hasSum_ite_eq 0 (1 : 𝕜)).tsum_eq
    · rw [if_neg he]
      have : (fun m => g k m) = fun m => (q ^ ((k : ℕ) + 1)) ^ m := by
        funext m
        simp only [g]
        rw [if_neg he]
      rw [this]
      exact tsum_geometric_of_norm_lt_one (hlt k)
  rw [prod_congr rfl fun k _ => hval k] at h
  have h2 := hasSum_regroup h (fun m : Fin N → ℕ => ∑ k : Fin N, ((k : ℕ) + 1) * m k)
    (fun n => multiplicityVectors N n) (fun n m => mem_multiplicityVectors)
  refine h2.congr_fun fun n => ?_
  have hzero : ∀ m ∈ multiplicityVectors N n, (∏ k, g k (m k)) ≠ 0 →
      ∀ k : Fin N, Even ((k : ℕ) + 1) → m k = 0 := by
    intro m _ hne k hk
    by_contra hmk
    apply hne
    exact prod_eq_zero (mem_univ k) (by simp only [g]; rw [if_pos hk, if_neg hmk])
  rw [← sum_filter_of_ne hzero]
  have hterm : ∀ m ∈ (multiplicityVectors N n).filter
      (fun m => ∀ k : Fin N, Even ((k : ℕ) + 1) → m k = 0), (∏ k, g k (m k)) = q ^ n := by
    intro m hm
    rw [mem_filter] at hm
    have : ∀ k, g k (m k) = (q ^ ((k : ℕ) + 1)) ^ m k := fun k => by
      simp only [g]
      by_cases he : Even ((k : ℕ) + 1)
      · rw [if_pos he, if_pos (hm.2 k he), hm.2 k he, pow_zero]
      · rw [if_neg he]
    rw [prod_congr rfl fun k _ => this k]
    simp_rw [← pow_mul]
    rw [prod_pow_eq_pow_sum, mem_multiplicityVectors.mp hm.1]
  rw [sum_congr rfl hterm, sum_const, nsmul_eq_mul]
  rfl

/-! ### The finite products -/

omit [CompleteSpace 𝕜] in
/-- The distinct-parts product with parts at most `N` is `(-q;q)_N`:
`∏_{k<N} (1 + q^{k+1}) = (-q;q)_N`, since the `j`-th factor `1 - (-q) q^j` of the finite
q-Pochhammer product is `1 + q^{j+1}`. -/
theorem prod_one_add_pow_succ (q : 𝕜) (N : ℕ) :
    ∏ k : Fin N, (1 + q ^ ((k : ℕ) + 1)) = finiteQPochhammerIn (-q) q N := by
  rw [finiteQPochhammerIn, ← Fin.prod_univ_eq_prod_range (fun j => 1 - -q * q ^ j) N]
  exact prod_congr rfl fun k _ => by simp only [neg_mul, sub_neg_eq_add, pow_succ']

/-- Pairing consecutive factors: `∏_{k<2n} f k = ∏_{j<n} f(2j) f(2j+1)`.  This is what splits
a product over the parts `1, …, 2M` into its odd and even halves in `prod_odd_inv`. -/
theorem prod_range_two_mul {M : Type*} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ k ∈ range (2 * n), f k = ∏ j ∈ range n, (f (2 * j) * f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, prod_range_succ, prod_range_succ, ih,
      prod_range_succ, mul_assoc]

omit [CompleteSpace 𝕜] in
/-- The odd-part product with parts below `2M` is `1/(q;q^2)_M`. -/
theorem prod_odd_inv (q : 𝕜) (M : ℕ) :
    (∏ k : Fin (2 * M), if Even ((k : ℕ) + 1) then (1 : 𝕜) else (1 - q ^ ((k : ℕ) + 1))⁻¹) =
      (finiteQPochhammerIn q (q ^ 2) M)⁻¹ := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if Even (k + 1) then (1 : 𝕜) else (1 - q ^ (k + 1))⁻¹)
    (2 * M), prod_range_two_mul, finiteQPochhammerIn, ← prod_inv_distrib]
  refine prod_congr rfl fun j _ => ?_
  have h1 : ¬ Even (2 * j + 1) := by
    rw [Nat.not_even_iff_odd]
    exact odd_two_mul_add_one j
  have h2 : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
  rw [if_neg h1, if_pos h2, mul_one, ← pow_mul, pow_succ', mul_comm 2 j]

/-! ### The infinite products -/

/-- `(q^2;q^2)_∞ = (q;q)_∞ (-q;q)_∞`. -/
theorem qPochhammerInfIn_sq_eq {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn (q ^ 2) (q ^ 2) = qPochhammerInfIn q q * qPochhammerInfIn (-q) q := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have h := (hasProd_qPochhammerInfIn q hq).mul (hasProd_qPochhammerInfIn (-q) hq)
  have h' : HasProd (fun j : ℕ => 1 - q ^ 2 * (q ^ 2) ^ j)
      (qPochhammerInfIn q q * qPochhammerInfIn (-q) q) := by
    refine h.congr_fun fun j => ?_
    show 1 - q ^ 2 * (q ^ 2) ^ j = (1 - q * q ^ j) * (1 - -q * q ^ j)
    ring
  exact (hasProd_qPochhammerInfIn (q ^ 2) hq2).unique h'

/-- The dissection `(q;q)_∞ = (q;q^2)_∞ (q^2;q^2)_∞`. -/
theorem qPochhammerInfIn_self_eq_odd_mul_even {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q = qPochhammerInfIn q (q ^ 2) * qPochhammerInfIn (q ^ 2) (q ^ 2) := by
  rw [qPochhammerInfIn_dissection q hq (r := 2) two_pos, prod_range_succ, prod_range_succ,
    prod_range_zero, one_mul, pow_zero, mul_one, pow_one, ← pow_two]

/-- **Euler**: `(-q;q)_∞ = 1/(q;q^2)_∞` for `‖q‖ < 1`. -/
theorem qPochhammerInfIn_neg_self_eq {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn (-q) q = (qPochhammerInfIn q (q ^ 2))⁻¹ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have h1 : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hq
  have h2 : qPochhammerInfIn (q ^ 2) (q ^ 2) ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq2 hq2
  have h3 : qPochhammerInfIn q (q ^ 2) ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq2 hq
  have hsq := qPochhammerInfIn_sq_eq hq
  have hdis := qPochhammerInfIn_self_eq_odd_mul_even hq
  rw [hdis] at hsq
  have hone : qPochhammerInfIn q (q ^ 2) * qPochhammerInfIn (-q) q = 1 := by
    have hA : qPochhammerInfIn (q ^ 2) (q ^ 2) *
        (qPochhammerInfIn q (q ^ 2) * qPochhammerInfIn (-q) q) =
        qPochhammerInfIn (q ^ 2) (q ^ 2) * 1 := by
      rw [mul_one]
      linear_combination -hsq
    exact mul_left_cancel₀ h2 hA
  exact eq_inv_of_mul_eq_one_right hone

/-! ### The generating functions of `d(n)` and `o(n)` -/

/-- `d(n)`: the number of partitions of `n` into distinct parts. -/
def distinctCount (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- `o(n)`: the number of partitions of `n` into odd parts. -/
def oddCount (n : ℕ) : ℕ := (Nat.Partition.odds n).card

/-- `d(n) ≤ p(n)`: the partitions into distinct parts form a subset of all partitions of `n`.
This is the coefficient bound that makes `∑ p(n) ‖q‖^n` a majorant for the distinct-parts
series. -/
theorem distinctCount_le (n : ℕ) : distinctCount n ≤ partitionCount n := card_le_univ _

/-- `o(n) ≤ p(n)`: the partitions into odd parts form a subset of all partitions of `n`, the
majorant bound used for the odd-parts series. -/
theorem oddCount_le (n : ℕ) : oddCount n ≤ partitionCount n := card_le_univ _

omit [CompleteSpace 𝕜] in
/-- `‖(n : 𝕜)‖ ≤ n` for a natural number `n`: Mathlib's `Nat.norm_cast_le` with the factor
`‖1‖ = 1` cleared away.  It converts the norm of an integer coefficient in `𝕜` into the real
counting bound needed for the dominated-convergence estimates below. -/
theorem norm_natCast_le' (n : ℕ) : ‖(n : 𝕜)‖ ≤ n := by
  have := Nat.norm_cast_le (α := 𝕜) n
  rwa [norm_one, mul_one] at this

/-- **The generating function of partitions into distinct parts**:
`∑_n d(n) q^n = (-q;q)_∞` for `‖q‖ < 1`. -/
theorem hasSum_distinctCount_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (distinctCount n : 𝕜) * q ^ n) (qPochhammerInfIn (-q) q) := by
  have hbound : Summable fun n : ℕ => (partitionCount n : ℝ) * ‖q‖ ^ n :=
    summable_partitionCount_mul_pow (norm_nonneg q) hq
  have hsum : Summable fun n : ℕ => (distinctCount n : 𝕜) * q ^ n :=
    Summable.of_norm_bounded hbound fun n => by
      rw [norm_mul, norm_pow]
      calc ‖(distinctCount n : 𝕜)‖ * ‖q‖ ^ n ≤ (distinctCount n : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_natCast_le' _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact distinctCount_le n
  have hfin : ∀ N, HasSum (fun n : ℕ => ((distinctVectors N n).card : 𝕜) * q ^ n)
      (finiteQPochhammerIn (-q) q N) := fun N => by
    have := hasSum_card_distinctVectors q N
    rwa [prod_one_add_pow_succ] at this
  have hlim1 : Tendsto (fun N : ℕ => ∑' n : ℕ, ((distinctVectors N n).card : 𝕜) * q ^ n)
      atTop (𝓝 (qPochhammerInfIn (-q) q)) := by
    simp_rw [fun N => (hfin N).tsum_eq]
    exact tendsto_finiteQPochhammerIn_qPochhammerInfIn (-q) hq
  have hlim2 : Tendsto (fun N : ℕ => ∑' n : ℕ, ((distinctVectors N n).card : 𝕜) * q ^ n)
      atTop (𝓝 (∑' n : ℕ, (distinctCount n : 𝕜) * q ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) (Eventually.of_forall
      fun N n => ?_)
    · refine tendsto_atTop_of_eventually_const (i₀ := n) fun N hN => ?_
      rw [distinctCount, card_distincts_eq hN]
    · rw [norm_mul, norm_pow]
      calc ‖((distinctVectors N n).card : 𝕜)‖ * ‖q‖ ^ n
          ≤ ((distinctVectors N n).card : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_natCast_le' _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact (card_filter_le _ _).trans (card_multiplicityVectors_le N n)
  have heq := tendsto_nhds_unique hlim2 hlim1
  rw [← heq]
  exact hsum.hasSum

/-- **The generating function of partitions into odd parts**:
`∑_n o(n) q^n = 1/(q;q^2)_∞` for `‖q‖ < 1`. -/
theorem hasSum_oddCount_mul_pow {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (oddCount n : 𝕜) * q ^ n) (qPochhammerInfIn q (q ^ 2))⁻¹ := by
  have hq2 : ‖q ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq two_ne_zero
  have hbound : Summable fun n : ℕ => (partitionCount n : ℝ) * ‖q‖ ^ n :=
    summable_partitionCount_mul_pow (norm_nonneg q) hq
  have hsum : Summable fun n : ℕ => (oddCount n : 𝕜) * q ^ n :=
    Summable.of_norm_bounded hbound fun n => by
      rw [norm_mul, norm_pow]
      calc ‖(oddCount n : 𝕜)‖ * ‖q‖ ^ n ≤ (oddCount n : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_natCast_le' _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact oddCount_le n
  have hfin : ∀ M, HasSum (fun n : ℕ => ((oddVectors (2 * M) n).card : 𝕜) * q ^ n)
      (finiteQPochhammerIn q (q ^ 2) M)⁻¹ := fun M => by
    have := hasSum_card_oddVectors hq (2 * M)
    rwa [prod_odd_inv] at this
  have hlim1 : Tendsto (fun M : ℕ => ∑' n : ℕ, ((oddVectors (2 * M) n).card : 𝕜) * q ^ n)
      atTop (𝓝 (qPochhammerInfIn q (q ^ 2))⁻¹) := by
    simp_rw [fun M => (hfin M).tsum_eq]
    exact (tendsto_finiteQPochhammerIn_qPochhammerInfIn q hq2).inv₀
      (qPochhammerInfIn_ne_zero_of_norm_lt_one hq2 hq)
  have hlim2 : Tendsto (fun M : ℕ => ∑' n : ℕ, ((oddVectors (2 * M) n).card : 𝕜) * q ^ n)
      atTop (𝓝 (∑' n : ℕ, (oddCount n : 𝕜) * q ^ n)) := by
    refine tendsto_tsum_of_dominated_convergence hbound (fun n => ?_) (Eventually.of_forall
      fun M n => ?_)
    · refine tendsto_atTop_of_eventually_const (i₀ := n) fun M hM => ?_
      rw [oddCount, card_odds_eq (by omega : n ≤ 2 * M)]
    · rw [norm_mul, norm_pow]
      calc ‖((oddVectors (2 * M) n).card : 𝕜)‖ * ‖q‖ ^ n
          ≤ ((oddVectors (2 * M) n).card : ℝ) * ‖q‖ ^ n :=
            mul_le_mul_of_nonneg_right (norm_natCast_le' _) (by positivity)
        _ ≤ (partitionCount n : ℝ) * ‖q‖ ^ n := by
            gcongr
            exact (card_filter_le _ _).trans (card_multiplicityVectors_le (2 * M) n)
  have heq := tendsto_nhds_unique hlim2 hlim1
  rw [← heq]
  exact hsum.hasSum

/-- **Euler's theorem**: the number of partitions of `n` into distinct parts equals the number
of partitions of `n` into odd parts. -/
theorem distinctCount_eq_oddCount (n : ℕ) : distinctCount n = oddCount n := by
  have key : (fun n => (distinctCount n : ℂ)) = fun n => (oddCount n : ℂ) :=
    eq_of_hasSum_pow_eq (f := fun z : ℂ => qPochhammerInfIn (-z) z) one_pos
      (fun z hz => hasSum_distinctCount_mul_pow hz)
      (fun z hz => by
        show HasSum _ (qPochhammerInfIn (-z) z)
        rw [qPochhammerInfIn_neg_self_eq hz]
        exact hasSum_oddCount_mul_pow hz)
  exact_mod_cast congrFun key n

end Fabius

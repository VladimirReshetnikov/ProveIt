import GRHArticle.ProgressionFree.PolynomialTwoPrimeTransfer
import GRHArticle.ProgressionFree.PolynomialCounterexample

/-!
# The binary two-prime bound

The first 32 Roth increments have an exact dyadic numerator. Later
increments are bounded by one, so their normalized contribution is
at most `2⁻³²`. A finite ternary prefix of the true greedy benchmark
certifies the strict upper bound on the binary density gap.
-/

namespace GRHArticle.ProgressionFree

open scoped Classical BigOperators

/-- The numerator of a dyadic increment prefix with denominator `2^L`. -/
def binaryRothPrefixNumerator (r : ℕ → ℕ) (L : ℕ) : ℕ :=
  ∑ t ∈ Finset.range L, (r (t+1) - r t) * 2^(L-1-t)

/-- The interval Roth counts through 32 used by the binary bound. -/
def binaryRothNumberTable (n : ℕ) : ℕ :=
  ([0, 1, 2, 2, 3, 4, 4, 4, 4, 5, 5, 6, 6, 7, 8, 8, 8,
    8, 8, 8, 9, 9, 9, 9, 10, 10, 11, 11, 11, 11, 12, 12, 13] : List ℕ)[n]?.getD 0

/-- Exact dyadic evaluation of the table used in the article. -/
theorem binaryRothPrefixNumerator_table :
    binaryRothPrefixNumerator binaryRothNumberTable 32 = 3635155269 := by
  decide +kernel

private theorem binaryRothPrefixNumerator_congr {r s : ℕ → ℕ} {L : ℕ}
    (h : ∀ n ≤ L, r n = s n) :
    binaryRothPrefixNumerator r L = binaryRothPrefixNumerator s L := by
  unfold binaryRothPrefixNumerator
  apply Finset.sum_congr rfl
  intro t ht
  have h₀ := Finset.mem_range.mp ht
  rw [h t (by omega), h (t+1) (by omega)]

private theorem binaryRothPrefix_eq_numerator (r : ℕ → ℕ) (L : ℕ) :
    (1 / (2:ℝ)) * ∑ t ∈ Finset.range L, ((r (t+1) - r t : ℕ):ℝ) * (1 / (2:ℝ))^t =
      (binaryRothPrefixNumerator r L : ℝ) / (2:ℝ)^L := by
  unfold binaryRothPrefixNumerator
  push_cast only [Nat.cast_sum, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp only [div_eq_mul_inv, one_mul, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  have htL := Finset.mem_range.mp ht
  have hL : L = (L-1-t) + (t+1) := by omega
  rw [show (2:ℝ)^L = 2^(L-1-t) * 2^(t+1) by rw [← pow_add, ← hL]]
  rw [inv_pow, pow_succ (2:ℝ) t]
  field_simp

/-- The normalized remainder beyond the first `L` binary Roth increments. -/
theorem binary_rothIncrement_tail_le (L : ℕ) :
    (1 / (2:ℝ)) * (∑' t : ℕ, ((rothNumberNat (t+L+1) - rothNumberNat (t+L) : ℕ):ℝ) *
      (1 / (2:ℝ))^(t+L)) ≤ 1 / (2:ℝ)^L := by
  let z : ℝ := 1/2
  let a (t : ℕ) := ((rothNumberNat (t+1) - rothNumberNat t : ℕ):ℝ) * z^t
  have ha : Summable a := summable_rothIncrement_weight (by norm_num [z]) (by norm_num [z])
  have hg : Summable (fun t : ℕ ↦ z^t) := summable_geometric_of_lt_one (by norm_num [z]) (by norm_num [z])
  have hs := (summable_nat_add_iff L).mpr ha
  have hb : (∑' t, a (t+L)) ≤ ∑' t : ℕ, z^t * z^L := by
    refine hs.tsum_le_tsum (fun t ↦ ?_) (hg.mul_right (z^L))
    change ((rothNumberNat (t+L+1) - rothNumberNat (t+L) : ℕ):ℝ) * z^(t+L) ≤ _
    rw [← pow_add]
    have hinc : ((rothNumberNat (t+L+1) - rothNumberNat (t+L) : ℕ):ℝ) ≤ 1 := by
      exact_mod_cast rothNumberNat_increment_le_one (t+L)
    exact mul_le_of_le_one_left (pow_nonneg (by norm_num [z]) _) hinc
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num [z]) (by norm_num [z]),
    show (1-z)⁻¹ = 2 by norm_num [z]] at hb
  change z * (∑' t, a (t+L)) ≤ 1 / (2:ℝ)^L
  calc
    _ ≤ z * (2*z^L) := mul_le_mul_of_nonneg_left hb (by norm_num [z])
    _ = _ := by rw [← mul_assoc, show z*2 = 1 by norm_num [z], one_mul, show z = 1 / (2:ℝ) by rfl, one_div_pow]

/-- Any certified binary prefix numerator gives the one-prime bound with its
explicit dyadic tail. -/
theorem polynomialOnePrimeRothBound_binary_le_prefix
    (F : Type*) [Field F] [Fintype F] (hq : Fintype.card F = 2) (L : ℕ) :
    polynomialOnePrimeRothBound F ≤
      (binaryRothPrefixNumerator (fun n ↦ rothNumberNat n) L + 1 : ℕ) / (2:ℝ)^L := by
  let z : ℝ := 1/2
  let a (t : ℕ) := ((rothNumberNat (t+1) - rothNumberNat t : ℕ):ℝ) * z^t
  have ha : Summable a := summable_rothIncrement_weight (by norm_num [z]) (by norm_num [z])
  have hs : polynomialOnePrimeRothBound F = z * ∑' t, a t := by
    rw [polynomialOnePrimeRothBound_eq_increment_series, hq]
    norm_num [a,z, one_div]
  rw [hs, ← ha.sum_add_tsum_nat_add L, mul_add]
  have hhead := binaryRothPrefix_eq_numerator (fun n ↦ rothNumberNat n) L
  have htail := binary_rothIncrement_tail_le L
  change z * (∑ t ∈ Finset.range L, a t) = _ at hhead
  change z * (∑' t, a (t+L)) ≤ _ at htail
  rw [hhead, Nat.cast_add, Nat.cast_one, add_div]
  exact add_le_add_right htail _

/-- The exact rational two-prime bound from a bound on the first 32 increments. -/
theorem polynomialRatioDensitySupremum_binary_le_of_rothPrefix
    (F : Type*) [Field F] [Fintype F] (hq : Fintype.card F = 2)
    (ht : TwoPrimeTriangleBound)
    (hprefix : binaryRothPrefixNumerator (fun n ↦ rothNumberNat n) 32 ≤ 3635155269) :
    polynomialRatioDensitySupremum F ≤ (907739729:ℝ)/1073741824 := by
  have h := polynomialRatioDensitySupremum_le_twoPrime_of_triangle F ht
  rw [hq] at h
  have hp := polynomialOnePrimeRothBound_binary_le_prefix F hq 32
  rw [Nat.cast_add, Nat.cast_one] at hp
  have hc : (binaryRothPrefixNumerator (fun n ↦ rothNumberNat n) 32 : ℝ) ≤
      ((3635155269 : ℕ) : ℝ) := Nat.cast_le.mpr hprefix
  have hbound := hp.trans (div_le_div_of_nonneg_right (add_le_add_left hc 1) (by positivity))
  refine h.trans ?_
  norm_num at hbound ⊢
  linarith only [hbound]

/-- The article's binary rational and decimal upper bounds from the interval count table. -/
theorem polynomialRatioDensitySupremum_binary_le_of_rothTable
    (F : Type*) [Field F] [Fintype F] (hq : Fintype.card F = 2)
    (ht : TwoPrimeTriangleBound) (hroth : ∀ n ≤ 32, rothNumberNat n = binaryRothNumberTable n) :
    polynomialRatioDensitySupremum F ≤ (907739729:ℝ)/1073741824 ∧
      (907739729:ℝ)/1073741824 < 0.845398501494 := by
  refine ⟨polynomialRatioDensitySupremum_binary_le_of_rothPrefix F hq ht ?_, by norm_num⟩
  exact (binaryRothPrefixNumerator_congr hroth).trans_le binaryRothPrefixNumerator_table.le

private def binaryGreedyPrefix : Finset ℕ :=
  {0, 1, 3, 4, 9, 10, 12, 13, 27, 28, 30, 31, 36, 37, 39, 40}

private theorem binaryGreedyPrefix_admissible : ∀ n ∈ binaryGreedyPrefix, n ∈ greedyExponents := by
  change ∀ n ∈ binaryGreedyPrefix, ∀ d ∈ Nat.digits 3 n, d ≤ 1
  decide +kernel

/-- Sixteen greedy exponents already certify the binary benchmark at the
precision needed for the strict density gap. -/
theorem polynomialDegreeBenchmark_binary_lower (F : Type*) [Field F] [Fintype F]
    (hq : Fintype.card F = 2) :
    (1859049764379:ℝ)/2199023255552 ≤ polynomialDegreeBenchmark F := by
  let z : ℝ := 1/2
  let a (n : ℕ) := greedyExponents.indicator (fun n ↦ z^n) n
  have ha₀ (n : ℕ) : 0 ≤ a n := by
    dsimp [a]
    exact Set.indicator_nonneg (fun n _ ↦ pow_nonneg (by norm_num [z]) n) _
  have ha : Summable a := by
    refine Summable.of_nonneg_of_le ha₀ (fun n ↦ ?_)
      (summable_geometric_of_lt_one (r := z) (by norm_num [z]) (by norm_num [z]))
    dsimp [a]
    by_cases hn : n ∈ greedyExponents
    · rw [Set.indicator_of_mem hn]
    · rw [Set.indicator_of_notMem hn]
      positivity
  have hsum := ha.sum_le_tsum binaryGreedyPrefix (fun n _ ↦ ha₀ n)
  have hprefix : (∑ n ∈ binaryGreedyPrefix, a n) = ∑ n ∈ binaryGreedyPrefix, z^n := by
    apply Finset.sum_congr rfl
    intro n hn
    exact Set.indicator_of_mem (binaryGreedyPrefix_admissible n hn) _
  have hbench : polynomialDegreeBenchmark F = z * ∑' n, a n := by
    norm_num [polynomialDegreeBenchmark, hq, a, z, one_div]
  rw [hprefix] at hsum
  have hweight : (1859049764379:ℝ)/2199023255552 = z * ∑ n ∈ binaryGreedyPrefix, z^n := by
    norm_num [binaryGreedyPrefix, z, Finset.sum_insert]
  rw [hbench, hweight]
  exact mul_le_mul_of_nonneg_left hsum (by norm_num [z])

/-- A rigorous strict bound on the difference from the actual greedy benchmark. -/
theorem polynomialRatioDensitySupremum_binary_gap_of_rothTable
    (F : Type*) [Field F] [Fintype F] (hq : Fintype.card F = 2)
    (ht : TwoPrimeTriangleBound) (hroth : ∀ n ≤ 32, rothNumberNat n = binaryRothNumberTable n) :
    0 < polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F ∧
      polynomialRatioDensitySupremum F - polynomialDegreeBenchmark F < 5.46e-7 := by
  constructor
  · exact sub_pos.mpr (polynomialDegreeBenchmark_lt_polynomialRatioDensitySupremum F)
  · calc
      _ ≤ (907739729:ℝ)/1073741824 - (1859049764379:ℝ)/2199023255552 :=
        sub_le_sub (polynomialRatioDensitySupremum_binary_le_of_rothTable F hq ht hroth).1
          (polynomialDegreeBenchmark_binary_lower F hq)
      _ < 5.46e-7 := by norm_num

end GRHArticle.ProgressionFree

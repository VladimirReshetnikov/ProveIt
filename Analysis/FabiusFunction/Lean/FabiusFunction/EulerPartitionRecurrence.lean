import FabiusFunction.PartitionGeneratingFunction
import FabiusFunction.PowerSeriesUniqueness
import FabiusFunction.JacobiTripleProduct
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Euler's partition recurrence

Multiplying the pentagonal number theorem `(q;q)_∞ = ∑_{k ∈ ℤ} (-1)^k q^{k(3k-1)/2}` by the
partition generating function `∑_n p(n) q^n = 1/(q;q)_∞` gives `1`; comparing coefficients
(`eq_of_hasSum_pow_eq`, the identity theorem for power series) yields the convolution identity
`∑_{k+l=n} e(k) p(l) = δ_{n,0}` with the pentagonal coefficients
`e(k) = ∑_{j : j(3j-1)/2 = k} (-1)^j`, and unfolding the pentagonal fibres gives Euler's
recurrence

`p(n) = ∑_{j=1}^{n} (-1)^{j-1} (p(n - j(3j-1)/2) + p(n - j(3j+1)/2))`   (`n ≥ 1`),

with `p(m) = 0` for `m < 0` (`partitionCountSub`).

## Main declarations

* `pentagonalFibre`, `pentagonalCoeff`, `hasSum_pentagonalCoeff_mul_pow`.
* `sum_antidiagonal_pentagonalCoeff_mul_partitionCount`: the convolution identity.
* `sum_pentagonalCoeff_mul`: unfolding the pentagonal fibres.
* `partitionCount_eq_pentagonal_sum`: Euler's recurrence.
-/

set_option autoImplicit false

open Finset Filter Topology

namespace Fabius

/-- `|k| ≤ k(3k-1)/2`. -/
theorem natAbs_le_pentagonalExponent (k : ℤ) : k.natAbs ≤ pentagonalExponent k := by
  have h := two_mul_pentagonalExponent k
  have : (k.natAbs : ℤ) ≤ (pentagonalExponent k : ℤ) := by
    rw [Int.natCast_natAbs]
    rcases le_or_gt 0 k with hk | hk
    · rw [abs_of_nonneg hk]
      rcases eq_or_lt_of_le hk with rfl | hpos
      · simp
      · nlinarith
    · rw [abs_of_neg hk]
      nlinarith
  exact_mod_cast this

/-- The integers `k` with `k(3k-1)/2 = n`. -/
noncomputable def pentagonalFibre (n : ℕ) : Finset ℤ :=
  (Finset.Icc (-(n : ℤ)) n).filter fun k => pentagonalExponent k = n

theorem mem_pentagonalFibre {n : ℕ} {k : ℤ} :
    k ∈ pentagonalFibre n ↔ pentagonalExponent k = n := by
  unfold pentagonalFibre
  rw [mem_filter, Finset.mem_Icc]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    have h1 := natAbs_le_pentagonalExponent k
    rw [h] at h1
    have h2 : (k.natAbs : ℤ) ≤ n := by exact_mod_cast h1
    rw [Int.natCast_natAbs] at h2
    exact abs_le.mp h2

/-- **Euler's pentagonal coefficients** `e(n) = ∑_{k : k(3k-1)/2 = n} (-1)^k`. -/
noncomputable def pentagonalCoeff (n : ℕ) : ℂ := ∑ k ∈ pentagonalFibre n, (-1 : ℂ) ^ k

theorem pentagonalExponent_zero : pentagonalExponent 0 = 0 := by
  simp [pentagonalExponent]

theorem pentagonalFibre_zero : pentagonalFibre 0 = {0} := by
  ext k
  rw [mem_pentagonalFibre, mem_singleton]
  constructor
  · intro h
    by_contra hk
    exact (pentagonalExponent_pos hk).ne' h
  · rintro rfl
    exact pentagonalExponent_zero

theorem pentagonalCoeff_zero : pentagonalCoeff 0 = 1 := by
  rw [pentagonalCoeff, pentagonalFibre_zero, sum_singleton, zpow_zero]

theorem norm_pentagonalCoeff_le (n : ℕ) : ‖pentagonalCoeff n‖ ≤ 2 * n + 1 := by
  unfold pentagonalCoeff
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_zpow, norm_neg, norm_one, one_zpow, sum_const, nsmul_eq_mul, mul_one]
  have h1 : (pentagonalFibre n).card ≤ (Finset.Icc (-(n : ℤ)) n).card := card_filter_le _ _
  have h2 : (Finset.Icc (-(n : ℤ)) n).card = 2 * n + 1 := by
    rw [Int.card_Icc, show (n : ℤ) + 1 - -(n : ℤ) = ((2 * n + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
  calc ((pentagonalFibre n).card : ℝ) ≤ ((Finset.Icc (-(n : ℤ)) n).card : ℝ) := by
        exact_mod_cast h1
    _ = 2 * n + 1 := by rw [h2]; push_cast; ring

/-- The pentagonal number theorem as a power series in `q`:
`∑_n e(n) q^n = (q;q)_∞` for `‖q‖ < 1`. -/
theorem hasSum_pentagonalCoeff_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => pentagonalCoeff n * q ^ n) (qPochhammerInfIn q q) := by
  have h := hasSum_regroup (hasSum_pentagonal hq) pentagonalExponent pentagonalFibre
    fun n k => mem_pentagonalFibre
  refine h.congr_fun fun n => ?_
  rw [pentagonalCoeff, sum_mul]
  exact sum_congr rfl fun k hk => by rw [mem_pentagonalFibre.mp hk]

theorem summable_norm_pentagonalCoeff_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖pentagonalCoeff n * q ^ n‖ := by
  have hq' : ‖(‖q‖ : ℝ)‖ < 1 := by rwa [Real.norm_of_nonneg (norm_nonneg q)]
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hq'
  have h2 := summable_geometric_of_lt_one (norm_nonneg q) hq
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) ((h1.mul_left 2).add h2)
  rw [norm_mul, norm_pow]
  calc ‖pentagonalCoeff n‖ * ‖q‖ ^ n ≤ (2 * n + 1) * ‖q‖ ^ n :=
        mul_le_mul_of_nonneg_right (norm_pentagonalCoeff_le n) (by positivity)
    _ = 2 * ((n : ℝ) ^ 1 * ‖q‖ ^ n) + ‖q‖ ^ n := by ring

theorem summable_norm_partitionCount_mul_pow {q : ℂ} (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => ‖(partitionCount n : ℂ) * q ^ n‖ := by
  refine (summable_partitionCount_mul_pow (norm_nonneg q) hq).congr fun n => ?_
  rw [norm_mul, norm_pow, Complex.norm_natCast]

/-- **Euler's recurrence in convolution form**: `∑_{k+l=n} e(k) p(l) = δ_{n,0}`. -/
theorem sum_antidiagonal_pentagonalCoeff_mul_partitionCount (n : ℕ) :
    ∑ kl ∈ antidiagonal n, pentagonalCoeff kl.1 * (partitionCount kl.2 : ℂ) =
      if n = 0 then 1 else 0 := by
  have key : (fun n : ℕ => ∑ kl ∈ antidiagonal n,
      pentagonalCoeff kl.1 * (partitionCount kl.2 : ℂ)) = fun n => if n = 0 then 1 else 0 := by
    refine eq_of_hasSum_pow_eq (f := fun _ => (1 : ℂ)) one_pos (fun z hz => ?_) (fun z hz => ?_)
    · have hf := summable_norm_pentagonalCoeff_mul_pow hz
      have hg := summable_norm_partitionCount_mul_pow hz
      have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
      rw [(hasSum_pentagonalCoeff_mul_pow hz).tsum_eq, (hasSum_partitionCount_mul_pow hz).tsum_eq,
        mul_inv_cancel₀ (qPochhammerInfIn_ne_zero_of_norm_lt_one hz hz)] at hprod
      have hS := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
      rw [← hprod] at hS
      refine hS.congr_fun fun n => ?_
      rw [sum_mul]
      refine sum_congr rfl fun kl hkl => ?_
      rw [mem_antidiagonal] at hkl
      rw [← hkl, pow_add]
      ring
    · refine (hasSum_ite_eq 0 (1 : ℂ)).congr_fun fun n => ?_
      by_cases hn : n = 0
      · subst hn
        simp
      · simp [hn]
  exact congrFun key n

/-- The fibres `pentagonalFibre y`, `y ≤ n`, are the fibres of `pentagonalExponent` on the box
`{j : |j| ≤ n, p(j) ≤ n}`. -/
theorem pentagonalFibre_eq_filter {n y : ℕ} (hy : y ≤ n) :
    pentagonalFibre y =
      ((Finset.Icc (-(n : ℤ)) n).filter fun i => pentagonalExponent i ≤ n).filter
        fun i => pentagonalExponent i = y := by
  ext i
  rw [mem_pentagonalFibre, mem_filter, mem_filter, Finset.mem_Icc]
  constructor
  · intro h
    refine ⟨⟨?_, by omega⟩, h⟩
    have h1 := natAbs_le_pentagonalExponent i
    rw [h] at h1
    have h2 : (i.natAbs : ℤ) ≤ n := by exact_mod_cast h1.trans hy
    rw [Int.natCast_natAbs] at h2
    exact abs_le.mp h2
  · exact fun h => h.2

/-- **Unfolding the pentagonal fibres**: for every `f : ℕ → ℂ`,
`∑_{k ≤ n} e(k) f(k) = f(0) + ∑_{j=1}^{n} (-1)^j (F(p(j)) + F(p(-j)))`, where `F(e) = f(e)` if
`e ≤ n` and `0` otherwise. -/
theorem sum_pentagonalCoeff_mul (n : ℕ) (f : ℕ → ℂ) :
    ∑ k ∈ range (n + 1), pentagonalCoeff k * f k =
      f 0 + ∑ j ∈ Icc 1 n, (-1 : ℂ) ^ j *
        ((if pentagonalExponent j ≤ n then f (pentagonalExponent j) else 0) +
         (if pentagonalExponent (-(j : ℤ)) ≤ n then f (pentagonalExponent (-(j : ℤ))) else 0)) := by
  set S : Finset ℤ := (Finset.Icc (-(n : ℤ)) n).filter fun i => pentagonalExponent i ≤ n with hS
  -- Step 1: the left side as a sum over `S`
  have h1 : ∑ k ∈ range (n + 1), pentagonalCoeff k * f k =
      ∑ i ∈ S, (-1 : ℂ) ^ i * f (pentagonalExponent i) := by
    unfold pentagonalCoeff
    simp_rw [sum_mul]
    rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := range (n + 1)) (g := pentagonalExponent)
      (fun i hi => by rw [hS, mem_filter] at hi; exact mem_range.mpr (Nat.lt_succ_of_le hi.2))]
    refine sum_congr rfl fun k hk => ?_
    rw [← pentagonalFibre_eq_filter (Nat.lt_succ_iff.mp (mem_range.mp hk))]
    exact sum_congr rfl fun i hi => by rw [mem_pentagonalFibre.mp hi]
  -- Step 2: split `S` into `{0}`, the positive and the negative part
  have h0 : (0 : ℤ) ∈ S := by
    rw [hS, mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [pentagonalExponent_zero]
    exact Nat.zero_le n
  have hsplit : ∑ i ∈ S, (-1 : ℂ) ^ i * f (pentagonalExponent i) =
      f 0 + (∑ i ∈ S.filter (fun i => 0 < i), (-1 : ℂ) ^ i * f (pentagonalExponent i) +
        ∑ i ∈ S.filter (fun i => i < 0), (-1 : ℂ) ^ i * f (pentagonalExponent i)) := by
    rw [← sum_filter_add_sum_filter_not S (fun i => i = 0)]
    have hz : S.filter (fun i => i = 0) = {0} := by
      ext i
      rw [mem_filter, mem_singleton]
      exact ⟨fun h => h.2, fun h => ⟨h ▸ h0, h⟩⟩
    rw [hz, sum_singleton, zpow_zero, one_mul, pentagonalExponent_zero]
    congr 1
    rw [← sum_filter_add_sum_filter_not (S.filter fun i => ¬ i = 0) (fun i => 0 < i)]
    congr 1
    · refine sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by omega⟩, h3⟩
    · refine sum_congr ?_ fun _ _ => rfl
      ext i
      simp only [mem_filter]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, by omega⟩, by omega⟩
  -- Step 3: the positive part, reindexed by `j = i`
  have hpos : ∑ i ∈ S.filter (fun i => 0 < i), (-1 : ℂ) ^ i * f (pentagonalExponent i) =
      ∑ j ∈ Icc 1 n, (-1 : ℂ) ^ j *
        (if pentagonalExponent j ≤ n then f (pentagonalExponent j) else 0) := by
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    refine sum_nbij' (fun i => i.toNat) (fun j => (j : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_filter, hS, mem_filter, Finset.mem_Icc] at hi
      rw [mem_filter, mem_Icc]
      obtain ⟨⟨⟨_, hin⟩, hpi⟩, hi0⟩ := hi
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rwa [Int.toNat_of_nonneg hi0.le]
    · intro j hj
      rw [mem_filter, mem_Icc] at hj
      rw [mem_filter, hS, mem_filter, Finset.mem_Icc]
      obtain ⟨⟨hj1, hjn⟩, hpj⟩ := hj
      exact ⟨⟨⟨by omega, by omega⟩, hpj⟩, by omega⟩
    · intro i hi
      rw [mem_filter] at hi
      exact Int.toNat_of_nonneg hi.2.le
    · intro j _
      exact Int.toNat_natCast j
    · intro i hi
      rw [mem_filter] at hi
      conv_lhs => rw [← Int.toNat_of_nonneg hi.2.le]
      rw [zpow_natCast]
  -- Step 4: the negative part, reindexed by `j = -i`
  have hneg : ∑ i ∈ S.filter (fun i => i < 0), (-1 : ℂ) ^ i * f (pentagonalExponent i) =
      ∑ j ∈ Icc 1 n, (-1 : ℂ) ^ j *
        (if pentagonalExponent (-(j : ℤ)) ≤ n then f (pentagonalExponent (-(j : ℤ))) else 0) := by
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    refine sum_nbij' (fun i => (-i).toNat) (fun j => -(j : ℤ)) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [mem_filter, hS, mem_filter, Finset.mem_Icc] at hi
      rw [mem_filter, mem_Icc]
      obtain ⟨⟨⟨hin, _⟩, hpi⟩, hi0⟩ := hi
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      rwa [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -i), neg_neg]
    · intro j hj
      rw [mem_filter, mem_Icc] at hj
      rw [mem_filter, hS, mem_filter, Finset.mem_Icc]
      obtain ⟨⟨hj1, hjn⟩, hpj⟩ := hj
      exact ⟨⟨⟨by omega, by omega⟩, hpj⟩, by omega⟩
    · intro i hi
      rw [mem_filter] at hi
      obtain ⟨-, hi0⟩ := hi
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -i), neg_neg]
    · intro j _
      rw [neg_neg, Int.toNat_natCast]
    · intro i hi
      rw [mem_filter] at hi
      obtain ⟨-, hi0⟩ := hi
      have hi' : i = -(((-i).toNat : ℕ) : ℤ) := by
        rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -i), neg_neg]
      conv_lhs => rw [hi']
      rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg_one]
  -- Step 5: assemble
  rw [h1, hsplit, hpos, hneg, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun j _ => by ring

/-- `p(n - e)` with the convention `p(m) = 0` for `m < 0`. -/
def partitionCountSub (n e : ℕ) : ℂ := if e ≤ n then (partitionCount (n - e) : ℂ) else 0

/-- **Euler's partition recurrence**: for `n ≥ 1`,
`p(n) = ∑_{j=1}^{n} (-1)^{j-1} (p(n - j(3j-1)/2) + p(n - j(3j+1)/2))`, with `p(m) = 0` for
`m < 0`. -/
theorem partitionCount_eq_pentagonal_sum {n : ℕ} (hn : 1 ≤ n) :
    (partitionCount n : ℂ) = ∑ j ∈ Icc 1 n, (-1 : ℂ) ^ (j - 1) *
      (partitionCountSub n (pentagonalExponent j) +
        partitionCountSub n (pentagonalExponent (-(j : ℤ)))) := by
  have h := sum_antidiagonal_pentagonalCoeff_mul_partitionCount n
  rw [if_neg (by omega), Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  dsimp only at h
  rw [sum_pentagonalCoeff_mul n (fun k => (partitionCount (n - k) : ℂ)), Nat.sub_zero] at h
  have hsign : ∀ j ∈ Icc 1 n, (-1 : ℂ) ^ (j - 1) *
      (partitionCountSub n (pentagonalExponent j) +
        partitionCountSub n (pentagonalExponent (-(j : ℤ)))) =
      -((-1 : ℂ) ^ j *
        ((if pentagonalExponent j ≤ n then (partitionCount (n - pentagonalExponent j) : ℂ) else 0) +
         (if pentagonalExponent (-(j : ℤ)) ≤ n then
            (partitionCount (n - pentagonalExponent (-(j : ℤ))) : ℂ) else 0))) := by
    intro j hj
    rw [mem_Icc] at hj
    obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]
    unfold partitionCountSub
    ring
  rw [sum_congr rfl hsign, sum_neg_distrib]
  linear_combination h

end Fabius

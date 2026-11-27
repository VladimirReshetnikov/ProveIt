import GRHArticle.ProgressionFree.DensityBounds
import Mathlib.Analysis.PSeries

/-!
# Prime-square tail in the integer smooth estimates

The actual sum over primes bounds the excluded multiples at every cutoff.
Truncating the prime sum leaves an error of at most the reciprocal cutoff.
-/

namespace GRHArticle.ProgressionFree

open Filter Topology Finset
open scoped BigOperators

/-- Contribution of the prime `p` above the smoothness cutoff `Y`. -/
noncomputable def integerPrimeSquareTerm (Y p : ℕ) : ℝ :=
  if Y < p ∧ p.Prime then 1/(p:ℝ)^2 else 0

/-- Sum of the reciprocal squares of the primes strictly above `Y`. -/
noncomputable def integerPrimeSquareTail (Y : ℕ) : ℝ := ∑' p, integerPrimeSquareTerm Y p

theorem integerPrimeSquareTerm_nonneg (Y p : ℕ) : 0 ≤ integerPrimeSquareTerm Y p := by
  unfold integerPrimeSquareTerm
  split <;> positivity

theorem summable_integerPrimeSquareTerm (Y : ℕ) : Summable (integerPrimeSquareTerm Y) := by
  apply (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)).of_nonneg_of_le
    (integerPrimeSquareTerm_nonneg Y)
  intro p
  unfold integerPrimeSquareTerm
  split <;> first | exact le_rfl | positivity

/-- The exact prime tail bounds the density discarded by the squarefree
rough-part construction uniformly in the sample size. -/
theorem densityUpTo_largePrimeSquare_le_tail (Y N : ℕ) :
    densityUpTo {n | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p^2 ∣ n} N ≤ integerPrimeSquareTail Y := by
  let S := (range (N+1)).filter fun p ↦ Y < p ∧ p.Prime
  have hm (p : ℕ) (hp : p ∈ S) : Y < p ∧ p.Prime := (mem_filter.mp hp).2
  calc
    _ ≤ densityUpTo {n | ∃ p ∈ S, p^2 ∣ n} N := by
      apply densityUpTo_le_of_subset_on_cutoff N
      intro n hn ⟨p, hY, hprime, hd⟩
      have hpn : p ≤ n := Nat.le_of_dvd (mem_Icc.mp hn).1 ((dvd_pow_self p (by decide : 2 ≠ 0)).trans hd)
      exact ⟨p, mem_filter.mpr ⟨mem_range.mpr (by have := (mem_Icc.mp hn).2; omega), hY, hprime⟩, hd⟩
    _ ≤ ∑ p ∈ S, 1/(p:ℝ)^2 := by
      simpa only [Nat.cast_pow] using densityUpTo_divisibleByOneOf_le S (fun p ↦ p^2) N
        (fun p hp ↦ pow_pos (hm p hp).2.pos _)
    _ = ∑ p ∈ S, integerPrimeSquareTerm Y p := sum_congr rfl (fun p hp ↦ (if_pos (hm p hp)).symm)
    _ ≤ _ := (summable_integerPrimeSquareTerm Y).sum_le_tsum S (fun p _ ↦ integerPrimeSquareTerm_nonneg Y p)

theorem integerPrimeSquareTail_le_reciprocal {Y : ℕ} (hY : 0 < Y) :
    integerPrimeSquareTail Y ≤ 1/(Y:ℝ) := by
  apply le_of_tendsto' (summable_integerPrimeSquareTerm Y).hasSum.tendsto_sum_nat
  intro n
  let S := (range n).filter fun p ↦ Y < p ∧ p.Prime
  have hs : S ⊆ Ioc Y n := fun p hp ↦
    mem_Ioc.mpr ⟨(mem_filter.mp hp).2.1, (mem_range.mp (mem_filter.mp hp).1).le⟩
  calc
    ∑ p ∈ range n, integerPrimeSquareTerm Y p = ∑ p ∈ S, 1/(p:ℝ)^2 := by
      simp only [S, sum_filter, integerPrimeSquareTerm]
    _ ≤ ∑ p ∈ Ioc Y n, 1/(p:ℝ)^2 := sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ ↦ by positivity)
    _ ≤ _ := sum_Ioc_one_div_sq_le _ _ hY

/-- Split the prime series at a finite cutoff. -/
theorem integerPrimeSquareTail_split {Y K : ℕ} (h : Y ≤ K) :
    integerPrimeSquareTail Y = (∑ p ∈ range (K+1), integerPrimeSquareTerm Y p) +
      integerPrimeSquareTail K := by
  have h₁ := (summable_integerPrimeSquareTerm Y).sum_add_tsum_nat_add (K+1)
  have h₂ := (summable_integerPrimeSquareTerm K).sum_add_tsum_nat_add (K+1)
  have he (n : ℕ) : integerPrimeSquareTerm Y (n+(K+1)) = integerPrimeSquareTerm K (n+(K+1)) := by
    simp [integerPrimeSquareTerm, show Y < n+(K+1) by omega, show K < n+(K+1) by omega]
  have hzero : ∑ n ∈ range (K+1), integerPrimeSquareTerm K n = 0 :=
    sum_eq_zero fun n hn ↦ if_neg (fun e ↦ (Nat.lt_succ_iff.mp (mem_range.mp hn)).not_gt e.1)
  simp only [hzero, zero_add] at h₂
  simp_rw [he] at h₁
  rw [h₂] at h₁
  exact h₁.symm

/-- A finite prime computation and an elementary bound for the remaining tail. -/
theorem integerPrimeSquareTail_le_truncation {Y K : ℕ} (h : Y ≤ K) (hK : 0 < K) :
    integerPrimeSquareTail Y ≤ (∑ p ∈ range (K+1), integerPrimeSquareTerm Y p) + 1/(K:ℝ) := by
  rw [integerPrimeSquareTail_split h]
  exact add_le_add le_rfl (integerPrimeSquareTail_le_reciprocal hK)

end GRHArticle.ProgressionFree

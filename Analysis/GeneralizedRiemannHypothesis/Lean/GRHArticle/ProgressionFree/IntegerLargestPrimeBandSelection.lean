import GRHArticle.ProgressionFree.IntegerLargestPrimePastingDensity

/-!
# Choosing largest-prime bands for countably many rules

Choose each lower endpoint after its rule is approximately independent of
every sufficiently large smoothness cutoff. Subtracting the estimates at
the two endpoints gives a summable error throughout each band.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology

private theorem densityUpTo_sdiff {A B : Set ℕ} (h : A ⊆ B) (N : ℕ) :
    densityUpTo (B \ A) N = densityUpTo B N - densityUpTo A N := by
  classical
  let slice (C : Set ℕ) := (Icc 1 N).filter (· ∈ C)
  have hsub : slice A ⊆ slice B := fun _ hn ↦
    mem_filter.mpr ⟨(mem_filter.mp hn).1,h (mem_filter.mp hn).2⟩
  have heq : slice (B \ A) = slice B \ slice A := by
    apply Finset.ext
    intro n
    rw [Finset.mem_sdiff]
    simp only [slice, mem_filter, Set.mem_sdiff]
    tauto
  change ((slice (B \ A)).card : ℝ) / N = ((slice B).card : ℝ) / N - ((slice A).card : ℝ) / N
  rw [heq, card_sdiff_of_subset hsub, Nat.cast_sub (card_le_card hsub), sub_div]

private theorem band_difference {M : ℕ → ℕ} (hM : Monotone M) (h0 : 1 ≤ M 0)
    (E : Set ℕ) (j N : ℕ) :
    densityUpTo (E ∩ integerLargestPrimeBand M j) N =
      densityUpTo (E ∩ Nat.smoothNumbers (M (j+1)+1)) N -
        densityUpTo (E ∩ Nat.smoothNumbers (M j+1)) N := by
  let lo := Nat.smoothNumbers (M j+1)
  let hi := Nat.smoothNumbers (M (j+1)+1)
  have h (n : ℕ) (hn : n ∈ Icc 1 N) :
      n ∈ E ∩ integerLargestPrimeBand M j ↔ n ∈ (E ∩ hi) \ (E ∩ lo) := by
    have hp := Nat.ne_of_gt (mem_Icc.mp hn).1
    have hlo := integerLargestPrimeFactor_le_iff_smooth hp (h0.trans (hM (Nat.zero_le j)))
    have hhi := integerLargestPrimeFactor_le_iff_smooth hp (h0.trans (hM (Nat.zero_le (j+1))))
    change (_ ∧ M j < integerLargestPrimeFactor n ∧ _) ↔ (_ ∧ n ∈ hi) ∧ ¬ (_ ∧ n ∈ lo)
    dsimp only [hi,lo]
    rw [← hlo, ← hhi, lt_iff_not_ge]
    tauto
  have he : densityUpTo (E ∩ integerLargestPrimeBand M j) N =
      densityUpTo ((E ∩ hi) \ (E ∩ lo)) N := le_antisymm
    (densityUpTo_le_of_subset_on_cutoff N (fun n hn ↦ (h n hn).mp))
    (densityUpTo_le_of_subset_on_cutoff N (fun n hn ↦ (h n hn).mpr))
  rw [he]
  apply densityUpTo_sdiff
  exact Set.inter_subset_inter_right E (Nat.smoothNumbers_mono (Nat.succ_le_succ (hM (Nat.le_succ j))))

/-- A countable family of rules, each asymptotically independent of large
smoothness cutoffs, can be pasted along largest-prime bands to realize the
limiting density. The lower endpoints can dominate prescribed cutoffs. -/
theorem exists_integerLargestPrimeBands_of_smooth_independence
    (Y : ℕ → ℕ) (E : ℕ → Set ℕ) {e : ℕ → ℝ} {b : ℝ} (he : Tendsto e atTop (𝓝 b))
    (h : ∀ j, ∀ ε : ℝ, 0 < ε → ∃ K, ∀ N Z : ℕ, K ≤ N → K ≤ Z →
      |densityUpTo (E j ∩ Nat.smoothNumbers (Z+1)) N -
        e j * densityUpTo (Nat.smoothNumbers (Z+1)) N| ≤ ε) :
    ∃ M : ℕ → ℕ, StrictMono M ∧ 1 ≤ M 0 ∧ (∀ j, Y j ≤ M j) ∧
      HasNaturalDensity (integerLargestPrimeBandPaste M E) b := by
  let ε (j : ℕ) := (1/2 : ℝ)^j
  choose K hK using fun j ↦ h j (ε j) (by dsimp [ε]; positivity)
  let M (j : ℕ) := j+1 + ∑ i ∈ range (j+1), (K i + Y i)
  have hm (j : ℕ) : M j = j+1 + ((∑ i ∈ range j, (K i + Y i)) + (K j + Y j)) := by
    simp only [M,sum_range_succ]
  have hKM (j : ℕ) : K j ≤ M j := by rw [hm]; omega
  have hM : StrictMono M := strictMono_nat_of_lt_succ fun j ↦ by
    change j+1 + _ < j+1+1 + ∑ i ∈ range (j+1+1), (K i + Y i)
    rw [sum_range_succ (f := fun i ↦ K i + Y i) (j+1)]
    omega
  have h0 : 1 ≤ M 0 := by rw [hm]; omega
  refine ⟨M,hM,h0,fun j ↦ by rw [hm]; omega,?_⟩
  apply hasNaturalDensity_integerLargestPrimeBandPaste hM E he
    ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).mul_left 2)
  intro j N
  by_cases hn : M j ≤ N
  · have hl := abs_le.mp (hK j N (M j) ((hKM j).trans hn) (hKM j))
    have hu := abs_le.mp (hK j N (M (j+1)) ((hKM j).trans hn)
      ((hKM j).trans (hM (Nat.lt_succ_self j)).le))
    have hb := band_difference hM.monotone h0 Set.univ j N
    simp only [Set.univ_inter] at hb
    rw [band_difference hM.monotone h0, hb, mul_sub]
    change |_ - _| ≤ 2 * ε j
    exact abs_le.mpr ⟨by linarith [hl.1,hu.1,hl.2,hu.2],by linarith [hl.1,hu.1,hl.2,hu.2]⟩
  · have hz : densityUpTo (integerLargestPrimeBand M j) N = 0 := by
      have hh : densityUpTo (integerLargestPrimeBand M j) N ≤ densityUpTo ∅ N :=
        densityUpTo_le_of_subset_on_cutoff N fun n hin hband ↦ by
          have hle := (integerLargestPrimeFactor_le (mem_Icc.mp hin).1).trans (mem_Icc.mp hin).2
          exact (hn (hband.1.le.trans hle)).elim
      simpa [densityUpTo, countUpTo] using le_antisymm hh (densityUpTo_mono (Set.empty_subset _) N)
    have hz' := le_antisymm ((densityUpTo_mono (Set.inter_subset_right (s := E j)) N).trans_eq hz)
      (densityUpTo_nonneg _ _)
    rw [hz',hz,mul_zero,sub_zero,abs_zero]
    positivity

end GRHArticle.ProgressionFree

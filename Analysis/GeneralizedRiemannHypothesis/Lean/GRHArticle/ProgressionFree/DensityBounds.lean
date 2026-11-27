import GRHArticle.ProgressionFree.Density
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# Uniform bounds on exceptional sets

Multiples of a positive divisor occupy at most the reciprocal of the divisor
at every positive-integer cutoff. Finite union bounds and telescoping control
the error from omitting prime squares above a cutoff.
-/

open scoped BigOperators

namespace GRHArticle.ProgressionFree

theorem densityUpTo_le_of_subset_on_cutoff {s t : Set ℕ} (N : ℕ)
    (h : ∀ n ∈ Finset.Icc 1 N, n ∈ s → n ∈ t) :
    densityUpTo s N ≤ densityUpTo t N := by
  have hcount : countUpTo s N ≤ countUpTo t N := by
    classical
    unfold countUpTo
    apply Finset.card_le_card
    intro n hn
    obtain ⟨hI, hs⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hI, h n hI hs⟩
  unfold densityUpTo
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg N)

theorem densityUpTo_mono {s t : Set ℕ} (hst : s ⊆ t) (N : ℕ) :
    densityUpTo s N ≤ densityUpTo t N :=
  densityUpTo_le_of_subset_on_cutoff N fun _ _ hn => hst hn

theorem densityUpTo_union_le (s t : Set ℕ) (N : ℕ) :
    densityUpTo (s ∪ t) N ≤ densityUpTo s N + densityUpTo t N := by
  have hcount : countUpTo (s ∪ t) N ≤ countUpTo s N + countUpTo t N := by
    classical
    unfold countUpTo
    refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
    intro n hn
    simp only [Finset.mem_filter, Set.mem_union, Finset.mem_union] at hn ⊢
    tauto
  unfold densityUpTo
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hcount) (Nat.cast_nonneg N)

theorem densityUpTo_abs_sub_le_of_symmDiff_subset {s t E : Set ℕ} (N : ℕ)
    (hE : (s \ t) ∪ (t \ s) ⊆ E) :
    |densityUpTo s N - densityUpTo t N| ≤ densityUpTo E N := by
  have hst : s ⊆ t ∪ E := by
    intro n hn
    by_cases ht : n ∈ t
    · exact Or.inl ht
    · exact Or.inr (hE (Or.inl ⟨hn, ht⟩))
  have hts : t ⊆ s ∪ E := by
    intro n hn
    by_cases hs : n ∈ s
    · exact Or.inl hs
    · exact Or.inr (hE (Or.inr ⟨hn, hs⟩))
  have hs := (densityUpTo_mono hst N).trans (densityUpTo_union_le t E N)
  have ht := (densityUpTo_mono hts N).trans (densityUpTo_union_le s E N)
  exact abs_le.mpr ⟨by linarith only [ht], by linarith only [hs]⟩

theorem densityUpTo_finiteUnion_le {ι : Type*} (T : Finset ι) (A : ι → Set ℕ) (N : ℕ) :
    densityUpTo {n | ∃ i ∈ T, n ∈ A i} N ≤ ∑ i ∈ T, densityUpTo (A i) N := by
  classical
  have hcount : countUpTo {n | ∃ i ∈ T, n ∈ A i} N ≤ ∑ i ∈ T, countUpTo (A i) N := by
    let B (i : ι) := (Finset.Icc 1 N).filter (· ∈ A i)
    calc
      _ ≤ (T.biUnion B).card := by
        unfold countUpTo
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Set.mem_setOf_eq] at hn
        obtain ⟨hI, i, hi, ha⟩ := hn
        exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hI, ha⟩⟩
      _ ≤ _ := Finset.card_biUnion_le
  have hcast : (countUpTo {n | ∃ i ∈ T, n ∈ A i} N : ℝ) ≤
      (∑ i ∈ T, countUpTo (A i) N : ℕ) := by exact_mod_cast hcount
  unfold densityUpTo
  calc
    _ ≤ ((∑ i ∈ T, countUpTo (A i) N : ℕ) : ℝ) / (N : ℝ) :=
      div_le_div_of_nonneg_right hcast (Nat.cast_nonneg N)
    _ = _ := by
      simp only [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]

theorem densityUpTo_dvd_le (d N : ℕ) (hd : 0 < d) :
    densityUpTo {n | d ∣ n} N ≤ 1 / (d : ℝ) := by
  unfold densityUpTo
  rw [countUpTo_dvd d N hd]
  by_cases hN : N = 0
  · simp [hN]
  · have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hdr : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
    apply (div_le_div_iff₀ hNr hdr).mpr
    rw [one_mul]
    exact_mod_cast Nat.div_mul_le_self N d

theorem densityUpTo_divisibleByOneOf_le {ι : Type*} (T : Finset ι) (d : ι → ℕ) (N : ℕ)
    (hd : ∀ i ∈ T, 0 < d i) :
    densityUpTo {n | ∃ i ∈ T, d i ∣ n} N ≤ ∑ i ∈ T, 1 / (d i : ℝ) :=
  (densityUpTo_finiteUnion_le T (fun i => {n | d i ∣ n}) N).trans
    (Finset.sum_le_sum fun i hi => densityUpTo_dvd_le _ _ (hd i hi))

theorem sum_Ioc_one_div_sq_le (Y N : ℕ) (hY : 0 < Y) :
    (∑ q ∈ Finset.Ioc Y N, 1 / (q : ℝ) ^ 2) ≤ 1 / (Y : ℝ) := by
  by_cases hYN : Y ≤ N
  · have he : Finset.Ico (Y + 1) (N + 1) = Finset.Ioc Y N := by
      ext q
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
    have hshift := Finset.sum_Ico_add' (fun q : ℕ => 1 / (q : ℝ) ^ 2) Y N 1
    rw [he] at hshift
    rw [← hshift]
    calc
      _ ≤ ∑ q ∈ Finset.Ico Y N, (1 / (q : ℝ) - 1 / ((q + 1 : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq₀ : 0 < (q : ℝ) := Nat.cast_pos.mpr
          (hY.trans_le (Finset.mem_Ico.mp hq).1)
        have hs : 0 < (q : ℝ) + 1 := by linarith only [hq₀]
        simp only [Nat.cast_add, Nat.cast_one]
        calc
          _ ≤ 1 / ((q : ℝ) * ((q : ℝ) + 1)) := by
            apply one_div_le_one_div_of_le (mul_pos hq₀ hs)
            nlinarith only [hs]
          _ = _ := by
            field_simp [hq₀.ne', hs.ne']
            ring
      _ = 1 / (Y : ℝ) - 1 / (N : ℝ) := by
        have htele := Finset.sum_Ico_sub (fun q : ℕ => 1 / (q : ℝ)) hYN
        calc
          _ = -(∑ q ∈ Finset.Ico Y N, (1 / ((q + 1 : ℕ) : ℝ) - 1 / (q : ℝ))) := by
            simp only [← Finset.sum_neg_distrib, neg_sub]
          _ = _ := by rw [htele, neg_sub]
      _ ≤ _ := sub_le_self _ (by positivity)
  · rw [Finset.Ioc_eq_empty_of_le (by omega), Finset.sum_empty]
    positivity

/-- Uniform density bound for integers divisible by the square of a prime
larger than `Y`. The bound applies before taking any limit. -/
theorem densityUpTo_largePrimeSquare_le (Y N : ℕ) (hY : 0 < Y) :
    densityUpTo {n | ∃ p : ℕ, Y < p ∧ p.Prime ∧ p ^ 2 ∣ n} N ≤ 1 / (Y : ℝ) := by
  calc
    _ ≤ densityUpTo {n | ∃ q ∈ Finset.Ioc Y N, q ^ 2 ∣ n} N := by
      apply densityUpTo_le_of_subset_on_cutoff N
      intro n hn ⟨p, hYp, _, hp⟩
      have hpdvd : p ∣ p ^ 2 := ⟨p, by rw [pow_two]⟩
      have hpN : p ≤ N := (Nat.le_of_dvd (Finset.mem_Icc.mp hn).1 (hpdvd.trans hp)).trans
        (Finset.mem_Icc.mp hn).2
      exact ⟨p, Finset.mem_Ioc.mpr ⟨hYp, hpN⟩, hp⟩
    _ ≤ ∑ q ∈ Finset.Ioc Y N, 1 / (q : ℝ) ^ 2 := by
      simpa only [Nat.cast_pow] using
        densityUpTo_divisibleByOneOf_le (Finset.Ioc Y N) (fun q => q ^ 2) N
          (fun q hq => pow_pos (hY.trans (Finset.mem_Ioc.mp hq).1) _)
    _ ≤ _ := sum_Ioc_one_div_sq_le Y N hY


/-- Uniformly approximating counting proportions arbitrarily closely by sets
with natural densities suffices for existence of the original limit. -/
theorem exists_hasNaturalDensity_of_uniform_approximation (s : Set ℕ)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ (t : Set ℕ) (d : ℝ), HasNaturalDensity t d ∧
      ∀ N, |densityUpTo s N - densityUpTo t N| ≤ ε) :
    ∃ d, HasNaturalDensity s d := by
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.mpr ?_)
  intro ε hε
  have hε₄ : 0 < ε / 4 := by positivity
  obtain ⟨t, d, htd, he⟩ := happrox (ε / 4) hε₄
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htd (ε / 4) hε₄
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm₁ := abs_le.mp (he m)
  have hn₁ := abs_le.mp (he n)
  have hm₂ : |densityUpTo t m - d| < ε / 4 := by simpa only [Real.dist_eq] using hN m hm
  have hn₂ : |densityUpTo t n - d| < ε / 4 := by simpa only [Real.dist_eq] using hN n hn
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith only [hm₁.1, hn₁.2, (abs_lt.mp hm₂).1, (abs_lt.mp hn₂).2],
    by linarith only [hm₁.2, hn₁.1, (abs_lt.mp hm₂).2, (abs_lt.mp hn₂).1]⟩

end GRHArticle.ProgressionFree

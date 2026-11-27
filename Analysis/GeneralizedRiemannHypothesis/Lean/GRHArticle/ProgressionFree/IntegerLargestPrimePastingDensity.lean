import GRHArticle.ProgressionFree.IntegerLargestPrimeBands

/-!
# Natural density of a largest-prime pasting

Each fixed finite collection of largest-prime bands has density zero. The
mass of the remaining bands can be evaluated with a summable approximation
error and coefficients tending to the desired density.
-/

namespace GRHArticle.ProgressionFree

open Finset Filter Topology
open scoped BigOperators

private theorem mem_slice {A : Set ℕ} {N n : ℕ} :
    n ∈ integerPrefixSlice A N ↔ n ∈ Icc 1 N ∧ n ∈ A := by
  simp only [integerPrefixSlice, integerPrefix, mem_filter]

private theorem densityUpTo_eq_slice (A : Set ℕ) (N : ℕ) :
    densityUpTo A N = ((integerPrefixSlice A N).card : ℝ) / N := rfl


/-- A set with summable reciprocals has natural density zero. -/
theorem hasNaturalDensity_zero_of_summable_reciprocals {A : Set ℕ}
    (hA : Summable (fun a : A ↦ (1 : ℝ) / (a.val : ℝ))) :
    HasNaturalDensity A 0 := by
  classical
  let f (N n : ℕ) : ℝ := if n ∈ Icc 1 N ∧ n ∈ A then 1 / (N : ℝ) else 0
  have hf (n : ℕ) : Tendsto (fun N ↦ f N n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_atTop_nhds_zero_nat (fun N ↦ ?_) (fun N ↦ ?_)
    · dsimp [f]; split <;> positivity
    · dsimp [f]; split <;> first | rfl | positivity
  have hsum : Summable (A.indicator (fun a : ℕ ↦ (1 : ℝ) / (a : ℝ))) :=
    summable_subtype_iff_indicator.mp hA
  have hfb : ∀ᶠ N in atTop, ∀ n, ‖f N n‖ ≤ A.indicator (fun a ↦ (1 : ℝ) / (a : ℝ)) n :=
    Eventually.of_forall fun N n ↦ by
      by_cases hn : n ∈ Icc 1 N ∧ n ∈ A
      · have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn.1).2
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from (mem_Icc.mp hn.1).1)
        simp only [f, if_pos hn, Set.indicator_of_mem hn.2, Real.norm_eq_abs, abs_of_nonneg
          (show (0 : ℝ) ≤ 1 / N by positivity)]
        exact one_div_le_one_div_of_le hn0 hnN
      · rw [show f N n = 0 by exact if_neg hn, norm_zero]
        exact Set.indicator_nonneg (fun _ _ ↦ by positivity) _
  have ht := tendsto_tsum_of_dominated_convergence hsum hf hfb
  rw [tsum_zero] at ht
  refine ht.congr fun N ↦ ?_
  rw [tsum_eq_sum (s := integerPrefixSlice A N)]
  · symm
    rw [densityUpTo_eq_slice, div_eq_mul_inv, ← nsmul_eq_mul, ← sum_const]
    apply sum_congr rfl
    intro n hn
    simp only [f, if_pos (mem_slice.mp hn), one_div]
  · intro n hn
    have h : ¬ (n ∈ Icc 1 N ∧ n ∈ A) := fun hm ↦ hn (mem_slice.mpr hm)
    exact if_neg h

/-- Every fixed upper cutoff on the largest prime factor gives density zero. -/
theorem hasNaturalDensity_integerLargestPrimeFactor_le_zero (Y : ℕ) :
    HasNaturalDensity {n | integerLargestPrimeFactor n ≤ Y} 0 := by
  by_cases hY : 1 ≤ Y
  · suffices h : densityUpTo {n | integerLargestPrimeFactor n ≤ Y} =
        densityUpTo (Nat.smoothNumbers (Y+1)) by
      unfold HasNaturalDensity
      rw [h]
      exact hasNaturalDensity_zero_of_summable_reciprocals
        (by simpa only [one_div] using summable_reciprocal_smoothNumbers Y)
    funext N
    apply le_antisymm <;> apply densityUpTo_le_of_subset_on_cutoff
    · intro n hn he
      exact (integerLargestPrimeFactor_le_iff_smooth
        (Nat.ne_of_gt (mem_Icc.mp hn).1) hY).mp he
    · intro n hn he
      exact (integerLargestPrimeFactor_le_iff_smooth
        (Nat.ne_of_gt (mem_Icc.mp hn).1) hY).mpr he
  · have h : {n | integerLargestPrimeFactor n ≤ Y} = (∅ : Set ℕ) :=
      Set.eq_empty_iff_forall_notMem.mpr fun n hn ↦ hY ((one_le_integerLargestPrimeFactor n).trans hn)
    rw [h]
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr fun N ↦ ?_
    have hfilter : integerPrefixSlice ∅ N = ∅ := by ext n; simp [mem_slice]
    rw [densityUpTo_eq_slice]
    rw [hfilter]
    simp

private theorem exists_mem_band {M : ℕ → ℕ} (hM : StrictMono M) {n : ℕ}
    (hn : M 0 < integerLargestPrimeFactor n) : ∃ j, n ∈ integerLargestPrimeBand M j := by
  have h : ∃ k, integerLargestPrimeFactor n ≤ M k :=
    ⟨integerLargestPrimeFactor n, hM.le_apply⟩
  let k := Nat.find h
  have hk : integerLargestPrimeFactor n ≤ M k := Nat.find_spec h
  cases he : k with
  | zero => exact (not_le_of_gt hn (he ▸ hk)).elim
  | succ j =>
    refine ⟨j, ?_, he ▸ hk⟩
    apply lt_of_not_ge
    intro hj
    have hj' := Nat.find_min' h hj
    omega

private theorem band_lt_cutoff {M : ℕ → ℕ} (hM : StrictMono M)
    {N j n : ℕ} (hI : n ∈ Icc 1 N) (hn : n ∈ integerLargestPrimeBand M j) : j < N := by
  have hj : j ≤ M j := hM.le_apply
  have hN := (integerLargestPrimeFactor_le (mem_Icc.mp hI).1).trans (mem_Icc.mp hI).2
  exact (hj.trans_lt hn.1).trans_le hN

/-- The finite band decomposition at any cutoff. -/
theorem densityUpTo_integerLargestPrimeBandPaste {M : ℕ → ℕ} (hM : StrictMono M)
    (E : ℕ → Set ℕ) (N : ℕ) :
    densityUpTo (integerLargestPrimeBandPaste M E) N =
      ∑ j ∈ range N, densityUpTo (E j ∩ integerLargestPrimeBand M j) N := by
  classical
  let B j := integerPrefixSlice (E j ∩ integerLargestPrimeBand M j) N
  have hB : integerPrefixSlice (integerLargestPrimeBandPaste M E) N =
      (range N).biUnion B := by
    ext n
    simp only [mem_slice, mem_biUnion, mem_range, B, Set.mem_inter_iff]
    constructor
    · rintro ⟨hn, j, hj, hf⟩
      exact ⟨j, band_lt_cutoff hM hn hf, hn, hj, hf⟩
    · rintro ⟨j, _, hn, hj, hf⟩
      exact ⟨hn, j, hj, hf⟩
  have hd : ((range N : Finset ℕ) : Set ℕ).PairwiseDisjoint B := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun n hi hj ↦ hij ?_
    exact eq_of_mem_integerLargestPrimeBand hM.monotone (mem_slice.mp hi).2.2
      (mem_slice.mp hj).2.2 rfl
  simp only [densityUpTo_eq_slice]
  rw [hB, card_biUnion hd, Nat.cast_sum, sum_div]

private theorem densityUpTo_band_eq_zero {M : ℕ → ℕ} (hM : StrictMono M)
    (E : Set ℕ) {N j : ℕ} (hj : N ≤ j) :
    densityUpTo (E ∩ integerLargestPrimeBand M j) N = 0 := by
  classical
  suffices h : integerPrefixSlice (E ∩ integerLargestPrimeBand M j) N = ∅ by
    rw [densityUpTo_eq_slice, h]
    simp
  refine Finset.eq_empty_iff_forall_notMem.mpr fun n hn ↦ ?_
  exact (not_lt_of_ge hj) (band_lt_cutoff hM (mem_slice.mp hn).1 (mem_slice.mp hn).2.2)

private theorem densityUpTo_upper_bands {M : ℕ → ℕ} (hM : StrictMono M) (N : ℕ) :
    (∑ j ∈ range N, densityUpTo (integerLargestPrimeBand M j) N) =
      densityUpTo {n | M 0 < integerLargestPrimeFactor n} N := by
  have h : integerLargestPrimeBandPaste M (fun _ ↦ Set.univ) =
      {n | M 0 < integerLargestPrimeFactor n} := by
    ext n
    constructor
    · rintro ⟨j, _, hj⟩
      exact (hM.monotone (Nat.zero_le j)).trans_lt hj.1
    · intro hn
      obtain ⟨j, hj⟩ := exists_mem_band hM hn
      exact ⟨j, Set.mem_univ _, hj⟩
  simpa only [h, Set.univ_inter] using
    (densityUpTo_integerLargestPrimeBandPaste hM (fun _ ↦ Set.univ) N).symm

private theorem hasNaturalDensity_upper_bands (Y : ℕ) :
    HasNaturalDensity {n | Y < integerLargestPrimeFactor n} 1 := by
  classical
  have hid : ∀ N : ℕ, 0 < N → densityUpTo {n | Y < integerLargestPrimeFactor n} N =
      1 - densityUpTo {n | integerLargestPrimeFactor n ≤ Y} N := by
    intro N hN
    simp only [densityUpTo_eq_slice]
    let C := integerPrefixSlice {n | Y < integerLargestPrimeFactor n} N
    let L := integerPrefixSlice {n | integerLargestPrimeFactor n ≤ Y} N
    have hu : C ∪ L = Icc 1 N := by
      ext n
      simp only [mem_union, C, L, mem_slice, Set.mem_setOf_eq]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro h
        exact (lt_or_ge Y (integerLargestPrimeFactor n)).imp
          (fun hn ↦ ⟨h, hn⟩) (fun hn ↦ ⟨h, hn⟩)
    have hd : Disjoint C L := Finset.disjoint_left.mpr fun n hC hL ↦ by
      have hc : Y < integerLargestPrimeFactor n := (mem_slice.mp hC).2
      have hl : integerLargestPrimeFactor n ≤ Y := (mem_slice.mp hL).2
      exact (not_le_of_gt hc) hl
    have hc : C.card + L.card = N := by
      rw [← card_union_of_disjoint hd, hu]
      simp [Nat.card_Icc]
    have hc' : (C.card : ℝ) + (L.card : ℝ) = N := by exact_mod_cast hc
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    apply (eq_sub_iff_add_eq).2
    rw [← add_div]
    convert div_self hN' using 1
    exact congrArg (fun t : ℝ ↦ t / N) hc'
  refine (show Tendsto (fun N ↦ 1 - densityUpTo {n | integerLargestPrimeFactor n ≤ Y} N)
        atTop (𝓝 1) by
      simpa using tendsto_const_nhds.sub (hasNaturalDensity_integerLargestPrimeFactor_le_zero Y)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hid N hN).symm

/-- Uniform, summable per-band errors suffice to paste a sequence of densities
converging to `b`. Each individual band has density zero, so an arbitrarily large
error on any fixed finite group of bands has no effect on the limit. -/
theorem hasNaturalDensity_integerLargestPrimeBandPaste {M : ℕ → ℕ} (hM : StrictMono M)
    (E : ℕ → Set ℕ) {b : ℝ} {e err : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝 b)) (hErr : Summable err)
    (happrox : ∀ j N, |densityUpTo (E j ∩ integerLargestPrimeBand M j) N -
      e j * densityUpTo (integerLargestPrimeBand M j) N| ≤ err j) :
    HasNaturalDensity (integerLargestPrimeBandPaste M E) b := by
  classical
  let f (N j : ℕ) := densityUpTo (E j ∩ integerLargestPrimeBand M j) N
  let g (N j : ℕ) := densityUpTo (integerLargestPrimeBand M j) N
  have hfg (N j : ℕ) : 0 ≤ f N j ∧ f N j ≤ g N j ∧ g N j ≤ 1 :=
    ⟨densityUpTo_nonneg _ _, densityUpTo_mono Set.inter_subset_right _,
      densityUpTo_le_one _ _⟩
  have hg (N j : ℕ) : 0 ≤ g N j := densityUpTo_nonneg _ _
  have hlim (j : ℕ) : Tendsto (fun N ↦ g N j) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hasNaturalDensity_integerLargestPrimeFactor_le_zero (M (j+1)))
      (fun N ↦ hg N j) (fun N ↦ densityUpTo_mono (fun _ hn ↦ hn.2) N)
  have hf (j : ℕ) : Tendsto (fun N ↦ f N j) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hlim j) (fun N ↦ (hfg N j).1) (fun N ↦ (hfg N j).2.1)
  have hErr0 (j : ℕ) : 0 ≤ err j := (abs_nonneg _).trans (happrox j 0)
  have hmain : Tendsto (fun N ↦ ∑ j ∈ range N, (f N j - b*g N j)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    let δ := ε / 2
    have hδ : 0 < δ := by positivity
    obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 he δ hδ
    let excess (N j : ℕ) := max (|f N j - b*g N j| - δ*g N j) 0
    let bound (j : ℕ) : ℝ := if j < K then 1 + |b| else 0
    have hbound : Summable bound := summable_of_hasFiniteSupport
      ((Set.finite_Iio K).subset (fun j hj ↦ by
        by_contra hn
        exact hj (if_neg hn)))
    have hten (j : ℕ) : Tendsto (fun N ↦ excess N j) atTop (𝓝 0) := by
      simpa [excess, Real.norm_eq_abs] using
        (((hf j).sub (tendsto_const_nhds.mul (hlim j))).abs.sub
          (tendsto_const_nhds.mul (hlim j))).max
          (tendsto_const_nhds (x := (0 : ℝ)))
    have hbnd (N j : ℕ) : ‖excess N j‖ ≤ err j + bound j := by
      have hnon : 0 ≤ excess N j := le_max_right _ _
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      by_cases hj : j < K
      · rw [show bound j = 1 + |b| by exact if_pos hj]
        have h : |f N j - b*g N j| ≤ 1 + |b| := by
          refine (abs_sub _ _).trans ?_
          rw [abs_of_nonneg (hfg N j).1, abs_mul, abs_of_nonneg (hg N j)]
          exact add_le_add ((hfg N j).2.1.trans (hfg N j).2.2)
            (mul_le_of_le_one_right (abs_nonneg _) (hfg N j).2.2)
        apply max_le _ (by linarith [hErr0 j, abs_nonneg b])
        linarith [mul_nonneg hδ.le (hg N j), hErr0 j]
      · rw [show bound j = 0 by exact if_neg hj, add_zero]
        have hej : |e j-b| ≤ δ := by
          simpa only [Real.dist_eq] using (hK j (le_of_not_gt hj)).le
        apply max_le _ (hErr0 j)
        have hh := abs_sub_le (f N j) (e j*g N j) (b*g N j)
        rw [← sub_mul, abs_mul, abs_of_nonneg (hg N j)] at hh
        linarith [happrox j N, mul_le_mul_of_nonneg_right hej (hg N j)]
    have hexcess := tendsto_tsum_of_dominated_convergence (hErr.add hbound) hten
      (Eventually.of_forall hbnd)
    rw [tsum_zero] at hexcess
    obtain ⟨L, hL⟩ := Metric.tendsto_atTop.1 hexcess δ hδ
    refine ⟨L, fun N hN ↦ ?_⟩
    have heq : ∑' j, excess N j = ∑ j ∈ range N, excess N j := by
      apply tsum_eq_sum
      intro j hj
      have h : N ≤ j := by simpa using hj
      have hg0 : g N j = 0 := by
        simpa only [g, Set.univ_inter] using
          (densityUpTo_band_eq_zero hM Set.univ h)
      have hf0 : f N j = 0 := densityUpTo_band_eq_zero hM (E j) h
      simp [excess, hf0, hg0]
    have hsmall := hL N hN
    rw [Real.dist_eq, sub_zero, heq, abs_of_nonneg (sum_nonneg fun _ _ ↦ le_max_right _ _)] at hsmall
    rw [Real.dist_eq, sub_zero]
    refine (abs_sum_le_sum_abs _ _).trans_lt ?_
    calc
      ∑ j ∈ range N, |f N j - b*g N j| ≤
          ∑ j ∈ range N, (excess N j + δ*g N j) :=
        sum_le_sum fun j _ ↦ (sub_le_iff_le_add.mp (le_max_left _ _))
      _ < ε := by
        rw [sum_add_distrib, ← mul_sum, densityUpTo_upper_bands hM N]
        have hmass := mul_le_of_le_one_right hδ.le
          (densityUpTo_le_one {n | M 0 < integerLargestPrimeFactor n} N)
        exact (add_lt_add_of_lt_of_le hsmall hmass).trans_le (by dsimp [δ]; linarith)
  have hmass := hasNaturalDensity_upper_bands (M 0)
  have ht := hmain.add (tendsto_const_nhds (x := b) |>.mul hmass)
  rw [mul_one, zero_add] at ht
  refine ht.congr fun N ↦ ?_
  rw [sum_sub_distrib, ← mul_sum, densityUpTo_upper_bands hM N, sub_add_cancel]
  exact (densityUpTo_integerLargestPrimeBandPaste hM E N).symm

end GRHArticle.ProgressionFree

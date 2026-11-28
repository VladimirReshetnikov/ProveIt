import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealUpperDensityTail

/-!
# Finite norm-ball approximations to the smooth ideal functionals

Truncating the fixed-template optimization loses at most the omitted
reciprocal mass. Truncating the separately optimized count loses at most
the tail of the full smooth counting series. Both error bounds tend to zero
and can be expressed using finite counts and the finite Euler factor.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- The set of weights attained by admissible subsets of a given domain. -/
def idealAdmissibleWeights (integral : Bool) (B : Set (Ideal (𝓞 K))⁰) : Set ℝ :=
  {w | ∃ A : Set (Ideal (𝓞 K))⁰, A ⊆ B ∧ IdealAdmissible integral A ∧
    w = idealReciprocalWeight (K := K) A}

private theorem idealAdmissibleWeights_nonempty (integral : Bool) (B : Set (Ideal (𝓞 K))⁰) :
    (idealAdmissibleWeights (K := K) integral B).Nonempty := by
  refine ⟨_, ∅, Set.empty_subset _, ?_, rfl⟩
  intro I J L hI
  exact hI.elim

private theorem idealAdmissibleWeights_bddAbove (integral : Bool)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {B : Set (Ideal (𝓞 K))⁰}
    (hB : B ⊆ Set.range (smoothMultiplier S)) : BddAbove (idealAdmissibleWeights (K := K) integral B) := by
  refine ⟨(idealSmoothDensityFactor S)⁻¹, ?_⟩
  rintro w ⟨A,hA,_,rfl⟩
  exact idealReciprocalWeight_le_smoothTotal (K := K) (hA.trans hB)

/-- The fixed-template optimum when every retained ideal has norm at most `H`. -/
noncomputable def idealSmoothBoundedLowerOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ) : ℝ :=
  idealSmoothDensityFactor S * sSup (idealAdmissibleWeights (K := K) integral
    (idealNormCutoff (Set.range (smoothMultiplier S)) H))

/-- The separately optimized sum through the integer norm cutoff `H`. -/
noncomputable def idealSmoothBoundedUpperOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ) : ℝ :=
  idealSmoothDensityFactor S * ∑ k ∈ Icc 1 H,
    (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k

/-- The omitted full smooth counting mass, computed from the finite Euler
factor and the counts through `H`. -/
noncomputable def idealSmoothFullCountTail (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ) : ℝ :=
  (idealSmoothDensityFactor S)⁻¹ - ∑ k ∈ Icc 1 H,
    (countUpTo (Set.range (smoothMultiplier S)) (k : ℝ) : ℝ) * integerPrefixStepWeight k

private theorem idealReciprocalWeight_mono {S : Finset (HeightOneSpectrum (𝓞 K))}
    {A B : Set (Ideal (𝓞 K))⁰} (hAB : A ⊆ B) (hB : B ⊆ Set.range (smoothMultiplier S)) :
    idealReciprocalWeight (K := K) A ≤ idealReciprocalWeight (K := K) B := by
  let incl : A → B := Set.inclusion hAB
  let f (I : A) : ℝ := (absNorm I.val.val : ℝ)⁻¹
  let g (I : B) : ℝ := (absNorm I.val.val : ℝ)⁻¹
  have hf : Summable f := summable_reciprocal_smoothIdealSubset (K := K) (hAB.trans hB)
  have hg : Summable g := summable_reciprocal_smoothIdealSubset (K := K) hB
  change (∑' I, f I) ≤ ∑' I, g I
  exact Summable.tsum_le_tsum_of_inj incl (Set.inclusion_injective hAB)
    (fun I _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) (fun _ ↦ le_rfl) hf hg

private def aboveNorm (A : Set (Ideal (𝓞 K))⁰) (H : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | I ∈ A ∧ H < absNorm I.val}

private theorem idealReciprocalWeight_split {S : Finset (HeightOneSpectrum (𝓞 K))}
    {A : Set (Ideal (𝓞 K))⁰} (hA : A ⊆ Set.range (smoothMultiplier S)) (H : ℕ) :
    idealReciprocalWeight (K := K) A = idealReciprocalWeight (K := K) (idealNormCutoff A H) +
      idealReciprocalWeight (K := K) (aboveNorm (K := K) A H) := by
  classical
  let B := idealNormCutoff A H
  let C := aboveNorm (K := K) A H
  let f (I : (Ideal (𝓞 K))⁰) : ℝ := (absNorm I.val : ℝ)⁻¹
  have hsB : Summable (B.indicator f) :=
    summable_subtype_iff_indicator.mp (summable_reciprocal_smoothIdealSubset (K := K) (S := S)
      (A := B) (fun _ h ↦ hA h.1))
  have hsC : Summable (C.indicator f) :=
    summable_subtype_iff_indicator.mp (summable_reciprocal_smoothIdealSubset (K := K) (S := S)
      (A := C) (fun _ h ↦ hA h.1))
  change (∑' I : A, f I.val) = (∑' I : B, f I.val) + ∑' I : C, f I.val
  rw [_root_.tsum_subtype A f, _root_.tsum_subtype B f, _root_.tsum_subtype C f, ← hsB.tsum_add hsC]
  apply tsum_congr
  intro I
  by_cases hI : I ∈ A <;> by_cases hn : absNorm I.val ≤ H <;>
    simp [B, C, idealNormCutoff, aboveNorm, hI, hn, not_lt_of_ge, lt_of_not_ge]

/-- The finite fixed-template optimum lies below the full optimum and
misses it by at most the omitted reciprocal mass. -/
theorem idealSmoothBoundedLower_bounds (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ) :
    idealSmoothBoundedLowerOptimization integral S H ≤ idealSmoothLowerOptimization integral S ∧
      idealSmoothLowerOptimization integral S ≤ idealSmoothBoundedLowerOptimization integral S H +
        idealSmoothDensityFactor S * idealReciprocalWeight (K := K) (idealSmoothNormTail S H) := by
  let R := Set.range (smoothMultiplier S)
  let F := idealNormCutoff R H
  let W (D : Set (Ideal (𝓞 K))⁰) := idealAdmissibleWeights (K := K) integral D
  let c := idealSmoothDensityFactor S
  have hc : 0 ≤ c := (idealSmoothDensityFactor_pos S).le
  have hF : F ⊆ R := fun _ h ↦ h.1
  have hbR : BddAbove (W R) := idealAdmissibleWeights_bddAbove integral (S := S) le_rfl
  have hbF : BddAbove (W F) := idealAdmissibleWeights_bddAbove integral hF
  refine ⟨?_, ?_⟩
  · change c * sSup (W F) ≤ c * sSup (W R)
    apply mul_le_mul_of_nonneg_left _ hc
    apply csSup_le (idealAdmissibleWeights_nonempty integral F)
    rintro w ⟨A,hA,hAd,rfl⟩
    exact le_csSup hbR ⟨A,hA.trans hF,hAd,rfl⟩
  · change c * sSup (W R) ≤ c * sSup (W F) + c * _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ hc
    apply csSup_le (idealAdmissibleWeights_nonempty integral R)
    rintro w ⟨A,hA,hAd,rfl⟩
    rw [idealReciprocalWeight_split (K := K) hA H]
    have hAF : idealNormCutoff A H ⊆ F := fun _ h ↦ ⟨hA h.1,h.2⟩
    have hAf : IdealAdmissible integral (idealNormCutoff A H) := by
      intro I J L hI hJ hL
      exact hAd hI.1 hJ.1 hL.1
    have hf : idealReciprocalWeight (K := K) (idealNormCutoff A H) ≤ sSup (W F) :=
      le_csSup hbF ⟨_,hAF,hAf,rfl⟩
    have hg : aboveNorm (K := K) A H ⊆ idealSmoothNormTail S H := fun _ h ↦ ⟨hA h.1,h.2⟩
    exact add_le_add hf (idealReciprocalWeight_mono (K := K) hg (fun _ h ↦ h.1))

private theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (h₀ : f 0 = 0) (H : ℕ) :
    ∑ k ∈ Icc 1 H, f k = ∑ k ∈ range (H+1), f k := by
  apply sum_subset
  · intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp hk).2)
  · intro k hk hn
    have h : k = 0 := by
      by_contra h
      exact hn (mem_Icc.mpr ⟨Nat.pos_of_ne_zero h, Nat.le_of_lt_succ (mem_range.mp hk)⟩)
    simpa only [h] using h₀

private theorem tendsto_sum_Icc_one_tsum {f : ℕ → ℝ} (hf : Summable f) (h₀ : f 0 = 0) :
    Tendsto (fun H ↦ ∑ k ∈ Icc 1 H, f k) atTop (𝓝 (∑' k, f k)) := by
  simp_rw [sum_Icc_one_eq_sum_range f h₀]
  exact hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- The finite expression for the remaining full-count mass tends to zero. -/
theorem tendsto_idealSmoothFullCountTail_zero (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (idealSmoothFullCountTail S) atTop (𝓝 0) := by
  let f (k : ℕ) := (countUpTo (Set.range (smoothMultiplier S)) (k : ℝ) : ℝ) * integerPrefixStepWeight k
  have hs := hasSum_countUpTo_stepWeight _ (hasSum_reciprocal_smoothIdeals S).summable
  have hf : Tendsto (fun H ↦ ∑ k ∈ Icc 1 H, f k) atTop (𝓝 ((idealSmoothDensityFactor S)⁻¹)) := by
    rw [← (hasSum_reciprocal_smoothIdeals S).tsum_eq, ← hs.tsum_eq]
    exact tendsto_sum_Icc_one_tsum hs.summable (by simp [f, integerPrefixStepWeight])
  have hconst : Tendsto (fun _ : ℕ ↦ (idealSmoothDensityFactor S)⁻¹) atTop
      (𝓝 ((idealSmoothDensityFactor S)⁻¹)) := tendsto_const_nhds
  change Tendsto (fun H ↦ (idealSmoothDensityFactor S)⁻¹ - ∑ k ∈ Icc 1 H, f k) atTop (𝓝 0)
  simpa only [sub_self] using hconst.sub hf

/-- The separately optimized finite sum has the explicit full-count-tail
error bound. -/
theorem idealSmoothBoundedUpper_bounds (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ) :
    idealSmoothBoundedUpperOptimization integral S H ≤ idealSmoothUpperOptimization integral S ∧
      idealSmoothUpperOptimization integral S ≤ idealSmoothBoundedUpperOptimization integral S H +
        idealSmoothDensityFactor S * idealSmoothFullCountTail S H := by
  classical
  let f (k : ℕ) := (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k
  let g (k : ℕ) := (countUpTo (Set.range (smoothMultiplier S)) (k : ℝ) : ℝ) * integerPrefixStepWeight k
  let T := Icc 1 H
  let c := idealSmoothDensityFactor S
  have hc : 0 ≤ c := (idealSmoothDensityFactor_pos S).le
  have hf : Summable f := summable_idealSmoothPrefixMaximum integral S
  have hsum := hasSum_countUpTo_stepWeight _ (hasSum_reciprocal_smoothIdeals S).summable
  have hg : Summable g := hsum.summable
  have hgt : (∑' k, g k) = c⁻¹ := hsum.tsum_eq.trans (hasSum_reciprocal_smoothIdeals S).tsum_eq
  have hstep (k : ℕ) : 0 ≤ integerPrefixStepWeight k := by unfold integerPrefixStepWeight; positivity
  have hle (k : ℕ) : f k ≤ g k := by
    apply mul_le_mul_of_nonneg_right _ (hstep k)
    exact_mod_cast idealSmoothPrefixMaximum_le integral S k
  refine ⟨?_, ?_⟩
  · apply mul_le_mul_of_nonneg_left _ hc
    exact hf.sum_le_tsum T (fun k _ ↦ mul_nonneg (Nat.cast_nonneg _) (hstep k))
  · have hfT := hf.sum_add_tsum_compl (s := T)
    have hgT := hg.sum_add_tsum_compl (s := T)
    let C := ↥((↑T : Set ℕ)ᶜ)
    have hfC : Summable (fun k : C ↦ f k.val) := hf.comp_injective Subtype.val_injective
    have hgC : Summable (fun k : C ↦ g k.val) := hg.comp_injective Subtype.val_injective
    have hpoint : ∀ k : C, f k.val ≤ g k.val := fun k ↦ hle k.val
    have hcomp : (∑' k : C, f k.val) ≤ ∑' k : C, g k.val := hfC.tsum_le_tsum hpoint hgC
    change c * (∑' k, f k) ≤ c * (∑ k ∈ T, f k) + c * (c⁻¹ - ∑ k ∈ T, g k)
    rw [← mul_add, ← hgt]
    apply mul_le_mul_of_nonneg_left _ hc
    linarith only [hfT, hgT, hcomp]

/-- The reciprocal weight of a finite set is the finite rational-form sum. -/
theorem idealReciprocalWeight_coe_finset (A : Finset (Ideal (𝓞 K))⁰) :
    idealReciprocalWeight (K := K) (A : Set (Ideal (𝓞 K))⁰) =
      ∑ I ∈ A, (absNorm I.val : ℝ)⁻¹ :=
  A.tsum_subtype (fun I : (Ideal (𝓞 K))⁰ ↦ (absNorm I.val : ℝ)⁻¹)

/-- The omitted reciprocal mass equals the inverse Euler factor minus a
finite sum of reciprocal norms. -/
theorem idealSmoothNormTail_weight_eq (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ) :
    idealReciprocalWeight (K := K) (idealSmoothNormTail S H) = (idealSmoothDensityFactor S)⁻¹ -
      ∑ I ∈ (idealNormCutoff_finite (Set.range (smoothMultiplier S)) H).toFinset, (absNorm I.val : ℝ)⁻¹ := by
  let R := Set.range (smoothMultiplier S)
  let F := (idealNormCutoff_finite R H).toFinset
  have h := idealReciprocalWeight_split (K := K) (S := S) (A := R) le_rfl H
  change idealReciprocalWeight (K := K) R = idealReciprocalWeight (K := K) (idealNormCutoff R H) +
    idealReciprocalWeight (K := K) (idealSmoothNormTail S H) at h
  have htotal : idealReciprocalWeight (K := K) R = (idealSmoothDensityFactor S)⁻¹ :=
    (hasSum_reciprocal_smoothIdeals S).tsum_eq
  have hF : idealReciprocalWeight (K := K) (idealNormCutoff R H) = ∑ I ∈ F, (absNorm I.val : ℝ)⁻¹ := by
    rw [← (idealNormCutoff_finite R H).coe_toFinset]
    exact idealReciprocalWeight_coe_finset (K := K) F
  rw [htotal,hF] at h
  linarith only [h]

theorem tendsto_idealSmoothBoundedLower (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (idealSmoothBoundedLowerOptimization integral S) atTop
      (𝓝 (idealSmoothLowerOptimization integral S)) := by
  let B := idealSmoothLowerOptimization integral S
  have h : Tendsto (fun H : ℕ ↦ B - idealSmoothDensityFactor S *
      idealReciprocalWeight (K := K) (idealSmoothNormTail S H)) atTop (𝓝 B) := by
    have hconst : Tendsto (fun _ : ℕ ↦ B) atTop (𝓝 B) := tendsto_const_nhds
    simpa only [mul_zero, sub_zero] using hconst.sub
      ((tendsto_idealSmoothNormTail_weight_zero S).const_mul (idealSmoothDensityFactor S))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds
  · intro H
    linarith only [(idealSmoothBoundedLower_bounds integral S H).2]
  · exact fun H ↦ (idealSmoothBoundedLower_bounds integral S H).1

theorem tendsto_idealSmoothBoundedUpper (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Tendsto (idealSmoothBoundedUpperOptimization integral S) atTop
      (𝓝 (idealSmoothUpperOptimization integral S)) := by
  unfold idealSmoothBoundedUpperOptimization idealSmoothUpperOptimization
  exact (tendsto_sum_Icc_one_tsum (summable_idealSmoothPrefixMaximum integral S)
    (by simp [integerPrefixStepWeight])).const_mul (idealSmoothDensityFactor S)

end GRHArticle.ProgressionFree.NumberFieldIdeals

import GRHArticle.ProgressionFree.NumberFieldIdeals.DensityExtrema
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealUpperDensityPrefix
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealUpperDensityTail

/-!
# Upper bound for the extremal upper density of ideals

For fixed `L`, count the first `L²` rough budgets. The remaining ideals
have either a large smooth factor or absolute norm at most `X/L`.
Both contributions vanish as `L` tends to infinity.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

private theorem countUpTo_union_le (A B : Set (Ideal (𝓞 K))⁰) (X : ℝ) :
    countUpTo (A ∪ B) X ≤ countUpTo A X + countUpTo B X := by
  change (idealRealNormCutoff (A ∪ B) X).ncard ≤ (idealRealNormCutoff A X).ncard + (idealRealNormCutoff B X).ncard
  have he : idealRealNormCutoff (A ∪ B) X = idealRealNormCutoff A X ∪ idealRealNormCutoff B X := by
    ext I
    exact or_and_right
  rw [he]
  exact Set.ncard_union_le _ _

private theorem countUpTo_realCutoff_le (A : Set (Ideal (𝓞 K))⁰) (X Y : ℝ) :
    countUpTo (idealRealNormCutoff A Y) X ≤ countUpTo A Y :=
  Set.ncard_le_ncard (fun _ h ↦ h.1) (idealRealNormCutoff_finite A Y)

private theorem smallRough_smallSmooth_norm_le (S : Finset (HeightOneSpectrum (𝓞 K)))
    (I : (Ideal (𝓞 K))⁰) {X : ℝ} (hX : 0 ≤ X) {L : ℕ} (hL : 0 < L)
    (hr : (absNorm (idealRoughPart S I).val : ℝ) ≤ X/(((L^2 : ℕ) : ℝ)+1))
    (hs : absNorm (idealSmoothPart S I).val ≤ L) : (absNorm I.val : ℝ) ≤ X/(L : ℝ) := by
  have hL' : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hcut : X/((L : ℝ)^2+1) * (L : ℝ) ≤ X/(L : ℝ) := by
    apply (le_div_iff₀ hL').mpr
    rw [mul_assoc]
    calc
      _ ≤ X/((L : ℝ)^2+1) * ((L : ℝ)^2+1) :=
        mul_le_mul_of_nonneg_left (by rw [pow_two]; linarith) (by positivity)
      _ = X := div_mul_cancel₀ X (by positivity)
  have hs' : (absNorm (idealSmoothPart S I).val : ℝ) ≤ (L : ℝ) := Nat.cast_le.mpr hs
  rw [← idealRoughPart_mul_smoothPart S I, Submonoid.coe_mul, map_mul, Nat.cast_mul]
  apply le_trans _ hcut
  exact mul_le_mul (by simpa only [Nat.cast_pow] using hr) hs' (Nat.cast_nonneg _) (by positivity)

/-- At every nonnegative real cutoff, upper counting splits into a finite
rough-budget sum, the large-smooth density, and a dilated full norm ball. -/
private theorem densityUpTo_le_budgetSum_add_tail (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {A : Set (Ideal (𝓞 K))⁰}
    (hA : IdealAdmissible integral A) {X : ℝ} (hX : 0 ≤ X) {L : ℕ} (hL : 0 < L) :
    densityUpTo A X ≤ (∑ k ∈ Icc 1 (L^2),
      ((idealRoughBudgetBand (roughIdeals S) X k).ncard : ℝ) /
        countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X * idealSmoothPrefixMaximum integral S k) +
      densityUpTo (idealLargeSmoothPart S L) X +
      (countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X/(L : ℝ)) : ℝ) /
        countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X := by
  let M := L^2
  let B := idealLargeRoughPart S A X M
  let T := idealLargeSmoothPart S L
  let H := idealRealNormCutoff (Set.univ : Set (Ideal (𝓞 K))⁰) (X/(L : ℝ))
  have hsub : A ⊆ B ∪ (T ∪ H) := by
    intro I hI
    by_cases hr : X/((M : ℝ)+1) < (absNorm (idealRoughPart S I).val : ℝ)
    · exact Or.inl ⟨hI,hr⟩
    · by_cases hs : L < absNorm (idealSmoothPart S I).val
      · exact Or.inr (Or.inl hs)
      · exact Or.inr (Or.inr ⟨Set.mem_univ _, smallRough_smallSmooth_norm_le S I hX hL
          (le_of_not_gt hr) (le_of_not_gt hs)⟩)
  have hc := (countUpTo_mono hsub le_rfl hX).trans ((countUpTo_union_le B (T ∪ H) X).trans
    (add_le_add le_rfl (countUpTo_union_le T H X)))
  have hB := countUpTo_idealLargeRoughPart_le integral S hA X M
  have hH := countUpTo_realCutoff_le (Set.univ : Set (Ideal (𝓞 K))⁰) X (X/(L : ℝ))
  have hcombined := hc.trans (add_le_add hB (add_le_add le_rfl hH))
  calc
    _ ≤ (((∑ k ∈ Icc 1 M, (idealRoughBudgetBand (roughIdeals S) X k).ncard *
          idealSmoothPrefixMaximum integral S k : ℕ) : ℝ) +
        ((countUpTo T X : ℝ) + countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) (X/(L : ℝ)))) /
          countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast hcombined
    _ = _ := by
      simp only [Nat.cast_sum, Nat.cast_mul, add_div, sum_div, div_mul_eq_mul_div, M, T, densityUpTo,
        add_assoc]

private theorem idealUpperDensity_le_budgetSum_add_tail (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {A : Set (Ideal (𝓞 K))⁰}
    (hA : IdealAdmissible integral A) {L : ℕ} (hL : 0 < L) :
    idealUpperDensity A ≤ idealSmoothUpperOptimization integral S +
      idealSmoothDensityFactor S * idealReciprocalWeight (K := K) (idealSmoothNormTail S L) + (L : ℝ)⁻¹ := by
  let d := idealSmoothDensityFactor S * (∑ k ∈ Icc 1 (L^2),
      (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k) +
      idealSmoothDensityFactor S * idealReciprocalWeight (K := K) (idealSmoothNormTail S L) + 1/(L : ℝ)
  have hf := ((tendsto_idealSmoothBudgetSum integral S (L^2)).add
    (hasNaturalDensity_idealLargeSmoothPart S L)).add
    (tendsto_countUpTo_univ_scaled_ratio (K := K) (Nat.cast_pos.mpr hL))
  have hle : idealUpperDensity A ≤ d := by
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    apply limsup_le_of_le
      (isBoundedUnder_of_eventually_ge ((eventually_ge_atTop 0).mono
        fun _ h ↦ (densityUpTo_mem_unitInterval A h).1)).isCoboundedUnder_le
    filter_upwards [eventually_ge_atTop 0, hf.eventually_lt_const (lt_add_of_pos_right d hε)] with X hX hnear
    exact (densityUpTo_le_budgetSum_add_tail integral S hA hX hL).trans hnear.le
  apply hle.trans
  unfold d
  rw [one_div]
  apply add_le_add (add_le_add ?_ le_rfl) le_rfl
  apply mul_le_mul_of_nonneg_left _ (idealSmoothDensityFactor_pos S).le
  exact (summable_idealSmoothPrefixMaximum integral S).sum_le_tsum _ (fun k _ ↦ by
    unfold integerPrefixStepWeight
    positivity)

/-- Every admissible set has upper density at most the normalized smooth
upper optimization, for any finite designated prime set. -/
theorem idealUpperDensity_le_idealSmoothUpperOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {A : Set (Ideal (𝓞 K))⁰}
    (hA : IdealAdmissible integral A) : idealUpperDensity A ≤ idealSmoothUpperOptimization integral S := by
  have hf := ((tendsto_idealSmoothNormTail_weight_zero S).const_mul (idealSmoothDensityFactor S)).const_add
    (idealSmoothUpperOptimization integral S)
  have hv : Tendsto (fun L : ℕ ↦ (L : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := hf.add hv
  simp only [mul_zero, add_zero] at h
  apply ge_of_tendsto h
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with L hL
  exact idealUpperDensity_le_budgetSum_add_tail integral S hA hL

/-- The separately optimized smooth count supplies the universal upper
bound on admissible upper natural density. -/
theorem idealUpperDensitySupremum_le_idealSmoothUpperOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealUpperDensitySupremum K integral ≤ idealSmoothUpperOptimization integral S := by
  apply csSup_le
  · refine ⟨_, ∅, ?_, rfl⟩
    intro I J L hI
    exact hI.elim
  · rintro d ⟨A,hA,rfl⟩
    exact idealUpperDensity_le_idealSmoothUpperOptimization integral S hA

end GRHArticle.ProgressionFree.NumberFieldIdeals

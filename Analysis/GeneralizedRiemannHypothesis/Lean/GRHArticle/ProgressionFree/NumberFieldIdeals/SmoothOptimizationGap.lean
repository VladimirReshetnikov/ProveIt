import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealPrefixObstruction
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothOptimization

/-!
# The smooth-ideal gap from incompatible cutoff optima

A deficit of at least one at a cutoff no larger than `Norm(p)^8` contributes
at least the weight of the interval starting at that final cutoff.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped BigOperators nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

private theorem stepWeight_mono {k M : ℕ} (hk : 0 < k) (h : k ≤ M) :
    integerPrefixStepWeight M ≤ integerPrefixStepWeight k := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast hk
  have h' : (k : ℝ) ≤ (M : ℝ) := by exact_mod_cast h
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

/-- Every fixed admissible smooth set loses at least one whole cutoff step
against separately optimizing all the smooth norm cutoffs. -/
theorem idealSmoothWeight_deficit (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S)
    {D : Set (Ideal (𝓞 K))⁰} (hD : D ⊆ Set.range (smoothMultiplier S))
    (hvalid : IdealAdmissible integral D) :
    integerPrefixStepWeight (absNorm p.val.asIdeal ^ 8) ≤
      (∑' k, (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k) -
        idealReciprocalWeight (K := K) D := by
  let f (k : ℕ) := (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k
  let g (k : ℕ) := (countUpTo D (k : ℝ) : ℝ) * integerPrefixStepWeight k
  have hf : Summable f := summable_idealSmoothPrefixMaximum integral S
  have hg : HasSum g (idealReciprocalWeight (K := K) D) :=
    hasSum_countUpTo_stepWeight D (summable_reciprocal_smoothIdealSubset (K := K) hD)
  have hstep (k : ℕ) : 0 ≤ integerPrefixStepWeight k := by
    unfold integerPrefixStepWeight
    positivity
  have hnonneg (k : ℕ) : 0 ≤ f k - g k := by
    apply sub_nonneg.mpr
    apply mul_le_mul_of_nonneg_right _ (hstep k)
    exact_mod_cast countUpTo_le_idealSmoothPrefixMaximum hD hvalid k
  obtain ⟨k,hk,hkM,E,hE,hEf,hbetter⟩ := exists_better_smooth_cutoff S p integral hD hvalid
  have hcount := hbetter.trans_le (countUpTo_le_idealSmoothPrefixMaximum hE hEf k)
  have hone : (countUpTo D (k : ℝ) : ℝ) + 1 ≤ (idealSmoothPrefixMaximum integral S k : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hcount
  have hloss : integerPrefixStepWeight k ≤ f k - g k := by
    change _ ≤ (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k -
      (countUpTo D (k : ℝ) : ℝ) * integerPrefixStepWeight k
    rw [← sub_mul]
    exact le_mul_of_one_le_left (hstep k) (by linarith only [hone])
  calc
    _ ≤ integerPrefixStepWeight k := stepWeight_mono hk hkM
    _ ≤ f k - g k := hloss
    _ ≤ ∑' j, (f j - g j) := by
      simpa only [Finset.sum_singleton] using (hf.sub hg.summable).sum_le_tsum {k} (fun j _ ↦ hnonneg j)
    _ = _ := by rw [hf.tsum_sub hg.summable, hg.tsum_eq]

/-- The stated `c_S / (M * (M+1))` gap between the two normalized
optimizations, for either ideal-ratio convention. -/
theorem idealSmoothOptimization_gap (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    idealSmoothDensityFactor S * integerPrefixStepWeight (absNorm p.val.asIdeal ^ 8) ≤
      idealSmoothUpperOptimization integral S - idealSmoothLowerOptimization integral S := by
  let U₀ := ∑' k, (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k
  let W := {w : ℝ | ∃ D : Set (Ideal (𝓞 K))⁰, D ⊆ Set.range (smoothMultiplier S) ∧
    IdealAdmissible integral D ∧ w = idealReciprocalWeight (K := K) D}
  have hW : W.Nonempty := by
    refine ⟨_, ∅, Set.empty_subset _, ?_, rfl⟩
    intro I J L hI
    exact hI.elim
  have hsup : sSup W ≤ U₀ - integerPrefixStepWeight (absNorm p.val.asIdeal ^ 8) := by
    apply csSup_le hW
    rintro w ⟨D,hD,hvalid,rfl⟩
    have h := idealSmoothWeight_deficit integral S p hD hvalid
    dsimp only [U₀]
    linarith only [h]
  have h := mul_le_mul_of_nonneg_left hsup (idealSmoothDensityFactor_pos S).le
  rw [mul_sub] at h
  change _ ≤ idealSmoothDensityFactor S * U₀ - idealSmoothDensityFactor S * sSup W
  linarith only [h]

theorem idealSmoothLowerOptimization_lt_upperOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S) :
    idealSmoothLowerOptimization integral S < idealSmoothUpperOptimization integral S := by
  apply sub_pos.mp
  apply lt_of_lt_of_le _ (idealSmoothOptimization_gap integral S p)
  have hM : 0 < absNorm p.val.asIdeal ^ 8 := Nat.pow_pos (zero_lt_one.trans (primeIdeal_norm_gt_one p.val))
  have hM' : 0 < ((absNorm p.val.asIdeal ^ 8 : ℕ) : ℝ) := by exact_mod_cast hM
  refine mul_pos (idealSmoothDensityFactor_pos S) ?_
  unfold integerPrefixStepWeight
  positivity

/-- Transfer the finite loss through any accompanying smooth upper and
sharp squarefree-rough lower bounds. -/
theorem idealDensityGap_of_smoothBounds (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) (p : S)
    {b u v tail : ℝ} (hb : b ≤ idealSmoothLowerOptimization integral S)
    (hu : v * idealSmoothUpperOptimization integral S ≤ u)
    (hv : v ≤ 1) (htail : 1-v ≤ tail) :
    idealSmoothDensityFactor S * integerPrefixStepWeight (absNorm p.val.asIdeal ^ 8) - tail ≤ u-b := by
  have hpenalty : (1-v) * idealSmoothUpperOptimization integral S ≤ tail :=
    (mul_le_mul_of_nonneg_left (idealSmoothUpperOptimization_le_one integral S)
      (sub_nonneg.mpr hv)).trans (by simpa using htail)
  have hgap := idealSmoothOptimization_gap integral S p
  linarith only [hpenalty, hgap, hb, hu]

end GRHArticle.ProgressionFree.NumberFieldIdeals

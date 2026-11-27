import GRHArticle.ProgressionFree.NumberFieldIdeals.NormCutoffWeights
import GRHArticle.ProgressionFree.NumberFieldIdeals.FiniteLocalRules

/-!
# Normalized smooth-ideal optimizations

The lower functional optimizes the reciprocal-norm weight of a single
admissible set. The upper functional optimizes the cardinality of each
norm cutoff separately and sums the resulting step weights.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset
open scoped BigOperators nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- Density of ideals with no prime divisors in the designated finite set. -/
noncomputable def idealSmoothDensityFactor (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  ∏ p ∈ S, (1-primeWeight p)

theorem idealSmoothDensityFactor_pos (S : Finset (HeightOneSpectrum (𝓞 K))) :
    0 < idealSmoothDensityFactor S :=
  Finset.prod_pos fun p _ ↦ sub_pos.mpr (primeWeight_pos_lt_one p).2

/-- Reciprocal-norm weight of a set of nonzero integral ideals. -/
noncomputable def idealReciprocalWeight (A : Set (Ideal (𝓞 K))⁰) : ℝ :=
  ∑' I : A, (absNorm I.val.val : ℝ)⁻¹

theorem hasSum_reciprocal_smoothIdeals (S : Finset (HeightOneSpectrum (𝓞 K))) :
    HasSum (fun I : Set.range (smoothMultiplier S) ↦ (absNorm I.val.val : ℝ)⁻¹)
      (idealSmoothDensityFactor S)⁻¹ := by
  classical
  let f (e : S → ℕ) : Set.range (smoothMultiplier S) := ⟨smoothMultiplier S e,Set.mem_range_self e⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b he
      exact smoothMultiplier_injective S (congrArg Subtype.val he)
    · rintro ⟨I, e, rfl⟩
      exact ⟨e,rfl⟩
  let E := Equiv.ofBijective f hf
  apply E.hasSum_iff.mp
  rw [idealSmoothDensityFactor, ← prod_coe_sort, ← Finset.prod_inv_distrib]
  exact hasSum_smoothMultiplier_invNorm S

theorem summable_reciprocal_smoothIdealSubset {S : Finset (HeightOneSpectrum (𝓞 K))}
    {A : Set (Ideal (𝓞 K))⁰} (hA : A ⊆ Set.range (smoothMultiplier S)) :
    Summable (fun I : A ↦ (absNorm I.val.val : ℝ)⁻¹) := by
  let incl : A → Set.range (smoothMultiplier S) := Set.inclusion hA
  have hinj : Function.Injective incl := Set.inclusion_injective hA
  have hs := (hasSum_reciprocal_smoothIdeals S).summable.comp_injective hinj
  exact hs

theorem idealReciprocalWeight_le_smoothTotal {S : Finset (HeightOneSpectrum (𝓞 K))}
    {A : Set (Ideal (𝓞 K))⁰} (hA : A ⊆ Set.range (smoothMultiplier S)) :
    idealReciprocalWeight (K := K) A ≤ (idealSmoothDensityFactor S)⁻¹ := by
  let B := Set.range (smoothMultiplier S)
  let incl : A → B := Set.inclusion hA
  have hf : Function.Injective incl := Set.inclusion_injective hA
  let f (I : A) : ℝ := (absNorm I.val.val : ℝ)⁻¹
  let g (I : B) : ℝ := (absNorm I.val.val : ℝ)⁻¹
  have hfull : HasSum g (idealSmoothDensityFactor S)⁻¹ := hasSum_reciprocal_smoothIdeals S
  rw [← hfull.tsum_eq]
  change (∑' I : A, f I) ≤ ∑' I : B, g I
  exact Summable.tsum_le_tsum_of_inj incl hf
    (fun I _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)) (fun _ ↦ le_rfl)
    (summable_reciprocal_smoothIdealSubset (K := K) hA) hfull.summable

private noncomputable def smoothIdealBall (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) :
    Finset (Ideal (𝓞 K))⁰ := (idealNormCutoff_finite (Set.range (smoothMultiplier S)) k).toFinset

private noncomputable def smoothIdealCandidates (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) : Finset (Finset (Ideal (𝓞 K))⁰) := by
  classical
  exact (smoothIdealBall S k).powerset.filter (fun F ↦ IdealAdmissible integral (F : Set (Ideal (𝓞 K))⁰))

private theorem mem_smoothIdealCandidates_iff {integral : Bool}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {k : ℕ} {F : Finset (Ideal (𝓞 K))⁰} :
    F ∈ smoothIdealCandidates integral S k ↔
      (F : Set (Ideal (𝓞 K))⁰) ⊆ idealNormCutoff (Set.range (smoothMultiplier S)) k ∧
        IdealAdmissible integral (F : Set (Ideal (𝓞 K))⁰) := by
  classical
  simp only [smoothIdealCandidates, mem_filter, mem_powerset]
  rw [← Finset.coe_subset, smoothIdealBall, Set.Finite.coe_toFinset]

/-- Largest admissible cardinality in one exact integer smooth norm ball. -/
noncomputable def idealSmoothPrefixMaximum (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) : ℕ :=
  (smoothIdealCandidates integral S k).sup Finset.card

theorem idealSmoothPrefixMaximum_le (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) :
    idealSmoothPrefixMaximum integral S k ≤ countUpTo (Set.range (smoothMultiplier S)) (k : ℝ) := by
  rw [countUpTo_nat_eq_ncard, Set.ncard_eq_toFinset_card _ (idealNormCutoff_finite _ k)]
  apply Finset.sup_le
  intro F hF
  apply Finset.card_le_card
  intro I hI
  exact (idealNormCutoff_finite _ k).mem_toFinset.mpr ((mem_smoothIdealCandidates_iff.mp hF).1 hI)

/-- The separately optimal count is attained by an admissible finite set. -/
theorem exists_idealSmoothPrefixOptimizer (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (k : ℕ) :
    ∃ F : Finset (Ideal (𝓞 K))⁰,
      (F : Set (Ideal (𝓞 K))⁰) ⊆ idealNormCutoff (Set.range (smoothMultiplier S)) k ∧
      IdealAdmissible integral (F : Set (Ideal (𝓞 K))⁰) ∧ F.card = idealSmoothPrefixMaximum integral S k := by
  have hn : (smoothIdealCandidates integral S k).Nonempty := by
    refine ⟨∅,mem_smoothIdealCandidates_iff.mpr ⟨by simp, ?_⟩⟩
    intro I J L hI
    exact (Finset.notMem_empty I hI).elim
  obtain ⟨F,hF,he⟩ := Finset.exists_mem_eq_sup _ hn Finset.card
  exact ⟨F,(mem_smoothIdealCandidates_iff.mp hF).1,(mem_smoothIdealCandidates_iff.mp hF).2,he.symm⟩

theorem countUpTo_le_idealSmoothPrefixMaximum {integral : Bool}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {A : Set (Ideal (𝓞 K))⁰}
    (hA : A ⊆ Set.range (smoothMultiplier S)) (ha : IdealAdmissible integral A) (k : ℕ) :
    countUpTo A (k : ℝ) ≤ idealSmoothPrefixMaximum integral S k := by
  rw [countUpTo_nat_eq_ncard, Set.ncard_eq_toFinset_card _ (idealNormCutoff_finite A k)]
  apply Finset.le_sup (f := Finset.card)
  apply mem_smoothIdealCandidates_iff.mpr
  simp only [Set.Finite.coe_toFinset]
  refine ⟨fun _ h ↦ ⟨hA h.1,h.2⟩, ?_⟩
  intro I J L hI hJ hL
  exact ha hI.1 hJ.1 hL.1

/-- The normalized sum of separately maximized cutoff counts. -/
noncomputable def idealSmoothUpperOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  idealSmoothDensityFactor S *
    ∑' k : ℕ, (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k

/-- The normalized supremum of fixed admissible reciprocal-norm weights. -/
noncomputable def idealSmoothLowerOptimization (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) : ℝ :=
  idealSmoothDensityFactor S * sSup
    {w : ℝ | ∃ A : Set (Ideal (𝓞 K))⁰, A ⊆ Set.range (smoothMultiplier S) ∧
      IdealAdmissible integral A ∧ w = idealReciprocalWeight (K := K) A}

theorem summable_idealSmoothPrefixMaximum (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Summable (fun k : ℕ ↦ (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k) := by
  have hs := (hasSum_countUpTo_stepWeight _ (hasSum_reciprocal_smoothIdeals S).summable).summable
  apply Summable.of_nonneg_of_le (fun _ ↦ by unfold integerPrefixStepWeight; positivity) _ hs
  intro k
  apply mul_le_mul_of_nonneg_right _ (by unfold integerPrefixStepWeight; positivity)
  exact_mod_cast idealSmoothPrefixMaximum_le integral S k

theorem idealSmoothUpperOptimization_le_one (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    idealSmoothUpperOptimization integral S ≤ 1 := by
  have hsum := hasSum_reciprocal_smoothIdeals S
  have hs := hasSum_countUpTo_stepWeight _ hsum.summable
  have hle := (summable_idealSmoothPrefixMaximum integral S).tsum_le_tsum (fun k ↦
    mul_le_mul_of_nonneg_right (by exact_mod_cast idealSmoothPrefixMaximum_le integral S k)
      (by unfold integerPrefixStepWeight; positivity : 0 ≤ integerPrefixStepWeight k)) hs.summable
  rw [hs.tsum_eq, hsum.tsum_eq] at hle
  have hp := idealSmoothDensityFactor_pos S
  exact (mul_le_mul_of_nonneg_left hle hp.le).trans_eq (mul_inv_cancel₀ hp.ne')

/-- The lower functional majorizes the normalized weight of every eligible set. -/
theorem idealSmoothDensityFactor_mul_weight_le_lowerOptimization {integral : Bool}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {A : Set (Ideal (𝓞 K))⁰}
    (hA : A ⊆ Set.range (smoothMultiplier S)) (ha : IdealAdmissible integral A) :
    idealSmoothDensityFactor S * idealReciprocalWeight (K := K) A ≤ idealSmoothLowerOptimization integral S := by
  unfold idealSmoothLowerOptimization
  apply mul_le_mul_of_nonneg_left _ (idealSmoothDensityFactor_pos S).le
  refine le_csSup ?_ ?_
  · refine ⟨(idealSmoothDensityFactor S)⁻¹, ?_⟩
    rintro w ⟨B,hB,_,rfl⟩
    exact idealReciprocalWeight_le_smoothTotal (K := K) hB
  · exact ⟨A,hA,ha,rfl⟩

end GRHArticle.ProgressionFree.NumberFieldIdeals

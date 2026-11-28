import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealFiniteOptimizationTables
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealSmoothApproximation
import Mathlib.Data.Rat.BigOperators

/-!
# Correctness of the finite rational ideal evaluator

A finite ideal table is compared to the actual norm ball by an injective
presentation of its ideals and exact tests for the midpoint relation
and divisibility.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals.IdealCutoffTable

open NumberField Ideal IsDedekindDomain Finset
open scoped nonZeroDivisors BigOperators Classical

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (T : IdealCutoffTable ι) (S : Finset (HeightOneSpectrum (𝓞 K))) (H : ℕ)
variable (repr : ι → (Ideal (𝓞 K))⁰)

/-- Exact finite presentation of one smooth ideal norm ball. -/
structure Correct : Prop where
  injective : Function.Injective repr
  range_eq : Set.range repr = idealNormCutoff (Set.range (smoothMultiplier S)) H
  norm_eq (i : ι) : T.norm i = absNorm (repr i).val
  midpoint_iff (a b c : ι) : T.midpoint a b c = true ↔ repr a * repr c = repr b * repr b
  divides_iff (a b : ι) : T.divides a b = true ↔ repr a ∣ repr b

variable {T S H repr}

omit [DecidableEq ι] in
private theorem band_subset (h : T.Correct S H repr) {k : ℕ} {A : Finset ι}
    (hA : A ⊆ T.normBall k) :
    (A.image repr : Set (Ideal (𝓞 K))⁰) ⊆ idealNormCutoff (Set.range (smoothMultiplier S)) k := by
  intro J hJ
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hJ
  have haH : repr a ∈ idealNormCutoff (Set.range (smoothMultiplier S)) H :=
    h.range_eq ▸ Set.mem_range_self a
  exact ⟨haH.1, h.norm_eq a ▸ (T.mem_normBall k a).mp (hA ha)⟩

omit [DecidableEq ι] in
private theorem exists_preimage (h : T.Correct S H repr) {k : ℕ} (hk : k ≤ H)
    {F : Finset (Ideal (𝓞 K))⁰} (hF : (F : Set (Ideal (𝓞 K))⁰) ⊆
      idealNormCutoff (Set.range (smoothMultiplier S)) k) :
    ∃ A : Finset ι, A ⊆ T.normBall k ∧ A.image repr = F := by
  let A := (T.normBall k).filter (fun a ↦ repr a ∈ F)
  refine ⟨A,filter_subset _ _,?_⟩
  ext J
  constructor
  · rintro hJ
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hJ
    exact (mem_filter.mp ha).2
  · intro hJ
    have hJk := hF hJ
    have hJH : J ∈ idealNormCutoff (Set.range (smoothMultiplier S)) H := ⟨hJk.1,hJk.2.trans hk⟩
    have hJr : J ∈ Set.range repr := h.range_eq.symm ▸ hJH
    obtain ⟨a,rfl⟩ := hJr
    exact Finset.mem_image.mpr ⟨a,mem_filter.mpr ⟨(T.mem_normBall k a).mpr (h.norm_eq a ▸ hJk.2), hJ⟩,rfl⟩

omit [Fintype ι] [DecidableEq ι] in
/-- The executable test agrees with admissibility in the number field. -/
theorem admissible_image_iff (h : T.Correct S H repr) (integral : Bool) (A : Finset ι) :
    IdealAdmissible integral (A.image repr : Set (Ideal (𝓞 K))⁰) ↔ T.Admissible integral A := by
  constructor
  · intro ha a hA b hB c hC he hd
    apply h.injective
    exact ha (mem_image_of_mem repr hA) (mem_image_of_mem repr hB) (mem_image_of_mem repr hC)
      ((h.midpoint_iff a b c).mp he) (fun hi ↦ (h.divides_iff a b).mp (hd hi))
  · intro ha I J L hI hJ hL he hd
    obtain ⟨a,ha',rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨b,hb',rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨c,hc',rfl⟩ := Finset.mem_image.mp hL
    exact congrArg repr (ha a ha' b hb' c hc' ((h.midpoint_iff a b c).mpr he)
      (fun hi ↦ (h.divides_iff a b).mpr (hd hi)))

omit [DecidableEq ι] in
private theorem count_image (h : T.Correct S H repr) {k : ℕ} {A : Finset ι}
    (ha : A ⊆ T.normBall k) :
    countUpTo (A.image repr : Set (Ideal (𝓞 K))⁰) (k : ℝ) = A.card := by
  have he : idealNormCutoff (A.image repr : Set (Ideal (𝓞 K))⁰) k = (A.image repr : Set (Ideal (𝓞 K))⁰) := by
    ext I
    exact ⟨fun hI ↦ hI.1,fun hI ↦ ⟨hI,(band_subset h ha hI).2⟩⟩
  rw [countUpTo_nat_eq_ncard, he, Set.ncard_coe_finset, Finset.card_image_of_injective _ h.injective]

/-- The table's separately optimal count is the actual norm-ball maximum. -/
theorem prefixMaximum_eq (h : T.Correct S H repr) (integral : Bool) {k : ℕ} (hk : k ≤ H) :
    T.prefixMaximum integral k = idealSmoothPrefixMaximum integral S k := by
  apply le_antisymm
  · apply Finset.sup_le
    intro A hA
    obtain ⟨hAn,hAf⟩ := (T.mem_candidates integral k A).mp hA
    rw [← count_image h hAn]
    exact countUpTo_le_idealSmoothPrefixMaximum (fun _ hI ↦ (band_subset h hAn hI).1)
      ((admissible_image_iff h integral A).mpr hAf) k
  · obtain ⟨F,hF,hFf,hc⟩ := exists_idealSmoothPrefixOptimizer integral S k
    obtain ⟨A,hAn,he⟩ := exists_preimage h hk hF
    have hAf := (admissible_image_iff h integral A).mp (he.symm ▸ hFf)
    rw [← hc, ← he, Finset.card_image_of_injective _ h.injective]
    exact Finset.le_sup (f := Finset.card) ((T.mem_candidates integral k A).mpr ⟨hAn,hAf⟩)

omit [DecidableEq ι] in
private theorem image_normBall_eq (h : T.Correct S H repr) {k : ℕ} (hk : k ≤ H) :
    (T.normBall k).image repr = (idealNormCutoff_finite (Set.range (smoothMultiplier S)) k).toFinset := by
  ext I
  constructor
  · exact fun hI ↦ (idealNormCutoff_finite _ _).mem_toFinset.mpr (band_subset h le_rfl hI)
  · intro hI
    have hIk := (idealNormCutoff_finite _ _).mem_toFinset.mp hI
    have hIH : I ∈ idealNormCutoff (Set.range (smoothMultiplier S)) H := ⟨hIk.1,hIk.2.trans hk⟩
    have hir : I ∈ Set.range repr := h.range_eq.symm ▸ hIH
    obtain ⟨a,rfl⟩ := hir
    exact Finset.mem_image.mpr ⟨a,(T.mem_normBall k a).mpr (h.norm_eq a ▸ hIk.2),rfl⟩

omit [DecidableEq ι] in
theorem normBall_card_eq (h : T.Correct S H repr) {k : ℕ} (hk : k ≤ H) :
    (T.normBall k).card = countUpTo (Set.range (smoothMultiplier S)) (k : ℝ) := by
  rw [countUpTo_nat_eq_ncard, Set.ncard_eq_toFinset_card _ (idealNormCutoff_finite _ k),
    ← image_normBall_eq h hk, Finset.card_image_of_injective _ h.injective]

omit [Fintype ι] [DecidableEq ι] in
private theorem weight_image (h : T.Correct S H repr) (A : Finset ι) :
    (T.reciprocalWeight A : ℝ) = idealReciprocalWeight (K := K) (A.image repr : Set (Ideal (𝓞 K))⁰) := by
  rw [idealReciprocalWeight_coe_finset, Finset.sum_image (fun _ _ _ _ ha ↦ h.injective ha)]
  simp [reciprocalWeight, h.norm_eq]

/-- The rational optimum reified in the real field is the finite actual
ideal-weight optimum before normalization. -/
theorem lowerWeight_eq (h : T.Correct S H repr) (integral : Bool) :
    (T.lowerWeight integral H : ℝ) = sSup (idealAdmissibleWeights (K := K) integral
      (idealNormCutoff (Set.range (smoothMultiplier S)) H)) := by
  obtain ⟨A,hA,hmax⟩ := Finset.exists_mem_eq_sup' (T.candidates_nonempty integral H) T.reciprocalWeight
  have hA' := (T.mem_candidates integral H A).mp hA
  change T.lowerWeight integral H = T.reciprocalWeight A at hmax
  have hgreatest : IsGreatest (idealAdmissibleWeights (K := K) integral
      (idealNormCutoff (Set.range (smoothMultiplier S)) H)) (T.lowerWeight integral H : ℝ) := by
    refine ⟨?_,?_⟩
    · refine ⟨A.image repr,band_subset h hA'.1,(admissible_image_iff h integral A).mpr hA'.2,?_⟩
      rw [hmax, weight_image h]
    · rintro w ⟨B,hB,hBf,rfl⟩
      let hfin : B.Finite := (idealNormCutoff_finite _ H).subset hB
      let F := hfin.toFinset
      have hFB : (F : Set (Ideal (𝓞 K))⁰) = B := hfin.coe_toFinset
      have hF : (F : Set (Ideal (𝓞 K))⁰) ⊆ idealNormCutoff (Set.range (smoothMultiplier S)) H := hFB.symm ▸ hB
      obtain ⟨D,hDn,he⟩ := exists_preimage h le_rfl hF
      have hDB : (D.image repr : Set (Ideal (𝓞 K))⁰) = B := by rw [he,hFB]
      have hDf := (admissible_image_iff h integral D).mp (hDB.symm ▸ hBf)
      have hd := (T.mem_candidates integral H D).mpr ⟨hDn,hDf⟩
      have hle : T.reciprocalWeight D ≤ T.lowerWeight integral H :=
        Finset.le_sup' T.reciprocalWeight hd
      rw [← hDB, ← weight_image h]
      exact_mod_cast hle
  exact hgreatest.csSup_eq.symm

/-- The finite Euler product can be evaluated on prime norms with their
full multiplicities. -/
theorem roughFactor_eq (S : Finset (HeightOneSpectrum (𝓞 K))) :
    (roughFactor (S.val.map (fun p ↦ absNorm p.asIdeal)) : ℝ) = idealSmoothDensityFactor S := by
  simp only [roughFactor, Multiset.map_map, Function.comp_apply, Finset.prod_map_val, Rat.cast_prod,
    Rat.cast_sub, Rat.cast_one, Rat.cast_inv, Rat.cast_natCast, idealSmoothDensityFactor, primeWeight]

/-- The two executable rational approximants are exactly the finite ideal
optimization values. -/
theorem bounded_eval_eq (h : T.Correct S H repr) (integral : Bool) :
    let primes := S.val.map (fun p ↦ absNorm p.asIdeal)
    (T.boundedLower primes integral H : ℝ) = idealSmoothBoundedLowerOptimization integral S H ∧
      (T.boundedUpper primes integral H : ℝ) = idealSmoothBoundedUpperOptimization integral S H := by
  dsimp only
  constructor
  · simp only [boundedLower, Rat.cast_mul, roughFactor_eq S, lowerWeight_eq h integral,
      idealSmoothBoundedLowerOptimization]
  · simp only [boundedUpper, Rat.cast_mul, roughFactor_eq S, Rat.cast_sum, Rat.cast_natCast,
      idealSmoothBoundedUpperOptimization]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [prefixMaximum_eq h integral (mem_Icc.mp hk).2]
    simp [IdealCutoffTable.stepWeight, integerPrefixStepWeight]

omit [DecidableEq ι] in
/-- Both rational error estimates reify to the stated smooth-tail bounds. -/
theorem error_eval_eq (h : T.Correct S H repr) :
    let primes := S.val.map (fun p ↦ absNorm p.asIdeal)
    (T.lowerError primes H : ℝ) = idealSmoothDensityFactor S *
      idealReciprocalWeight (K := K) (idealSmoothNormTail S H) ∧
      (T.upperError primes H : ℝ) = idealSmoothDensityFactor S * idealSmoothFullCountTail S H := by
  dsimp only
  have hfactor := mul_inv_cancel₀ (idealSmoothDensityFactor_pos S).ne'
  constructor
  · simp only [lowerError, Rat.cast_sub, Rat.cast_one, Rat.cast_mul, roughFactor_eq S]
    rw [weight_image h, image_normBall_eq h le_rfl, idealReciprocalWeight_coe_finset,
      idealSmoothNormTail_weight_eq, mul_sub, hfactor]
  · simp only [upperError, Rat.cast_sub, Rat.cast_one, Rat.cast_mul, roughFactor_eq S, Rat.cast_sum, Rat.cast_natCast,
      idealSmoothFullCountTail, mul_sub, hfactor]
    congr 2
    apply Finset.sum_congr rfl
    intro k hk
    rw [normBall_card_eq h (mem_Icc.mp hk).2]
    simp [IdealCutoffTable.stepWeight, integerPrefixStepWeight]

end GRHArticle.ProgressionFree.NumberFieldIdeals.IdealCutoffTable

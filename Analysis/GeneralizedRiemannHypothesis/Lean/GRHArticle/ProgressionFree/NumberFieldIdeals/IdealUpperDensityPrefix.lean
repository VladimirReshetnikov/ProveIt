import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughBands
import GRHArticle.ProgressionFree.NumberFieldIdeals.IdealRoughParts
import GRHArticle.ProgressionFree.NumberFieldIdeals.SmoothOptimization

/-!
# Upper count over finitely many rough budgets

A cutoff with large rough factor has only finitely many possible smooth
budgets. The actual fiber is admissible, so its count is no greater
than the exact optimizer for its budget.
-/

namespace GRHArticle.ProgressionFree.NumberFieldIdeals

open NumberField Ideal IsDedekindDomain Finset Filter Topology
open scoped nonZeroDivisors BigOperators

variable {K : Type*} [Field K] [NumberField K]

/-- The part of an ideal set with rough factors belonging to the first
`M` positive budgets at cutoff `X`. -/
noncomputable def idealLargeRoughPart (S : Finset (HeightOneSpectrum (𝓞 K)))
    (A : Set (Ideal (𝓞 K))⁰) (X : ℝ) (M : ℕ) : Set (Ideal (𝓞 K))⁰ :=
  {I | I ∈ A ∧ X/((M : ℝ)+1) < (absNorm (idealRoughPart S I).val : ℝ)}

theorem countUpTo_idealLargeRoughPart_le (integral : Bool)
    (S : Finset (HeightOneSpectrum (𝓞 K))) {A : Set (Ideal (𝓞 K))⁰}
    (hA : IdealAdmissible integral A) (X : ℝ) (M : ℕ) :
    countUpTo (idealLargeRoughPart S A X M) X ≤
      ∑ k ∈ Icc 1 M, (idealRoughBudgetBand (roughIdeals S) X k).ncard * idealSmoothPrefixMaximum integral S k := by
  classical
  let B := idealRealNormCutoff (idealLargeRoughPart S A X M) X
  let R (k : ℕ) := (idealRoughBudgetBand_finite (roughIdeals S) X k).toFinset
  let C (k : ℕ) (g : (Ideal (𝓞 K))⁰) := (idealNormCutoff_finite (idealSmoothFiber S A g) k).toFinset
  let D := (Icc 1 M).sigma fun k ↦ (R k).sigma (C k)
  let project (I : (Ideal (𝓞 K))⁰) : Σ _ : ℕ, Σ _ : (Ideal (𝓞 K))⁰, (Ideal (𝓞 K))⁰ :=
    ⟨⌊X / (absNorm (idealRoughPart S I).val : ℝ)⌋₊,idealRoughPart S I,idealSmoothPart S I⟩
  have hcard : B.ncard ≤ D.card := by
    rw [Set.ncard_eq_toFinset_card _ (idealRealNormCutoff_finite _ X)]
    apply Finset.card_le_card_of_injOn project
    · intro I hI
      have hI : I ∈ B := (idealRealNormCutoff_finite _ X).mem_toFinset.mp hI
      let g := idealRoughPart S I
      let J := idealSmoothPart S I
      let x := (absNorm g.val : ℝ)
      let y := (absNorm J.val : ℝ)
      let k := ⌊X/x⌋₊
      have hx : 0 < x := Nat.cast_pos.mpr (absNorm_pos_of_nonZeroDivisors g)
      have hy : 1 ≤ y := by
        change (1 : ℝ) ≤ (absNorm J.val : ℝ)
        exact_mod_cast Nat.succ_le_of_lt (absNorm_pos_of_nonZeroDivisors J)
      have hxy : x*y ≤ X := by
        change (absNorm g.val : ℝ) * (absNorm J.val : ℝ) ≤ X
        rw [← Nat.cast_mul, ← map_mul, ← Submonoid.coe_mul, idealRoughPart_mul_smoothPart]
        exact hI.2
      have hm : X/((M : ℝ)+1) < x := hI.1.2
      have hratio₀ : 1 ≤ X/x := (le_div_iff₀ hx).mpr (by
        rw [one_mul]
        exact (le_mul_of_one_le_right hx.le hy).trans hxy)
      have hratioM : X/x < (M : ℝ)+1 := (div_lt_iff₀ hx).mpr (by
        simpa only [mul_comm] using (div_lt_iff₀ (by positivity : 0 < (M : ℝ)+1)).mp hm)
      have hratioN : 0 ≤ X/x := zero_le_one.trans hratio₀
      have hk₀ : 1 ≤ k := (Nat.le_floor_iff hratioN).mpr (by simpa using hratio₀)
      have hkle : (k : ℝ) ≤ X/x := Nat.floor_le hratioN
      have hkM : k ≤ M := by
        have hk' : k < M+1 := by exact_mod_cast hkle.trans_lt hratioM
        omega
      have hb1 : X/((k : ℝ)+1) < x := (div_lt_iff₀ (by positivity)).mpr (by
        simpa only [mul_comm] using (div_lt_iff₀ hx).mp (Nat.lt_floor_add_one (X/x)))
      have hb2 : x ≤ X/(k : ℝ) := (le_div_iff₀ (by exact_mod_cast hk₀ : 0 < (k : ℝ))).mpr (by
        simpa only [mul_comm] using (le_div_iff₀ hx).mp hkle)
      have hJk : absNorm J.val ≤ k := (Nat.le_floor_iff hratioN).mpr ((le_div_iff₀ hx).mpr (by
        simpa only [mul_comm] using hxy))
      change (⟨k,g,J⟩ : Σ _ : ℕ, Σ _ : (Ideal (𝓞 K))⁰, (Ideal (𝓞 K))⁰) ∈ D
      refine mem_sigma.mpr ⟨mem_Icc.mpr ⟨hk₀,hkM⟩, mem_sigma.mpr ⟨?_,?_⟩⟩
      · exact (idealRoughBudgetBand_finite (roughIdeals S) X k).mem_toFinset.mpr
          ⟨idealRoughPart_mem S I,hb1,hb2⟩
      · exact (idealNormCutoff_finite (idealSmoothFiber S A g) k).mem_toFinset.mpr
          ⟨idealSmoothPart_mem_idealSmoothFiber S hI.1.1,hJk⟩
    · intro I _ J _ h
      have hr := congrArg (fun z : Σ _ : ℕ, Σ _ : (Ideal (𝓞 K))⁰, (Ideal (𝓞 K))⁰ ↦ z.2.1) h
      have hs := congrArg (fun z : Σ _ : ℕ, Σ _ : (Ideal (𝓞 K))⁰, (Ideal (𝓞 K))⁰ ↦ z.2.2) h
      exact (idealRoughPart_mul_smoothPart S I).symm.trans
        ((congrArg₂ (·*·) hr hs).trans (idealRoughPart_mul_smoothPart S J))
  refine hcard.trans ?_
  change ((Icc 1 M).sigma fun k ↦ (R k).sigma (C k)).card ≤ _
  rw [card_sigma]
  apply sum_le_sum
  intro k _
  rw [card_sigma, Set.ncard_eq_toFinset_card _ (idealRoughBudgetBand_finite (roughIdeals S) X k)]
  calc
    _ ≤ ∑ _ ∈ R k, idealSmoothPrefixMaximum integral S k := by
      apply sum_le_sum
      intro g _
      have h := countUpTo_le_idealSmoothPrefixMaximum (idealSmoothFiber_subset_range S A g)
        (idealAdmissible_idealSmoothFiber S hA g) k
      simpa only [countUpTo_nat_eq_ncard, Set.ncard_eq_toFinset_card _ (idealNormCutoff_finite (idealSmoothFiber S A g) k)] using h
    _ = _ := by
      rw [sum_const, nsmul_eq_mul]
      rfl

/-- The limiting contribution of the first `M` rough budgets, normalized by
the entire ideal norm ball. -/
theorem tendsto_idealSmoothBudgetSum (integral : Bool) (S : Finset (HeightOneSpectrum (𝓞 K))) (M : ℕ) :
    Tendsto (fun X : ℝ ↦ ∑ k ∈ Icc 1 M,
      ((idealRoughBudgetBand (roughIdeals S) X k).ncard : ℝ) /
        countUpTo (Set.univ : Set (Ideal (𝓞 K))⁰) X * idealSmoothPrefixMaximum integral S k)
      atTop (𝓝 (idealSmoothDensityFactor S *
        ∑ k ∈ Icc 1 M, (idealSmoothPrefixMaximum integral S k : ℝ) * integerPrefixStepWeight k)) := by
  have hd : HasNaturalDensity (roughIdeals S) (idealSmoothDensityFactor S) :=
    hasNaturalDensity_roughIdeals S
  rw [mul_sum]
  apply tendsto_finsetSum
  intro k hk
  simpa only [mul_assoc, mul_comm (integerPrefixStepWeight k)] using
    (tendsto_idealRoughBudgetBand_ncard_div hd (mem_Icc.mp hk).1).mul_const
      (idealSmoothPrefixMaximum integral S k : ℝ)

end GRHArticle.ProgressionFree.NumberFieldIdeals

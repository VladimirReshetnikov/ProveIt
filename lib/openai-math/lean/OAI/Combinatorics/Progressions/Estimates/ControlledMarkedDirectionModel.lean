import OAI.Combinatorics.Progressions.Fourier.CommonMarkedFrequencyModel

namespace OAI

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_integral_direction_model (t : ℕ)
    (η : L →ₗ[ℚ] ℚ) {K A : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) K)
    (x : Fin t → ℚ) (hA : 1 ≤ A) (hx : ∀ i, RationalHeightLE (x i) A)
    (d₀ k₀ l₀ : ℕ)
    (hann : markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀ ⊓
      (markedShiftSecondIdeal F v w marked t).toSubmodule ≤
        (η.comp (markedShiftEval F v w marked t x)).ker)
    (l : ℕ) (hl : 0 < l) :
    let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
    let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
    ∃ m : ℕ, m ≤ finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ∧
      ∃ q : ℕ, q ≤ d ∧ ∃ u : ℕ, u ≤ q ∧ ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
        B ≤ bchIntegralDenominatorBound (s + 1) *
          markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A ^ (q ^ 3) *
            (l * markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A ^ q) ∧
        ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
          ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
            ∃ ξ : MarkedShiftQuotient F v w marked t →ₗ[ℚ] ℚ,
              M.filtration = markedShiftMultidegree F v w marked hw hv t ∧ D.grid = B ∧
              bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid B ∧
              (∀ i j, RationalHeightLE
                (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j)
                (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A)) ∧
              (∀ i, RationalHeightLE (ξ (D.basis i))
                (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A)) ∧
              (∀ z ∈ markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀,
                ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) z) =
                  η (markedShiftEval F v w marked t x z)) ∧
              (∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n) ∧
              ∀ p : ℝ, (q : ℝ) ≤ p → (B : ℝ) ≤ Real.exp p →
                (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A : ℝ) ≤ Real.exp p →
                  M.ComplexityLE p := by
  classical
  obtain ⟨m, hm, q, hq, u, hu, f, hstructure, hlayers, hdirection, ξ, hξ, hheight⟩ :=
    exists_markedShiftQuotient_bounded_direction_data F b ω hF hω v w marked hw hv hH hc hgen
      t η hη x hA hx d₀ k₀ l₀ hann
  let J := markedQuotientJointHeight s (Fintype.card ι)
    (finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t))
    (finrank ℚ (markedShiftSubalgebra F v w marked t)) m q u H K A
  choose c hc' using hlayers
  have hcJ (α i j) : RationalHeightLE (f.repr ((c α) i).val j) J :=
    (hc' α i j).mono (Nat.le_max_left _ _)
  have hξJ (i) : RationalHeightLE (ξ (f i)) J := (hheight i).mono (Nat.le_max_right _ _)
  let M₀ := markedShiftMultidegree F v w marked hw hv t
  obtain ⟨B, hB, hdiv, hbound, D, M, hMF, hDf, hDB, hcoords, hintegral, hcomplex⟩ :=
    M₀.exists_bounded_integral_model_with_frequency f c hcJ
      (fun i j k => (hstructure i j k).mono (Nat.le_max_left _ _)) ξ hξJ l hl
  refine ⟨m, hm, q, hq, u, hu, B, hB, hdiv, hbound, D, M, ξ,
    hMF, hDB, hcoords, ?_, ?_, hξ, hintegral, hcomplex⟩
  · intro i j
    rw [hDf]
    exact (hdirection i j).mono (Nat.le_max_left _ _)
  · simpa only [hDf] using hξJ

end Erdos3

end

section

namespace Erdos3

open Module

variable {I ι L : Type*} [Fintype I] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.associatedDegree.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (hω : ∀ i, ω i ≤ s) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1)
  {H : ℕ} (hH : 1 ≤ H)
  (hc : ∀ i j k, RationalHeightLE (lieStructureConstants b i j k) H)
  (hgen : ∀ i j, RationalHeightLE (b.repr (v i) j) H)

include hF hω hH hc hgen in
theorem exists_markedShift_direction_model_with_budget (t : ℕ)
    (η : L →ₗ[ℚ] ℚ) {K A : ℕ} (hη : ∀ i, RationalHeightLE (η (b i)) K)
    (x : Fin t → ℚ) (hA : 1 ≤ A) (hx : ∀ i, RationalHeightLE (x i) A)
    (d₀ k₀ l₀ : ℕ)
    (hann : markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀ ⊓
      (markedShiftSecondIdeal F v w marked t).toSubmodule ≤
        (η.comp (markedShiftEval F v w marked t x)).ker)
    (l : ℕ) (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hn : (Fintype.card ι : ℝ) ≤ p) (ht : (t : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p)
    (hAp : (A : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ q : ℕ, q ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t ∧
      ∃ D : RationalFilteredNilmanifold (MarkedShiftQuotient F v w marked t) (s + 1) q,
        ∃ M : D.MultidegreeStructure (mixedCorrelationDegree s),
          ∃ ξ : MarkedShiftQuotient F v w marked t →ₗ[ℚ] ℚ,
            M.filtration = markedShiftMultidegree F v w marked hw hv t ∧
            M.ComplexityLE (markedFrequencyModelBudget s p) ∧ l ∣ D.grid ∧
            bchSubgroupCoordinates D.basis D.lattice = scaledIntegerGrid D.grid ∧
            (∀ i j, rationalLogHeight
              (D.basis.repr (markedQuotientDirection F v w marked t (RationalTorus.basis t i)) j) ≤
                markedFrequencyModelBudget s p) ∧
            (∀ i, rationalLogHeight (ξ (D.basis i)) ≤ markedFrequencyModelBudget s p) ∧
            (∀ z ∈ markedShiftPolynomialSubmodule F v w marked t d₀ k₀ l₀,
              ξ (lieQuotientMap (markedShiftSecondIdeal F v w marked t) z) =
                η (markedShiftEval F v w marked t x z)) ∧
            ∀ z : D.filtration.Group, z ∈ D.lattice → ∃ n : ℤ, ξ z.coord = n := by
  let _ := F.associatedDegree.polynomialShift_finiteDimensional b ω hF hω t
  let _ : FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t) :=
    inferInstanceAs (FiniteDimensional ℚ (markedShiftSubalgebra F v w marked t).toSubmodule)
  let a := finrank ℚ (F.associatedDegree.PolynomialShiftAlgebra t)
  let d := finrank ℚ (markedShiftSubalgebra F v w marked t)
  have ha : a ≤ Fintype.card ι * (s + 1) * (t + 1) ^ s + t :=
    F.associatedDegree.polynomialShift_finrank_le b ω hF hω t
  have hd : d ≤ a := (markedShiftSubalgebra F v w marked t).toSubmodule.finrank_le
  have hi : finrank ℚ (markedShiftSecondIdeal F v w marked t).toSubmodule ≤ d :=
    (markedShiftSecondIdeal F v w marked t).toSubmodule.finrank_le
  let R := markedShiftInputBudget s p
  let Q := markedFrequencyHeightBudget s p
  have hpR : p ≤ R := le_markedShiftInputBudget s hp
  have hR : 0 ≤ R := markedShiftInputBudget_nonneg s hp
  have hRQ : R ≤ Q := markedShiftInputBudget_le_frequencyHeight s hp
  have hQS : Q ≤ markedFrequencyModelBudget s p := markedFrequencyHeightBudget_le_model s hp
  have haR : (a : ℝ) ≤ R := (Nat.cast_le.mpr ha).trans
    (markedShift_dimension_budget s (Fintype.card ι) t hp hn ht)
  have hdR : (d : ℝ) ≤ R := (Nat.cast_le.mpr hd).trans haR
  obtain ⟨m, hm, q, hq, u, hu, B, hB, hdiv, hbound, D, M, ξ,
      hMF, hgrid, hcoords, hdirection, hfreq, hpreserve, hintegral, hcomplex⟩ :=
    exists_markedShift_integral_direction_model F b ω hF hω v w marked hw hv hH hc hgen
      t η hη x hA hx d₀ k₀ l₀ hann l hl
  have hmR : (m : ℝ) ≤ R := (Nat.cast_le.mpr (hm.trans hi)).trans hdR
  have hqR : (q : ℝ) ≤ R := (Nat.cast_le.mpr hq).trans hdR
  have huR : (u : ℝ) ≤ R := (Nat.cast_le.mpr hu).trans hqR
  have hheight : (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A : ℝ) ≤ Real.exp Q :=
    markedQuotientJointHeight_le_exp s (Fintype.card ι) a d m q u H K A hR
      (step_le_markedShiftInputBudget s hp) (hn.trans hpR) haR hdR hmR hqR huR
      (hHp.trans (Real.exp_le_exp.mpr hpR)) (hKp.trans (Real.exp_le_exp.mpr hpR))
      (hAp.trans (Real.exp_le_exp.mpr hpR))
  have hgridS : (B : ℝ) ≤ Real.exp (markedFrequencyModelBudget s p) := by
    have hb := integral_frequency_grid_allowance_le_exp (bchIntegralDenominatorBound (s + 1)) q
      (markedQuotientJointHeight s (Fintype.card ι) a d m q u H K A) l
      (hR.trans hRQ) (hqR.trans hRQ) hheight
      (hlp.trans (Real.exp_le_exp.mpr (hpR.trans hRQ)))
    exact (Nat.cast_le.mpr hbound).trans (hb.trans
      (Real.exp_le_exp.mpr (le_add_of_nonneg_left (hR.trans hRQ))))
  refine ⟨q, hq.trans (hd.trans ha), D, M, ξ, hMF,
    hcomplex _ (hqR.trans (hRQ.trans hQS)) hgridS
      (hheight.trans (Real.exp_le_exp.mpr hQS)), ?_, ?_, ?_, ?_, hpreserve, hintegral⟩
  · rw [hgrid]
    exact hdiv
  · simpa only [hgrid] using hcoords
  · exact fun i j => (rationalLogHeight_le_of_height (hdirection i j) hheight).trans hQS
  · exact fun i => (rationalLogHeight_le_of_height (hfreq i) hheight).trans hQS

end Erdos3

end

end OAI

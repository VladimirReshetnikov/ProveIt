import OAI.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget

namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparationCoordinateCap_mono {m s D t T : ℕ}
    (hms : m ≤ s) (htT : t ≤ T) :
    preparationCoordinateCap m D t ≤ preparationCoordinateCap s D T := by
  have hpow : (t + 1) ^ m ≤ (T + 1) ^ s :=
    (Nat.pow_le_pow_left (Nat.add_le_add_right htT 1) m).trans
      (Nat.pow_le_pow_right (by omega) hms)
  have hprod := Nat.mul_le_mul_left D hpow
  unfold preparationCoordinateCap
  omega

variable {m s D nX : ℕ}

theorem preparedRelativeInitializer_padded_coordinate_card_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    ∀ j, Fintype.card (prep.pad (max m s) j).Coord ≤
      preparationCoordinateCap s D (s * D) := by
  apply prep.pad_coordinate_card_le
  intro j
  exact (hcoord j).trans
    (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))

noncomputable abbrev preparedRelativeInitializerVariableCount
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (s M : ℕ) : ℕ :=
  Fintype.card (LayerSamplerVariables
    (EnlargedPreparedCommonKernel (max m s)
      (modularInitialBlockCount (max m s) (nX + max m s * M)))
    (PreparedSamplerContinuous (prep.pad (max m s)))
    (preparedSamplerTransverse (prep.pad (max m s)))
    (EnlargedPreparedCommonSamplerBlock (prep.pad (max m s))
      (modularInitialBlockCount (max m s) (nX + max m s * M))))

theorem preparedRelativeInitializerVariableCount_le
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    {M : ℕ} (hcoord : ∀ j, Fintype.card (prep j).Coord ≤ M) :
    preparedRelativeInitializerVariableCount prep s M ≤
      enlargedPreparedCommonSamplerDimension s M
        (modularInitialBlockCount s (nX + s * M)) := by
  have hdim := (enlargedPreparedCommonSampler_dimensions
    (prep.pad (max m s))
    (modularInitialBlockCount (max m s) (nX + max m s * M))
    (prep.pad_coordinate_card_le hcoord)).1
  calc
    preparedRelativeInitializerVariableCount prep s M ≤
        enlargedPreparedCommonSamplerDimension (max m s) M
          (modularInitialBlockCount (max m s) (nX + max m s * M)) := hdim
    _ = _ := by rw [max_eq_right hms]

theorem preparedRelativeInitializerVariableCount_le_dimension
    (prep : RankPreparationFamily (Fin nX) (Fin D) m) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D)) :
    let M := preparationCoordinateCap s D (s * D)
    preparedRelativeInitializerVariableCount prep s M ≤
      enlargedPreparedCommonSamplerDimension s M
        (modularInitialBlockCount s (nX + s * M)) := by
  apply preparedRelativeInitializerVariableCount_le prep hms
  intro j
  exact (hcoord j).trans
    (preparationCoordinateCap_mono hms (Nat.mul_le_mul_right D hms))

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

private theorem early_input_components {p t c z r B : ℝ} (s : ℕ)
    (hp : 0 ≤ p) (ht : 0 ≤ t) (hc : 0 ≤ c) (hz : 0 ≤ z) (hr : 0 ≤ r)
    (hB : r + 2 * z + ((s : ℝ) + 2) * c + 6 * t + p + s + 60 ≤ B) :
    z ≤ B ∧ r ≤ B ∧ p + 16 + ((s : ℝ) + 1) * c + z ≤ B ∧
      c + 1 ≤ B ∧ 6 * t + 35 ≤ B := by
  have hsc : 0 ≤ (s : ℝ) * c := mul_nonneg (Nat.cast_nonneg s) hc
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  constructor
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]
  · nlinarith only [hp, ht, hc, hz, hr, hs, hsc, hB]

theorem exists_preparedRelative_structural_input_power (s : ℕ) :
    ∃ relativePower : ℕ, 2 ≤ relativePower ∧ ∀ {p : ℝ}, 2 ≤ p →
    ∀ D nX : ℕ, (D : ℝ) ≤ p → (nX : ℝ) ≤ p →
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      let pRelative := (p + 2) ^ relativePower
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative := by
  obtain ⟨C, _, hstruct⟩ := exists_prepared_early_structural_power_budget s s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + 2) ^ C + X + Polynomial.C (s + 3) + 2
  obtain ⟨relativePower, hpower, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨relativePower, hpower, ?_⟩
  intro p hp D nX hD hnX M Jalloc dim pRelative
  have hp0 : 0 ≤ p := by linarith
  have hb : (p + 2) ^ C + p + ((s : ℝ) + 3) + 2 ≤ pRelative := by
    simpa [P, X, Polynomial.eval₂_pow, Nat.cast_add] using hbound p hp0
  have hs := hstruct p hp s D nX le_rfl hD hnX
  simp only [max_self] at hs
  change (M : ℝ) + Jalloc + dim + allocatedUniformChartLog (M : ℝ) ≤ (p + 2) ^ C at hs
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hJ : (0 : ℝ) ≤ Jalloc := Nat.cast_nonneg _
  have hdim : (0 : ℝ) ≤ dim := Nat.cast_nonneg _
  have hchart : 0 ≤ allocatedUniformChartLog (M : ℝ) := by
    unfold allocatedUniformChartLog
    positivity
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hC0 : 0 ≤ (p + 2) ^ C := by positivity
  clear_value pRelative M Jalloc dim
  exact ⟨by linarith only [hb, hC0, hs0], by linarith only [hb, hC0, hp0],
    by linarith only [hb, hs, hJ, hdim, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hdim, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hJ, hchart, hp0, hs0],
    by linarith only [hb, hs, hM, hJ, hdim, hp0, hs0]⟩

theorem exists_preparedRelative_candidate_input_powers
    (s relativePower childExponent normalizationPower regularityPower : ℕ) :
    ∃ basePower precisionPower : ℕ, 2 ≤ basePower ∧ 2 ≤ precisionPower ∧
    ∀ {p vars : ℝ}, 0 ≤ p → 0 ≤ vars → vars ≤ (p + 2) ^ relativePower →
      let pRelative := (p + 2) ^ relativePower
      let childCost := (pRelative + 4) ^ childExponent
      let normBudget := (childCost + vars + 4) ^ normalizationPower
      let Bstruct := (p + 2) ^ basePower
      normBudget ≤ Bstruct ∧ (normBudget + 2) ^ regularityPower ≤ Bstruct ∧
        p + 16 + ((s : ℝ) + 1) * childCost + normBudget ≤ Bstruct ∧
        childCost + 1 ≤ Bstruct ∧ 6 * pRelative + 35 ≤ Bstruct ∧
        3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
  let X : Polynomial ℕ := Polynomial.X
  let t := (X + 2) ^ relativePower
  let c := (t + 4) ^ childExponent
  let z := (c + t + 4) ^ normalizationPower
  let r := (z + 2) ^ regularityPower
  let P := r + 2 * z + (Polynomial.C s + 2) * c + 6 * t + X + Polynomial.C s + 60
  obtain ⟨basePower, hbase, hbound⟩ := exists_natPolynomial_fixed_power_budget P
  obtain ⟨precisionPower, hprecision, herror⟩ :=
    exists_natPolynomial_fixed_power_budget (3 * t + 130)
  refine ⟨basePower, precisionPower, hbase, hprecision, ?_⟩
  intro p vars hp hv hvt pRelative childCost normBudget Bstruct
  let zBound := (childCost + pRelative + 4) ^ normalizationPower
  let rBound := (zBound + 2) ^ regularityPower
  have ht0 : 0 ≤ pRelative := by dsimp only [pRelative]; positivity
  have hc0 : 0 ≤ childCost := by dsimp only [childCost]; positivity
  have hz0 : 0 ≤ zBound := by dsimp only [zBound]; positivity
  have hr0 : 0 ≤ rBound := by dsimp only [rBound]; positivity
  have hn0 : 0 ≤ normBudget := by dsimp only [normBudget]; positivity
  have hn : normBudget ≤ zBound :=
    pow_le_pow_left₀ (by positivity : 0 ≤ childCost + vars + 4)
      (by linarith only [hvt] : childCost + vars + 4 ≤ childCost + pRelative + 4) _
  have hreg : (normBudget + 2) ^ regularityPower ≤ rBound :=
    pow_le_pow_left₀ (by positivity) (add_le_add hn (le_refl (2 : ℝ))) _
  have hb : rBound + 2 * zBound + ((s : ℝ) + 2) * childCost + 6 * pRelative + p + s + 60 ≤ Bstruct := by
    simpa only [P, r, z, c, t, X, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
      Nat.coe_castRingHom, rBound, zBound, childCost, pRelative, Bstruct] using hbound p hp
  have herr : 3 * pRelative + 130 ≤ (p + 2) ^ precisionPower := by
    simpa only [t, X, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_ofNat, pRelative] using herror p hp
  obtain ⟨hz, hr, hm, hc, ht⟩ := early_input_components s hp ht0 hc0 hz0 hr0 hb
  exact ⟨hn.trans hz, hreg.trans hr,
    (add_le_add (le_refl _) hn).trans hm, hc, ht, herr⟩

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial

structure PreparedRelativeInitializerScalarInputs
    {X : Type*} {s D E q : ℕ} (oldPatch : PolynomialPatch X s (D + E))
    (coordinates : Fin q → ℕ) (variableCount : ℕ)
    (p pRelative precisionBudget chartLog a Λ : ℝ) (n₀ d₀ : ℕ) : Prop where
  hpInit : 2 ≤ pRelative
  hDlog : (D : ℝ) ≤ Real.exp pRelative
  hqlog : (q : ℝ) ≤ Real.exp pRelative
  hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp pRelative
  hNlog : ∀ j, (coordinates j : ℝ) ≤ Real.exp pRelative
  hClog : ∀ _j : Fin q, Real.exp chartLog ≤ Real.exp pRelative
  hgainlog : Real.exp (-pRelative) ≤ Real.exp (-p)
  hδearly : Real.exp (-precisionBudget) ≤ Real.exp (-(3 * pRelative + 130))
  hpchild : pRelative + 2 ≤ pRelative + 2
  ha : Real.exp (-pRelative) ≤ a
  habsolute : RelativePatchAbsoluteRule s n₀ pRelative a Λ d₀
  hDim : (variableCount : ℝ) ≤ pRelative + 2
  hOldComplexity : relativePatchComplexity oldPatch ≤ pRelative + 2
  hgain1 : Real.exp (-p) ≤ 1
  hδ : 0 ≤ Real.exp (-precisionBudget)

theorem preparedRelativeInitializer_scalarInputs_of_bounds
    {X : Type*} {s D E q M variableCount n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch X s (D + E)) (coordinates : Fin q → ℕ)
    {p pRelative precisionBudget chartLog a Λ : ℝ}
    (hp : 2 ≤ p) (hpp : p ≤ pRelative)
    (hq : (q : ℝ) ≤ pRelative) (hM : (M : ℝ) ≤ pRelative)
    (hcoordinates : ∀ j, coordinates j ≤ M)
    (hvariableCount : (variableCount : ℝ) ≤ pRelative)
    (hchart : chartLog + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    PreparedRelativeInitializerScalarInputs oldPatch coordinates variableCount
      p pRelative precisionBudget chartLog a Λ n₀ d₀ := by
  have hRexp : pRelative ≤ Real.exp pRelative :=
    (by linarith : pRelative ≤ pRelative + 1).trans (Real.add_one_le_exp pRelative)
  have hD : (D : ℝ) ≤ p := by
    have hrank := (relativePatchComplexity_rank_le oldPatch).trans hcomplexity
    simp only [Nat.cast_add] at hrank
    linarith only [hrank, Nat.cast_nonneg (α := ℝ) E]
  have hkernel := relativePatchComplexity_kernel_bound oldPatch hcomplexity
  have hgain : Real.exp (-pRelative) ≤ Real.exp (-p) :=
    Real.exp_le_exp.mpr (neg_le_neg hpp)
  refine ⟨hp.trans hpp, (hD.trans hpp).trans hRexp, hq.trans hRexp,
    ?_, ?_, ?_, hgain, Real.exp_le_exp.mpr (neg_le_neg hprecision), le_rfl,
    hgain.trans ha, habsolute.mono hpp, ?_, ?_, ?_, (Real.exp_pos _).le⟩
  · exact (by linarith only [hkernel] : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p).trans
      (Real.exp_le_exp.mpr hpp)
  · intro j
    exact ((Nat.cast_le.mpr (hcoordinates j)).trans hM).trans hRexp
  · intro _
    exact Real.exp_le_exp.mpr (by linarith only [hchart])
  · linarith only [hvariableCount]
  · exact hcomplexity.trans (by linarith only [hpp])
  · exact Real.exp_le_one_iff.mpr (by linarith only [hp])

theorem preparedRelativeInitializer_scalarInputs
    {nX s D E m n₀ d₀ : ℕ}
    (oldPatch : PolynomialPatch (Fin nX) s (D + E))
    (prep : RankPreparationFamily (Fin nX) (Fin D) m)
    {p pRelative precisionBudget a Λ : ℝ}
    (hp : 2 ≤ p) (hms : m ≤ s)
    (hcoord : ∀ j, Fintype.card (prep j).Coord ≤
      preparationCoordinateCap m D (m * D))
    (hstructure :
      let M := preparationCoordinateCap s D (s * D)
      let Jalloc := modularInitialBlockCount s (nX + s * M)
      let dim := enlargedPreparedCommonSamplerDimension s M Jalloc
      p ≤ pRelative ∧ (s : ℝ) + 3 ≤ pRelative ∧
        (M : ℝ) ≤ pRelative ∧ (Jalloc : ℝ) ≤ pRelative ∧
        (dim : ℝ) ≤ pRelative ∧ allocatedUniformChartLog (M : ℝ) + 1 ≤ pRelative)
    (hprecision : 3 * pRelative + 130 ≤ precisionBudget)
    (hcomplexity : relativePatchComplexity oldPatch ≤ p)
    (ha : Real.exp (-p) ≤ a)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀) :
    let M := preparationCoordinateCap s D (s * D)
    PreparedRelativeInitializerScalarInputs oldPatch
      (fun j => Fintype.card (prep.pad (max m s) j).Coord)
      (preparedRelativeInitializerVariableCount prep s M)
      p pRelative precisionBudget (allocatedUniformChartLog (M : ℝ)) a Λ n₀ d₀ := by
  obtain ⟨hpp, hs, hM, _hJalloc, hdim, hchart⟩ := hstructure
  refine preparedRelativeInitializer_scalarInputs_of_bounds oldPatch _ hp hpp
    ?_ hM (preparedRelativeInitializer_padded_coordinate_card_le prep hms hcoord)
    ?_ hchart hprecision hcomplexity ha habsolute
  · rw [max_eq_right hms]
    linarith only [hs]
  · exact (Nat.cast_le.mpr
      (preparedRelativeInitializerVariableCount_le_dimension prep hms hcoord)).trans hdim

end Erdos3

end

end OAI

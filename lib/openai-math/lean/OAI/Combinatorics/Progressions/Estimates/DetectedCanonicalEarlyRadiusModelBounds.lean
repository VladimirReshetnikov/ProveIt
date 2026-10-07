import OAI.Combinatorics.Progressions.Dynamics.NormalizedTwistNativeApproximationBudget

namespace OAI

section

namespace Erdos3
open scoped BigOperators

noncomputable def allocatedEarlyModelLog (P pSlice : ℝ) (count : ℕ) : ℝ :=
  (pSlice + 1) * (count + 1) + earlyFiberCapLog P + P + 4

theorem IsDenseCommonStrideBox.mono_parameter {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {p q : ℝ} {A : Finset (I → ℤ)}
    (h : IsDenseCommonStrideBox N p A) (hpq : p ≤ q) :
    IsDenseCommonStrideBox N q A := by
  obtain ⟨c, step, H, hstep, hH, hsub, hdense, heq⟩ := h
  refine ⟨c, step, H, hstep, hH, hsub, fun i => ?_, heq⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
    (Nat.cast_nonneg _)).trans (hdense i)

theorem allocatedEarlyDetector_parameters {m : ℕ}
    (a n : Fin m → ℕ) (R V : Fin m → ℝ) (count : ℕ) {P pSlice u : ℝ}
    (hP : 0 ≤ P) (hpSlice : 0 ≤ pSlice) (hu : 0 ≤ u)
    (hm : (m : ℝ) ≤ P) (hcount : (count : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hV : ∀ j, 0 ≤ V j)
    (ha : ∀ j, (a j : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hVP : ∀ j, V j ≤ Real.exp P) :
    let pModel := allocatedEarlyModelLog P pSlice count
    let Ctail := 4 * ∏ j, earlyConstantDensityCap (a j) (n j) (R j) (V j)
    let K := Real.exp (pSlice * count)
    let pDetect := allocatedModelTestLog u pModel
    let α := allocatedModelUnitThreshold u pModel K Ctail
    let aDetect := 2 * u + 4 * pModel + 7
    0 ≤ pModel ∧ pSlice * count ≤ pModel ∧
      0 ≤ Ctail ∧ Ctail ≤ Real.exp pModel ∧ K ≤ Real.exp pModel ∧
      (count : ℝ) ≤ Real.exp pModel ∧
      0 ≤ pDetect ∧ pSlice ≤ pDetect ∧
      0 < α ∧ α ≤ 1 ∧ 0 ≤ aDetect ∧ Real.exp (-aDetect) ≤ α ∧
      count * Real.exp (-pDetect) ≤ α / 8 ∧ Real.exp (-pDetect) ≤ α / 4 := by
  intro pModel Ctail K pDetect α aDetect
  have hcap0 := earlyFiberCapLog_nonneg hP
  have hcnt0 : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  have hp0 : 0 ≤ pModel := by dsimp only [pModel, allocatedEarlyModelLog]; positivity
  have hslice : pSlice * count ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  have hpSliceModel : pSlice ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  have hPModel : P ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  have hcap : earlyFiberCapLog P + 4 ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  have htail0 : 0 ≤ Ctail := by
    apply mul_nonneg (by norm_num)
    exact Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (hV j))
  have htail : Ctail ≤ Real.exp pModel := by
    calc
      _ ≤ Real.exp 4 * Real.exp (earlyFiberCapLog P) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (4 : ℝ)])
          (earlyFiberCap_exp_bound a n R V hP hm hR hV ha hn hA hRP hVP)
          (Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (hV j)))
          (Real.exp_nonneg _)
      _ = Real.exp (earlyFiberCapLog P + 4) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hcap
  have hK : K ≤ Real.exp pModel := Real.exp_le_exp.mpr hslice
  have hcountExp : (count : ℝ) ≤ Real.exp pModel :=
    hcount.trans (hPModel.trans (by linarith [Real.add_one_le_exp pModel]))
  have hthreshold := allocatedModelUnitThreshold_bounds hu hp0 (Real.exp_nonneg _) htail0 hK htail
  have hdetect := allocatedModelTestLog_detection hu hp0 (Real.exp_nonneg _) htail0 hK htail hcountExp
  have hsliceDetect : pSlice ≤ pDetect := by
    dsimp only [pDetect, allocatedModelTestLog]
    linarith
  exact ⟨hp0, hslice, htail0, htail, hK, hcountExp, hdetect.1, hsliceDetect,
    hthreshold.1, hthreshold.2.1, by dsimp only [aDetect]; positivity,
    hthreshold.2.2, hdetect.2.1, hdetect.2.2⟩

theorem exists_allocatedEarlyDetector_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {P pSlice u : ℝ} {count : ℕ},
      0 ≤ P → pSlice ∈ Set.Icc 0 P → u ∈ Set.Icc 0 P → (count : ℝ) ≤ P →
      let pModel := allocatedEarlyModelLog P pSlice count
      pModel ∈ Set.Icc 0 ((P + C) ^ C) ∧
      allocatedModelTestLog u pModel ∈ Set.Icc 0 ((P + C) ^ C) ∧
      (2 * u + 4 * pModel + 7) ∈ Set.Icc 0 ((P + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let M := (X + 1) * (X + 1) + 3 * X ^ 3 + 17 * X ^ 2 + X + 4
  let D := 2 * X + 5 * M + 12
  let A := 2 * X + 4 * M + 7
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (M + D + A)
  refine ⟨C, hC, ?_⟩
  intro P pSlice u count hP hpSlice hu hcount pModel
  have hpSlice0 := hpSlice.1
  have hu0 := hu.1
  let modelBound := (P + 1) * (P + 1) + 3 * P ^ 3 + 17 * P ^ 2 + P + 4
  have hmodel0 : 0 ≤ modelBound := by dsimp only [modelBound]; positivity
  have hmodel : pModel ≤ modelBound := by
    dsimp only [pModel, allocatedEarlyModelLog, earlyFiberCapLog, modelBound]
    calc
      _ ≤ (P + 1) * (P + 1) + (3 * P ^ 3 + 17 * P ^ 2) + P + 4 := by
        gcongr
        exact hpSlice.2
      _ = _ := by ring
  have hp0 : 0 ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog, earlyFiberCapLog]
    positivity
  have hbudget : modelBound + (2 * P + 5 * modelBound + 12) +
      (2 * P + 4 * modelBound + 7) ≤ (P + C) ^ C := by
    simpa [M, D, A, X, modelBound, Polynomial.eval₂_pow] using hbound P hP
  refine ⟨⟨hp0, by linarith⟩, ⟨?_, ?_⟩, ⟨by positivity, ?_⟩⟩
  · unfold allocatedModelTestLog
    positivity
  · unfold allocatedModelTestLog
    linarith [hu.2]
  · linarith [hu.2]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem detectedCanonicalEarlyRadiusModel_bounds
    {Pearly pSlice : ℝ} (count : ℕ)
    (hPearly : 0 ≤ Pearly) (hpSlice : 0 ≤ pSlice)
    (hcount : (count : ℝ) ≤ Pearly) :
    let pModel := allocatedEarlyModelLog Pearly pSlice count
    0 ≤ pModel ∧ pSlice ≤ pModel ∧ Pearly ≤ pModel ∧
      (count : ℝ) ≤ Real.exp pModel := by
  intro pModel
  have hcap := earlyFiberCapLog_nonneg hPearly
  have hcount0 : (0 : ℝ) ≤ count := Nat.cast_nonneg _
  have hproduct := mul_nonneg hpSlice hcount0
  have hslice : pSlice ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  have hearly : Pearly ≤ pModel := by
    dsimp only [pModel, allocatedEarlyModelLog]
    nlinarith
  refine ⟨hPearly.trans hearly, hslice, hearly, ?_⟩
  exact hcount.trans (hearly.trans (by linarith [Real.add_one_le_exp pModel]))

end Erdos3.VectorPolynomial

end

end OAI

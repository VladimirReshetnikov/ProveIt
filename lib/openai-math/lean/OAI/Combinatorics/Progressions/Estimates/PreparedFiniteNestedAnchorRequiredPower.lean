import OAI.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def preparedFiniteScheduleAnchorGoodRequired
    (m : ℕ) (Pmaster Plate E B0 Pgood Pprod : ℝ) : ℝ :=
  max
    (max
      (preparedModularGeneralDetectorResources
        (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).required
      ((max
        (preparedModularGeneralDetectorResources
          (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj E +
        preparedCenteredMarginalExponent m) ^ preparedCenteredMarginalExponent m))
    (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
      ((Pprod + preparedModularGeneralProductivityExponent m) ^
        preparedModularGeneralProductivityExponent m))

theorem preparedFiniteScheduleAnchorGoodRequired_eq
    (m : ℕ) (Pmaster Plate E B0 Pgood Pprod : ℝ) :
    preparedFiniteScheduleAnchorGoodRequired m Pmaster Plate E B0 Pgood Pprod =
      max
        (max
          (preparedModularGeneralDetectorResources
            (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).required
          ((max
            (preparedModularGeneralDetectorResources
              (preparedModularGeneralDetectorConstants m 0) (0 + 1) Pmaster Plate).Pproj E +
            preparedCenteredMarginalExponent m) ^ preparedCenteredMarginalExponent m))
        (max (preparedCenteredShortForecastGoodRequired m B0 Pgood)
          ((Pprod + preparedModularGeneralProductivityExponent m) ^
            preparedModularGeneralProductivityExponent m)) := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedFiniteScheduleAnchorGoodRequired_eq_shortForecast
    (q : ℕ) (Pmaster Plate Econditional Bcert Pgood Pwidth : ℝ) :
    preparedFiniteScheduleAnchorGoodRequired q Pmaster Plate Econditional Bcert Pgood Pwidth =
      preparedShortForecastProductiveRequired q Pmaster Plate Econditional Bcert Pgood Pwidth := rfl

theorem exists_preparedFiniteNestedAnchorRequired_power_budget (q inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {B : ℝ}, 2 ≤ B →
      ∀ (M nX : ℕ) {pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional : ℝ},
      (M : ℝ) ≤ (B + 2) ^ inputPower →
      (nX : ℝ) ≤ (B + 2) ^ inputPower →
      pRadius ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pseed ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      gainLog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Vlog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Econditional ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (B + 2) ^ inputPower →
      let baseB0 := preparedUniformDegreeProductiveCertificateBudget
        M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
      let Pwidth := 4 * (Plate + 8) ^ 2
      let Bcert := preparedForecastGoodCertificateBudget baseB0 B Pwidth gainLog Vlog
      let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent q)
        baseB0 B Pwidth gainLog Vlog
      preparedFiniteScheduleAnchorGoodRequired q Pmaster Plate Econditional Bcert Pgood Pwidth ≤
        (B + 2) ^ outputPower := by
  let envelope : Polynomial ℕ := Polynomial.X + 9 + 8 * (Polynomial.X + 2) ^ inputPower
  obtain ⟨inflatedPower, _, hEnvelope⟩ := exists_natPolynomial_fixed_power_budget envelope
  obtain ⟨outputPower, houtputPower, hRequired⟩ :=
    exists_preparedShortForecastConstructedRequired_power_budget q inflatedPower
  refine ⟨outputPower, houtputPower, ?_⟩
  intro B hB M nX pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional
    hM hnX hRadius hScale hSeed hQw hGain hV hE hMaster hLate hPlate
    baseB0 Pwidth Bcert Pgood
  let inputBound := (B + 2) ^ inputPower
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hInput0 : 0 ≤ inputBound := pow_nonneg (by linarith only [hB0]) _
  have hEnvelopeReal : B + 9 + 8 * inputBound ≤ (B + 2) ^ inflatedPower := by
    simpa [envelope, inputBound, Polynomial.eval₂_pow] using hEnvelope B hB0
  have hInflated : inputBound ≤ (B + 2) ^ inflatedPower :=
    (by linarith only [hB0, hInput0] : inputBound ≤ B + 9 + 8 * inputBound).trans
      hEnvelopeReal
  have hChart : B ≤ (B + 2) ^ inflatedPower :=
    (by linarith only [hInput0] : B ≤ B + 9 + 8 * inputBound).trans hEnvelopeReal
  have hBase0 : 0 ≤ baseB0 := by
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
    have := hRadius.1
    have := hScale.1
    have := hSeed.1
    have := hQw.1
    have := hGain.1
    have := hV.1
    positivity
  have hBase : baseB0 ≤ (B + 2) ^ inflatedPower := by
    apply le_trans _ hEnvelopeReal
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
    change 1 + (M : ℝ) + nX + pRadius + Pscale + Pseed + Qw + (gainLog + 8) + Vlog ≤
      B + 9 + 8 * inputBound
    linarith only [hB0, hM, hnX, hRadius.2, hScale.2, hSeed.2, hQw.2, hGain.2, hV.2]
  exact hRequired B hB Pmaster Plate Econditional baseB0 B gainLog Vlog
    hMaster hLate (hPlate.trans hInflated)
    ⟨hE.1, hE.2.trans hInflated⟩ ⟨hBase0, hBase⟩ ⟨hB0, hChart⟩
    ⟨hGain.1, hGain.2.trans hInflated⟩ ⟨hV.1, hV.2.trans hInflated⟩

theorem exists_preparedFiniteNestedAnchorScalars_power_budget (q inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {B : ℝ}, 2 ≤ B →
      ∀ (M nX : ℕ) {pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional : ℝ},
      (M : ℝ) ≤ (B + 2) ^ inputPower →
      (nX : ℝ) ≤ (B + 2) ^ inputPower →
      pRadius ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pscale ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Pseed ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Qw ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      gainLog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Vlog ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      Econditional ∈ Set.Icc 0 ((B + 2) ^ inputPower) →
      0 ≤ Pmaster → Pmaster ≤ Plate → Plate ≤ (B + 2) ^ inputPower →
      let baseB0 := preparedUniformDegreeProductiveCertificateBudget
        M nX pRadius Pscale Pseed Qw (gainLog + 8) Vlog
      let Pwidth := 4 * (Plate + 8) ^ 2
      let Bcert := preparedForecastGoodCertificateBudget baseB0 B Pwidth gainLog Vlog
      let Pgood := preparedForecastGoodAnalyticBudget (preparedCenteredShortForecastSpatialExponent q)
        baseB0 B Pwidth gainLog Vlog
      baseB0 ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      Pwidth ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      Bcert ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      Pgood ∈ Set.Icc 0 ((B + 2) ^ outputPower) ∧
      preparedFiniteScheduleAnchorGoodRequired q Pmaster Plate Econditional Bcert Pgood Pwidth ≤
        (B + 2) ^ outputPower := by
  obtain ⟨goodPower, _, hGood⟩ :=
    exists_preparedForecastGoodBudgets_bound (preparedCenteredShortForecastSpatialExponent q)
  let U : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let T : Polynomial ℕ := Polynomial.X + 9 + 8 * U + 4 * (U + 8) ^ 2
  let envelope : Polynomial ℕ := T + (T + Polynomial.C goodPower) ^ goodPower
  obtain ⟨scalarPower, hscalarPower, hEnvelope⟩ := exists_natPolynomial_fixed_power_budget envelope
  obtain ⟨anchorPower, _, hAnchor⟩ := exists_preparedFiniteNestedAnchorRequired_power_budget q inputPower
  refine ⟨max scalarPower anchorPower, hscalarPower.trans (le_max_left _ _), ?_⟩
  intro B hB M nX pRadius Pscale Pseed Qw gainLog Vlog Pmaster Plate Econditional
    hM hnX hRadius hScale hSeed hQw hGain hV hE hMaster hLate hPlate
    baseB0 Pwidth Bcert Pgood
  let inputBound := (B + 2) ^ inputPower
  let commonBound := B + 9 + 8 * inputBound + 4 * (inputBound + 8) ^ 2
  have hB0 : 0 ≤ B := (by norm_num : (0 : ℝ) ≤ 2).trans hB
  have hInput0 : 0 ≤ inputBound := pow_nonneg (by linarith only [hB0]) _
  have hSquare0 : 0 ≤ 4 * (inputBound + 8) ^ 2 := by positivity
  have hInputCommon : inputBound ≤ commonBound := by
    dsimp only [commonBound]
    linarith only [hB0, hInput0, hSquare0]
  have hCommon0 : 0 ≤ commonBound := hInput0.trans hInputCommon
  have hChartCommon : B ≤ commonBound := by
    dsimp only [commonBound]
    linarith only [hInput0, hSquare0]
  have hBase0 : 0 ≤ baseB0 := by
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget]
    have := hRadius.1
    have := hScale.1
    have := hSeed.1
    have := hQw.1
    have := hGain.1
    have := hV.1
    positivity
  have hBaseCommon : baseB0 ≤ commonBound := by
    dsimp only [baseB0, preparedUniformDegreeProductiveCertificateBudget, commonBound]
    linarith only [hB0, hSquare0, hM, hnX, hRadius.2, hScale.2, hSeed.2,
      hQw.2, hGain.2, hV.2]
  have hWidth0 : 0 ≤ Pwidth := by dsimp only [Pwidth]; positivity
  have hPlate0 : 0 ≤ Plate := hMaster.trans hLate
  have hWidthCommon : Pwidth ≤ commonBound := by
    have hWidthUpper : Pwidth ≤ 4 * (inputBound + 8) ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by linarith only [hPlate0]) (add_le_add hPlate le_rfl) 2)
        (by norm_num)
    apply hWidthUpper.trans
    dsimp only [commonBound]
    linarith only [hB0, hInput0]
  have hGoodBounds := hGood hCommon0 ⟨hBase0, hBaseCommon⟩ ⟨hB0, hChartCommon⟩
    ⟨hWidth0, hWidthCommon⟩ ⟨hGain.1, hGain.2.trans hInputCommon⟩
    ⟨hV.1, hV.2.trans hInputCommon⟩
  have hEnvelopeReal : commonBound + (commonBound + goodPower) ^ goodPower ≤
      (B + 2) ^ scalarPower := by
    simpa [envelope, T, U, commonBound, inputBound, Polynomial.eval₂_pow] using hEnvelope B hB0
  have hGoodPower0 : 0 ≤ (commonBound + goodPower) ^ goodPower := by positivity
  have hCommonBound : commonBound ≤ (B + 2) ^ scalarPower :=
    (le_add_of_nonneg_right hGoodPower0).trans hEnvelopeReal
  have hGoodPowerBound : (commonBound + goodPower) ^ goodPower ≤ (B + 2) ^ scalarPower :=
    (le_add_of_nonneg_left hCommon0).trans hEnvelopeReal
  have hScalarFinal : (B + 2) ^ scalarPower ≤ (B + 2) ^ max scalarPower anchorPower :=
    pow_le_pow_right₀ (by linarith only [hB]) (le_max_left _ _)
  have hAnchorFinal : (B + 2) ^ anchorPower ≤ (B + 2) ^ max scalarPower anchorPower :=
    pow_le_pow_right₀ (by linarith only [hB]) (le_max_right _ _)
  refine ⟨⟨hBase0, hBaseCommon.trans (hCommonBound.trans hScalarFinal)⟩,
    ⟨hWidth0, hWidthCommon.trans (hCommonBound.trans hScalarFinal)⟩,
    ⟨hGoodBounds.1.1, hGoodBounds.1.2.trans (hGoodPowerBound.trans hScalarFinal)⟩,
    ⟨hGoodBounds.2.1, hGoodBounds.2.2.trans (hGoodPowerBound.trans hScalarFinal)⟩, ?_⟩
  exact (hAnchor hB M nX hM hnX hRadius hScale hSeed hQw hGain hV hE hMaster hLate hPlate).trans
    hAnchorFinal

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.PreparedModularDetectorBadProduct

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem exists_preparedLateScalar_power_budget (inputPower : ℕ) :
    ∃ outputPower : ℕ, 2 ≤ outputPower ∧ ∀ {p : ℝ}, 0 ≤ p →
    ∀ Bstruct Pscale pRadius Pseed Pmin Elog Vlog master Pphysical lateTarget : ℝ,
      Bstruct ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      Pscale ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      pRadius ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      Pseed ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      Pmin ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      Elog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      Vlog ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      master ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      Pphysical ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      lateTarget ∈ Set.Icc 0 ((p + 2) ^ inputPower) →
      let Qw := 2 * Bstruct + 2 * Vlog + 5 * Elog + 24
      let B0 := 1 + (Bstruct + Pscale + pRadius) + Pseed + Qw + Pmin + Elog + Vlog
      let Plate := preparedModularGeneralDetectorLateMaster master Pseed Qw Pphysical lateTarget +
        (1 + Pseed ^ 2) * Pmin + Pscale
      Qw ∈ Set.Icc 0 ((p + 2) ^ outputPower) ∧
      B0 ∈ Set.Icc 0 ((p + 2) ^ outputPower) ∧
      Plate ∈ Set.Icc 0 ((p + 2) ^ outputPower) ∧ master ≤ Plate := by
  obtain ⟨Asp, _, hsp⟩ := exists_spatialParameterBudget_bound
  let T : Polynomial ℕ := (Polynomial.X + 2) ^ inputPower
  let witness : Polynomial ℕ := (1 + T ^ 2) * (5 * T + 49) + T ^ 2 * (9 * T + 24)
  let bound : Polynomial ℕ := 3 * T + witness + (2 * T + Polynomial.C Asp) ^ Asp + 1 +
    (1 + T ^ 2) * T + (16 * T + 25)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_fixed_power_budget bound
  refine ⟨C, hC, ?_⟩
  intro p hp Bstruct Pscale pRadius Pseed Pmin Elog Vlog master Pphysical lateTarget
    hBs hScale hRadius hSeed hMin hE hV hMaster hPhysical hTarget Qw B0 Plate
  let t := (p + 2) ^ inputPower
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hw : 0 ≤ Qw := by dsimp [Qw]; linarith [hBs.1, hV.1, hE.1]
  have hwB : Qw ≤ 9 * t + 24 := by dsimp [Qw, t]; linarith [hBs.2, hV.2, hE.2]
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]; linarith [hBs.1, hScale.1, hRadius.1, hSeed.1, hMin.1, hE.1, hV.1]
  have hB0B : B0 ≤ 16 * t + 25 := by
    dsimp [B0, t]; linarith [hBs.2, hScale.2, hRadius.2, hSeed.2, hMin.2, hE.2, hV.2]
  have hSeed0 := hSeed.1
  have hSeedB : Pseed ≤ t := hSeed.2
  have hMin0 := hMin.1
  have hMinB : Pmin ≤ t := hMin.2
  have hwitness : allocatedWitnessScaleLog Pseed Qw ≤
      (1 + t ^ 2) * (5 * t + 49) + t ^ 2 * (9 * t + 24) := by
    unfold allocatedWitnessScaleLog allocatedScaleLog
    gcongr
  have hnarrow : 2 * (spatialPrimitiveEnvelope Pphysical lateTarget 0 +
      spatialTupleToleranceLog (spatialPrimitiveEnvelope Pphysical lateTarget 0)) + 4 ≤
      (2 * t + Asp) ^ Asp := by
    apply (spatialParameterBudget_bounds hPhysical.1 hTarget.1 le_rfl).2.1.trans
    apply (hsp hPhysical.1 hTarget.1 le_rfl).trans
    apply pow_le_pow_left₀ (by linarith [hPhysical.1, hTarget.1, Nat.cast_nonneg (α := ℝ) Asp])
    dsimp [t]
    linarith [hPhysical.2, hTarget.2]
  have hfloor : (1 + Pseed ^ 2) * Pmin ≤ (1 + t ^ 2) * t := by gcongr
  have hPlateB : Plate ≤ 3 * t +
      ((1 + t ^ 2) * (5 * t + 49) + t ^ 2 * (9 * t + 24)) +
      (2 * t + Asp) ^ Asp + 1 + (1 + t ^ 2) * t := by
    dsimp only [Plate, preparedModularGeneralDetectorLateMaster]
    linarith [hMaster.2, hTarget.2, hScale.2]
  have hLate := preparedModularGeneralDetectorLateMaster_bounds hMaster.1 hSeed.1 hw
    hPhysical.1 hTarget.1
  have hPlate : 0 ≤ Plate :=
    add_nonneg (add_nonneg hLate.1 (mul_nonneg (by positivity) hMin.1)) hScale.1
  have hmaster : master ≤ Plate := by
    have hnonneg : 0 ≤ (1 + Pseed ^ 2) * Pmin := by positivity
    dsimp [Plate]
    linarith [hLate.2.1, hScale.1]
  have hmajor : 3 * t + ((1 + t ^ 2) * (5 * t + 49) + t ^ 2 * (9 * t + 24)) +
      (2 * t + Asp) ^ Asp + 1 + (1 + t ^ 2) * t + (16 * t + 25) ≤ (p + 2) ^ C := by
    simpa [bound, witness, T, t, Polynomial.eval₂_pow] using hbound p hp
  have hrest : 0 ≤ 3 * t + ((1 + t ^ 2) * (5 * t + 49) + t ^ 2 * (9 * t + 24)) +
      (2 * t + Asp) ^ Asp + 1 + (1 + t ^ 2) * t := by positivity
  refine ⟨⟨hw, ?_⟩, ⟨hB0, ?_⟩, ⟨hPlate, ?_⟩, hmaster⟩ <;> linarith

end Erdos3.VectorPolynomial

end

end OAI

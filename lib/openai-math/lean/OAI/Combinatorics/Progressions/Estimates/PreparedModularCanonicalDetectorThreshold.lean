import OAI.Combinatorics.Progressions.Nilpotent.AllocatedNiltestSupportedSlicedDetection

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable abbrev allocatedDetectedZeroGain (variableCount : ℕ)
    (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℝ :=
  (Real.exp (-((5 * p + 20) * variableCount + p + 2)) * (α / 2)) *
    Real.exp (-((q + sampledSupportedSlicedDetectionConstant 0 Pdetect) ^
      sampledSupportedSlicedDetectionConstant 0 Pdetect)) ^ (2 ^ (0 + 1))

noncomputable abbrev allocatedDetectedZeroKernelCutoff (G : Type) [Fintype G]
    (variableCount : ℕ) (Pdetect : Polynomial ℕ) (p q α : ℝ) : ℕ :=
  scalarKernelCutoff (Fin (0 + 1)) G 1 ⌈Real.exp (p + 1)⌉₊
    (allocatedDetectedZeroGain variableCount Pdetect p q α / 2)

theorem allocatedDetectedZeroGain_pos (count : ℕ) (Pdetect : Polynomial ℕ)
    (p q : ℝ) {α : ℝ} (hα : 0 < α) :
    0 < allocatedDetectedZeroGain count Pdetect p q α := by
  unfold allocatedDetectedZeroGain
  positivity

theorem allocatedDetectedZeroKernelCutoff_pos (G : Type) [Fintype G]
    (count : ℕ) (Pdetect : Polynomial ℕ) (p q : ℝ) {α : ℝ} (hα : 0 < α) :
    0 < allocatedDetectedZeroKernelCutoff G count Pdetect p q α :=
  (scalarKernelCutoff_bounds (Fin (0 + 1)) G (by decide)
    (Nat.ceil_pos.mpr (Real.exp_pos _))
    (half_pos (allocatedDetectedZeroGain_pos count Pdetect p q hα))).1

theorem allocatedDetectedZeroGain_lower (count : ℕ) (Pdetect : Polynomial ℕ)
    {p q a α pGain : ℝ} (hα : Real.exp (-a) ≤ α)
    (hlog : slicedDetectionGainLog 0 (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      count p q a ≤ pGain) :
    Real.exp (-pGain) / 2 ≤ allocatedDetectedZeroGain count Pdetect p q α / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (Real.exp_le_exp.mpr (neg_le_neg hlog)).trans
    (slicedDetectionGain_lower 0 (sampledSupportedSlicedDetectionConstant 0 Pdetect) count hα)

theorem exists_allocatedDetectedZero_parameter_budget (Pdetect : Polynomial ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p q a α : ℝ} {count : ℕ} (G : Type) [Fintype G],
      0 ≤ D → 0 ≤ p → 0 ≤ q → 0 ≤ a →
      (count : ℝ) ≤ D → (Fintype.card G : ℝ) ≤ D → Real.exp (-a) ≤ α →
      let budget := (D + p + q + a + A) ^ A
      0 ≤ budget ∧ 0 < allocatedDetectedZeroGain count Pdetect p q α ∧
      Real.exp (-budget) / 2 ≤ allocatedDetectedZeroGain count Pdetect p q α / 2 ∧
      0 < allocatedDetectedZeroKernelCutoff G count Pdetect p q α ∧
      (allocatedDetectedZeroKernelCutoff G count Pdetect p q α : ℝ) ≤ Real.exp budget := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_slicedDetection_uniform_budget 0 (sampledSupportedSlicedDetectionConstant 0 Pdetect)
  refine ⟨A, hA, ?_⟩
  intro D p q a α count G _ hD hp hq ha hcount hG hα budget
  obtain ⟨hgainLog, hkernelLog⟩ := hbound G hD hp hq ha hcount hG
  have hαpos : 0 < α := (Real.exp_pos _).trans_le hα
  refine ⟨by dsimp only [budget]; positivity,
    allocatedDetectedZeroGain_pos count Pdetect p q hαpos,
    allocatedDetectedZeroGain_lower count Pdetect hα hgainLog,
    allocatedDetectedZeroKernelCutoff_pos G count Pdetect p q hαpos, ?_⟩
  exact (slicedDetection_kernel_cutoff_bound 0
    (sampledSupportedSlicedDetectionConstant 0 Pdetect) count G hp hq ha hα).trans
      (Real.exp_le_exp.mpr hkernelLog)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem preparedModularCanonicalDetectorThreshold_parameters
    {u pModel K Ctail : ℝ} (count : ℕ)
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hK : 0 ≤ K) (hCtail : 0 ≤ Ctail)
    (hKcap : K ≤ Real.exp pModel) (hCtailCap : Ctail ≤ Real.exp pModel)
    (hcount : (count : ℝ) ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let α := allocatedModelUnitThreshold u pModel K Ctail
    let aDetect := 2 * u + 4 * pModel + 7
    0 ≤ pDetect ∧ 0 < α ∧ α ≤ 1 ∧ 0 ≤ aDetect ∧ Real.exp (-aDetect) ≤ α ∧
      count * Real.exp (-pDetect) ≤ α / 8 ∧ Real.exp (-pDetect) ≤ α / 4 := by
  obtain ⟨hα, hαone, hαlower⟩ :=
    allocatedModelUnitThreshold_bounds hu hpModel hK hCtail hKcap hCtailCap
  obtain ⟨hpDetect, hmesh, herror⟩ :=
    allocatedModelTestLog_detection hu hpModel hK hCtail hKcap hCtailCap hcount
  exact ⟨hpDetect, hα, hαone, by positivity, hαlower, hmesh, herror⟩

theorem preparedModularCanonicalDetectorThreshold_gain_kernel
    (G : Type) [Fintype G] (Pdetect : Polynomial ℕ) (count : ℕ)
    {u pModel K Ctail : ℝ}
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hK : 0 ≤ K) (hCtail : 0 ≤ Ctail)
    (hKcap : K ≤ Real.exp pModel) (hCtailCap : Ctail ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let α := allocatedModelUnitThreshold u pModel K Ctail
    let aDetect := 2 * u + 4 * pModel + 7
    let gainLog := slicedDetectionGainLog 0 (sampledSupportedSlicedDetectionConstant 0 Pdetect)
      count pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (0 + 1)) G (gainLog + pDetect + 4)
    0 < allocatedDetectedZeroGain count Pdetect pDetect pDetect α ∧
      Real.exp (-gainLog) / 2 ≤ allocatedDetectedZeroGain count Pdetect pDetect pDetect α / 2 ∧
      0 < allocatedDetectedZeroKernelCutoff G count Pdetect pDetect pDetect α ∧
      (allocatedDetectedZeroKernelCutoff G count Pdetect pDetect pDetect α : ℝ) ≤ Real.exp Pk := by
  intro pDetect α aDetect gainLog Pk
  obtain ⟨hα, _, hαlower⟩ :=
    allocatedModelUnitThreshold_bounds hu hpModel hK hCtail hKcap hCtailCap
  have hpDetect : 0 ≤ pDetect := by
    dsimp only [pDetect, allocatedModelTestLog]
    positivity
  have haDetect : 0 ≤ aDetect := by dsimp only [aDetect]; positivity
  refine ⟨allocatedDetectedZeroGain_pos count Pdetect pDetect pDetect hα,
    allocatedDetectedZeroGain_lower count Pdetect hαlower le_rfl,
    allocatedDetectedZeroKernelCutoff_pos G count Pdetect pDetect pDetect hα, ?_⟩
  exact slicedDetection_kernel_cutoff_bound 0 (sampledSupportedSlicedDetectionConstant 0 Pdetect)
    count G hpDetect hpDetect haDetect hαlower

theorem preparedModularCanonicalDetectorThreshold_dense
    {I : Type*} [Fintype I] [DecidableEq I]
    {N : I → ℕ} {A : Finset (I → ℤ)} {P pSlice u : ℝ}
    (hP : 0 ≤ P) (hpSlice : 0 ≤ pSlice) (hu : 0 ≤ u)
    (hdense : IsDenseCommonStrideBox N pSlice A) :
    IsDenseCommonStrideBox N
      (allocatedModelTestLog u (allocatedEarlyModelLog P pSlice (Fintype.card I))) A := by
  apply hdense.mono_parameter
  have hcap : 0 ≤ earlyFiberCapLog P := earlyFiberCapLog_nonneg hP
  have hcount : (0 : ℝ) ≤ Fintype.card I := Nat.cast_nonneg _
  dsimp only [allocatedModelTestLog, allocatedEarlyModelLog]
  nlinarith

end Erdos3.VectorPolynomial

end

end OAI

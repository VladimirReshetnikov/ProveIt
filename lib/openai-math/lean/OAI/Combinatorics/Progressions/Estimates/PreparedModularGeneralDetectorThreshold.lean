import OAI.Combinatorics.Progressions.Geometry.SharedWidthAllocatedDetectedSpatialNativeSourceGeneral

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedDetectedGain_pos (s count : ℕ) (Pdetect : Polynomial ℕ)
    (p q : ℝ) {α : ℝ} (hα : 0 < α) :
    0 < allocatedDetectedGain s count Pdetect p q α := by
  unfold allocatedDetectedGain
  positivity

theorem allocatedDetectedKernelCutoff_pos (s : ℕ) (G : Type) [Fintype G]
    (count : ℕ) (Pdetect : Polynomial ℕ) (p q : ℝ) {α : ℝ} (hα : 0 < α) :
    0 < allocatedDetectedKernelCutoff s G count Pdetect p q α :=
  (scalarKernelCutoff_bounds (Fin (s + 1)) G (by decide)
    (Nat.ceil_pos.mpr (Real.exp_pos _))
    (half_pos (allocatedDetectedGain_pos s count Pdetect p q hα))).1

theorem allocatedDetectedGain_lower (s count : ℕ) (Pdetect : Polynomial ℕ)
    {p q a α pGain : ℝ} (hα : Real.exp (-a) ≤ α)
    (hlog : slicedDetectionGainLog s (sampledSupportedSlicedDetectionConstant s Pdetect)
      count p q a ≤ pGain) :
    Real.exp (-pGain) / 2 ≤ allocatedDetectedGain s count Pdetect p q α / 2 := by
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact (Real.exp_le_exp.mpr (neg_le_neg hlog)).trans
    (slicedDetectionGain_lower s (sampledSupportedSlicedDetectionConstant s Pdetect) count hα)

theorem exists_allocatedDetected_parameter_budget (s : ℕ) (Pdetect : Polynomial ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {D p q a α : ℝ} {count : ℕ} (G : Type) [Fintype G],
      0 ≤ D → 0 ≤ p → 0 ≤ q → 0 ≤ a →
      (count : ℝ) ≤ D → (Fintype.card G : ℝ) ≤ D → Real.exp (-a) ≤ α →
      let budget := (D + p + q + a + A) ^ A
      0 ≤ budget ∧ 0 < allocatedDetectedGain s count Pdetect p q α ∧
      Real.exp (-budget) / 2 ≤ allocatedDetectedGain s count Pdetect p q α / 2 ∧
      0 < allocatedDetectedKernelCutoff s G count Pdetect p q α ∧
      (allocatedDetectedKernelCutoff s G count Pdetect p q α : ℝ) ≤ Real.exp budget := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_slicedDetection_uniform_budget s (sampledSupportedSlicedDetectionConstant s Pdetect)
  refine ⟨A, hA, ?_⟩
  intro D p q a α count G _ hD hp hq ha hcount hG hα budget
  obtain ⟨hgainLog, hkernelLog⟩ := hbound G hD hp hq ha hcount hG
  have hαpos : 0 < α := (Real.exp_pos _).trans_le hα
  refine ⟨by dsimp only [budget]; positivity,
    allocatedDetectedGain_pos s count Pdetect p q hαpos,
    allocatedDetectedGain_lower s count Pdetect hα hgainLog,
    allocatedDetectedKernelCutoff_pos s G count Pdetect p q hαpos, ?_⟩
  exact (slicedDetection_kernel_cutoff_bound s
    (sampledSupportedSlicedDetectionConstant s Pdetect) count G hp hq ha hα).trans
      (Real.exp_le_exp.mpr hkernelLog)

theorem preparedModularGeneralDetectorThreshold_gain_kernel
    (s : ℕ) (G : Type) [Fintype G] (Pdetect : Polynomial ℕ) (count : ℕ)
    {u pModel K Ctail : ℝ}
    (hu : 0 ≤ u) (hpModel : 0 ≤ pModel) (hK : 0 ≤ K) (hCtail : 0 ≤ Ctail)
    (hKcap : K ≤ Real.exp pModel) (hCtailCap : Ctail ≤ Real.exp pModel) :
    let pDetect := allocatedModelTestLog u pModel
    let α := allocatedModelUnitThreshold u pModel K Ctail
    let aDetect := 2 * u + 4 * pModel + 7
    let gainLog := slicedDetectionGainLog s (sampledSupportedSlicedDetectionConstant s Pdetect)
      count pDetect pDetect aDetect
    let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + pDetect + 4)
    0 < allocatedDetectedGain s count Pdetect pDetect pDetect α ∧
      Real.exp (-gainLog) / 2 ≤ allocatedDetectedGain s count Pdetect pDetect pDetect α / 2 ∧
      0 < allocatedDetectedKernelCutoff s G count Pdetect pDetect pDetect α ∧
      (allocatedDetectedKernelCutoff s G count Pdetect pDetect pDetect α : ℝ) ≤ Real.exp Pk := by
  intro pDetect α aDetect gainLog Pk
  obtain ⟨hα, _, hαlower⟩ :=
    allocatedModelUnitThreshold_bounds hu hpModel hK hCtail hKcap hCtailCap
  have hpDetect : 0 ≤ pDetect := by
    dsimp only [pDetect, allocatedModelTestLog]
    positivity
  have haDetect : 0 ≤ aDetect := by dsimp only [aDetect]; positivity
  refine ⟨allocatedDetectedGain_pos s count Pdetect pDetect pDetect hα,
    allocatedDetectedGain_lower s count Pdetect hαlower le_rfl,
    allocatedDetectedKernelCutoff_pos s G count Pdetect pDetect pDetect hα, ?_⟩
  exact slicedDetection_kernel_cutoff_bound s (sampledSupportedSlicedDetectionConstant s Pdetect)
    count G hpDetect hpDetect haDetect hαlower

end Erdos3.VectorPolynomial

end

end OAI

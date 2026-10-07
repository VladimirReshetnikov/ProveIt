import OAI.Combinatorics.Progressions.Dynamics.OriginalParameterReferenceBudget
import OAI.Combinatorics.Progressions.Polynomial.ScalarInitialPolynomialBudget
import OAI.Combinatorics.Progressions.Polynomial.ScalarThresholdPolynomial

namespace OAI

section

namespace Erdos3

noncomputable def scalarInitialThreshold (E m n d : ℕ) (epsilon p P0 : ℝ) : ℝ :=
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  let U := scalarInitialReferenceInput m n d p P0
  let pref := affineReferenceInput epsilon U
  let common := affineCommonReferenceBudget E epsilon U
  let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
    (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
  scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E)
    (scalarTransferCellLog common b p Z U)
    (scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z))

theorem exists_scalarInitialThreshold_power (E d A : ℕ) (hE : 2 ≤ E)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m n : ℕ) (p : ℝ), 2 ≤ p →
      (m : ℝ) ≤ (d + 1 : ℝ) * p → (n : ℝ) ≤ p →
      epsilon⁻¹ ≤ Real.exp ((A : ℝ) * (p + 1)) →
      scalarInitialThreshold E m n d epsilon p ((A : ℝ) * (p + 1)) ≤ (p + 2) ^ C := by
  obtain ⟨C0, _, hUbound⟩ := exists_scalarInitialReferenceInput_power_bound d A
  obtain ⟨C1, hC1, hthreshold⟩ := exists_scalarCombinedLogThreshold_common_power
  let q := ((C0 + 4) * (affineReferencePower epsilon + 1) + 1) * E + 1
  refine ⟨(q + 2) * C1, by nlinarith [Nat.zero_le q], ?_⟩
  intro m n p hp hm hn heps
  let P0 := (A : ℝ) * (p + 1)
  let Z := replacementCommonInputLog m n d P0
  let G := 2 * physicalPairCoefficientLog n d Z + 2
  let U := scalarInitialReferenceInput m n d p P0
  let pref := affineReferenceInput epsilon U
  let common := affineCommonReferenceBudget E epsilon U
  let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
    (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
  have hp0 : 0 ≤ p := by linarith
  have hP0 : 0 ≤ P0 := by dsimp only [P0]; positivity
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  obtain ⟨hU, hZU, hGU, hP0U, hmU, hnU, hdU, hTU, hpU⟩ := scalarInitialReferenceInput_bounds m n d hp0 hP0
  have hGU' : G ≤ U := by linarith
  have hepsU : epsilon⁻¹ ≤ Real.exp U := heps.trans (Real.exp_le_exp.mpr hP0U)
  have hbase : 0 < scalarTransferBaseAccuracy (3 * p) := Real.exp_pos _
  have hbaseInv : (scalarTransferBaseAccuracy (3 * p))⁻¹ ≤ Real.exp U := by
    simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
    apply Real.exp_le_exp.mpr
    unfold scalarTransferTail at hTU
    linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hb := (adaptiveAffineCutoff_reference_bounds hE hepsilon hepsilon1 hU hp0 hT hZ hZ
    hpU hTU hZU hZU hmU hnU hepsU hbase hbaseInv).2
  have hc := affineCommonReferenceBudget_bounds hE epsilon hU
  have hcost : (pref + 2) ^ E ≤ common := by
    have hpref : 0 ≤ pref + 2 := by linarith [(affineReferenceInput_bounds epsilon hU).1]
    change (pref + 2) ^ E ≤ 2 * (pref + 2) ^ E
    nlinarith [pow_nonneg hpref E]
  have hthresholdCommon := hthreshold n d b p P0 Z G U common ((pref + 2) ^ E) hc.1 hZ
    (hpU.trans hc.2.1) (hP0U.trans hc.2.1) (hZU.trans hc.2.1) (hGU'.trans hc.2.1) hc.2.1
    (hnU.trans hc.2.1) (hdU.trans hc.2.1) hcost hb
  have hUoriginal : U ≤ (p + 2) ^ C0 := hUbound m n p hp0 hm hn
  have hcommonOriginal : common ≤ (p + 2) ^ q :=
    affineCommonReferenceBudget_le_original_power E epsilon hp hU hUoriginal
  exact polynomial_budget_comp hp0 hc.1 q C1 hcommonOriginal hthresholdCommon

end Erdos3

end

end OAI

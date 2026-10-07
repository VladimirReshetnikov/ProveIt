import OAI.Combinatorics.Progressions.Polynomial.AffineSidePolynomialBudget

namespace OAI

section

namespace Erdos3

theorem affineAdaptiveDegreeBudget_le_power {P : ℝ} (hP : 0 ≤ P) :
    affineAdaptiveDegreeBudget P ≤ 1024 * (P + 3) ^ 3 := by
  apply le_of_sub_nonneg
  simp only [affineAdaptiveDegreeBudget, affineLocalDegreeBudget, affineOuterDegreeInputBudget,
    affineLocalDegreeInputBudget, affineShellLogBudget, affineCountLogBudget, affinePrimitiveLogBudget]
  ring_nf
  positivity

theorem affineSidePolynomialBudget_le_power {P : ℝ} (hP : 0 ≤ P) :
    affineSidePolynomialBudget P ≤ 65536 * (P + 3) ^ 4 := by
  apply le_of_sub_nonneg
  simp only [affineSidePolynomialBudget, affineOrderPolynomialBudget, affineAccuracyPolynomialBudget,
    affineAdaptiveDegreeBudget, affineLocalDegreeBudget, affineOuterDegreeInputBudget,
    affineLocalDegreeInputBudget, affineShellLogBudget, affineCountLogBudget, affinePrimitiveLogBudget]
  ring_nf
  positivity

theorem adaptiveAffineCutoff_le_power (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    (adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog : ℝ) ≤
      1024 * (P + 3) ^ 3 :=
  (adaptiveAffineCutoff_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
    hLP hTP hCP hmod hA hsource hsite hinverse htotal htotalInv).trans (affineAdaptiveDegreeBudget_le_power hP)

theorem adaptiveAffineSideLog_le_power (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog dimLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P) (hdim : dimLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    adaptiveAffineSideLog A sourceDim siteDim epsilon L T C totalShell modLog dimLog ≤
      65536 * (P + 3) ^ 4 :=
  (adaptiveAffineSideLog_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
    hLP hTP hCP hmod hdim hA hsource hsite hinverse htotal htotalInv).trans (affineSidePolynomialBudget_le_power hP)

end Erdos3

end

section

namespace Erdos3

noncomputable def affineCommonReferenceBudget (E : ℕ) (epsilon U : ℝ) : ℝ :=
  2 * (affineReferenceInput epsilon U + 2) ^ E

theorem affineCommonReferenceBudget_bounds {E : ℕ} (hE : 2 ≤ E) (epsilon : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    0 ≤ affineCommonReferenceBudget E epsilon U ∧
    U ≤ affineCommonReferenceBudget E epsilon U ∧
    (⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ : ℝ) ≤ affineCommonReferenceBudget E epsilon U := by
  have hb := affineReferenceInput_bounds epsilon hU
  have hbase : 0 ≤ affineReferenceInput epsilon U + 2 := by linarith [hb.1]
  have hpow : affineReferenceInput epsilon U + 2 ≤ (affineReferenceInput epsilon U + 2) ^ E := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ affineReferenceInput epsilon U + 2)
      (show 1 ≤ E by omega)
  have hc := Nat.ceil_lt_add_one (by positivity : 0 ≤ (affineReferenceInput epsilon U + 2) ^ E)
  unfold affineCommonReferenceBudget
  exact ⟨by positivity, by linarith [hb.2.1], by linarith [hb.1]⟩

theorem adaptiveAffineCutoff_reference_bounds {E sourceDim siteDim : ℕ}
    {epsilon L T C totalShell modLog U : ℝ}
    (hE : 2 ≤ E) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U) (hmod : modLog ≤ U)
    (hsource : (sourceDim : ℝ) ≤ U) (hsite : (siteDim : ℝ) ≤ U)
    (hinverse : epsilon⁻¹ ≤ Real.exp U) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp U) :
    let A := ⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊
    let b := adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog
    2 * U ≤ (b : ℝ) ∧ (b : ℝ) ≤ 1024 * (affineCommonReferenceBudget E epsilon U + 3) ^ 3 := by
  intro A b
  have hp := affineReferenceInput_bounds epsilon hU
  have hc := affineCommonReferenceBudget_bounds hE epsilon hU
  have he : Real.exp U ≤ Real.exp (affineCommonReferenceBudget E epsilon U) := Real.exp_le_exp.mpr hc.2.1
  constructor
  · have hA : A ≤ b := by
      have h := (adaptiveAffineCutoff_bounds A sourceDim siteDim epsilon L T C totalShell modLog).1
      dsimp only [b]
      omega
    have hAr : (A : ℝ) ≤ b := by exact_mod_cast hA
    have hbase := ceil_power_dominates_twice hp.1 hE
    change 2 * affineReferenceInput epsilon U ≤ (A : ℝ) at hbase
    linarith [hp.2.1]
  · exact adaptiveAffineCutoff_le_power A sourceDim siteDim hepsilon hepsilon1 hc.1 hL hT hC hmod0
      (hLU.trans hc.2.1) (hTU.trans hc.2.1) (hCU.trans hc.2.1) (hmod.trans hc.2.1)
      hc.2.2 (hsource.trans hc.2.1) (hsite.trans hc.2.1) (hinverse.trans he) htotal (htotalInv.trans he)

theorem adaptiveAffineSideLog_reference_bound {E sourceDim siteDim : ℕ}
    {epsilon L T C totalShell modLog dimLog U : ℝ}
    (hE : 2 ≤ E) (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hU : 0 ≤ U)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLU : L ≤ U) (hTU : T ≤ U) (hCU : C ≤ U) (hmod : modLog ≤ U) (hdim : dimLog ≤ U)
    (hsource : (sourceDim : ℝ) ≤ U) (hsite : (siteDim : ℝ) ≤ U)
    (hinverse : epsilon⁻¹ ≤ Real.exp U) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp U) :
    adaptiveAffineSideLog ⌈(affineReferenceInput epsilon U + 2) ^ E⌉₊ sourceDim siteDim
      epsilon L T C totalShell modLog dimLog ≤ 65536 * (affineCommonReferenceBudget E epsilon U + 3) ^ 4 := by
  have hc := affineCommonReferenceBudget_bounds hE epsilon hU
  have he : Real.exp U ≤ Real.exp (affineCommonReferenceBudget E epsilon U) := Real.exp_le_exp.mpr hc.2.1
  exact adaptiveAffineSideLog_le_power _ sourceDim siteDim hepsilon hepsilon1 hc.1 hL hT hC hmod0
    (hLU.trans hc.2.1) (hTU.trans hc.2.1) (hCU.trans hc.2.1) (hmod.trans hc.2.1) (hdim.trans hc.2.1)
    hc.2.2 (hsource.trans hc.2.1) (hsite.trans hc.2.1) (hinverse.trans he) htotal (htotalInv.trans he)

end Erdos3

end

end OAI

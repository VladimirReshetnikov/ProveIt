import OAI.Combinatorics.Progressions.Dynamics.AdaptiveShellLogBudget

namespace OAI

section

namespace Erdos3

noncomputable def affineLocalDegreeInputBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P * (affinePrimitiveLogBudget P + 2 * P ^ 2 + 2) + 3 * P + 11

noncomputable def affineOuterDegreeInputBudget (P : ℝ) : ℝ := P * (2 * P ^ 2 + 1) + 4

noncomputable def affineLocalDegreeBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P + 2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2

noncomputable def affineAdaptiveDegreeBudget (P : ℝ) : ℝ :=
  P + affineLocalDegreeBudget P + 2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2

theorem affineDegreeBudgets_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineLocalDegreeInputBudget P ∧ 0 ≤ affineOuterDegreeInputBudget P ∧
      0 ≤ affineLocalDegreeBudget P ∧ 0 ≤ affineAdaptiveDegreeBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hS := (affineShellLogBudget_nonneg hP).2
  simp only [affineLocalDegreeInputBudget, affineOuterDegreeInputBudget, affineLocalDegreeBudget, affineAdaptiveDegreeBudget]
  constructor
  · positivity
  constructor
  · positivity
  constructor <;> positivity

theorem affineComparisonDegree_le_polynomialBudget (sourceDim siteDim : ℕ)
    {epsilon L T C shell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hshell : 0 < shell) (hshellInv : shell⁻¹ ≤ Real.exp (affineShellLogBudget P))
    (hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P) :
    (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) ≤ affineLocalDegreeBudget P := by
  let j := affineRemovalDepth T
  let tail := affineComparisonTail epsilon L T
  let scale := affineComparisonScale epsilon L T C
  let input := (j : ℝ) * (scale + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2) +
    epsilon + L + 2 * T + 10
  have hscale0 : 0 ≤ scale := (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hj : (j : ℝ) ≤ affinePrimitiveLogBudget P :=
    (Nat.cast_le.mpr (Nat.le_add_right j tail)).trans hsum
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hinner : scale + (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 2 ≤
      affinePrimitiveLogBudget P + 2 * P ^ 2 + 2 := by dsimp only [scale]; nlinarith
  have hmul := mul_le_mul hj hinner (by positivity) hH
  have hinput : input ≤ affineLocalDegreeInputBudget P := by
    dsimp only [input, affineLocalDegreeInputBudget]
    linarith
  have hinput0 : 0 ≤ input := by dsimp only [input]; positivity
  have hiter := CyclicCrootSisask.spectralIterations_le_logBudget hshell hinput0
    (affineShellLogBudget_nonneg hP).2 hshellInv
  have hiter' : (CyclicCrootSisask.spectralIterations shell input : ℝ) ≤
      2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2 := by linarith
  have hn : affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog ≤
      j + tail + CyclicCrootSisask.spectralIterations shell input := by
    dsimp only [affineComparisonDegree, affineFinalDegree, j, tail, input, scale]
    omega
  calc
    _ ≤ ((j + tail : ℕ) : ℝ) + (CyclicCrootSisask.spectralIterations shell input : ℝ) := by exact_mod_cast hn
    _ ≤ affinePrimitiveLogBudget P + (2 * (affineLocalDegreeInputBudget P + affineShellLogBudget P + 4) + 2) :=
      add_le_add hsum hiter'
    _ = _ := by unfold affineLocalDegreeBudget; ring

theorem affineGlobalComparisonDegree_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C shell modLog P : ℝ} (hP : 0 ≤ P) (hmod0 : 0 ≤ modLog)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hmod : modLog ≤ P) (hshell : 0 < shell) (hshellInv : shell⁻¹ ≤ Real.exp (affineShellLogBudget P))
    (hlocal : (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) ≤ affineLocalDegreeBudget P) :
    (affineGlobalComparisonDegree A sourceDim siteDim epsilon L T C shell modLog 0 : ℝ) ≤
      affineAdaptiveDegreeBudget P := by
  let input := (A : ℝ) * ((sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1) + 4
  have hs := mul_le_mul hsource hmod hmod0 hP
  have ht := mul_le_mul hsite hmod hmod0 hP
  have hi : (sourceDim : ℝ) * modLog + (siteDim : ℝ) * modLog + 1 ≤ 2 * P ^ 2 + 1 := by nlinarith
  have hm := mul_le_mul hA hi (by positivity) hP
  have hinput : input ≤ affineOuterDegreeInputBudget P := by
    dsimp only [input, affineOuterDegreeInputBudget]
    linarith
  have hinput0 : 0 ≤ input := by dsimp only [input]; positivity
  have hiter := CyclicCrootSisask.spectralIterations_le_logBudget hshell hinput0
    (affineShellLogBudget_nonneg hP).2 hshellInv
  have hiter' : (CyclicCrootSisask.spectralIterations shell input : ℝ) ≤
      2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2 := by linarith
  have hn : affineGlobalComparisonDegree A sourceDim siteDim epsilon L T C shell modLog 0 ≤
      A + affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog +
        CyclicCrootSisask.spectralIterations shell input := by
    dsimp only [affineGlobalComparisonDegree, input]
    simp only [add_zero]
    omega
  calc
    _ ≤ (A : ℝ) + (affineComparisonDegree sourceDim siteDim epsilon L T C shell modLog : ℝ) +
        (CyclicCrootSisask.spectralIterations shell input : ℝ) := by exact_mod_cast hn
    _ ≤ P + affineLocalDegreeBudget P + (2 * (affineOuterDegreeInputBudget P + affineShellLogBudget P + 4) + 2) :=
      add_le_add (add_le_add hA hlocal) hiter'
    _ = _ := by unfold affineAdaptiveDegreeBudget; ring

theorem adaptiveAffineCutoff_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    (adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog : ℝ) ≤
      affineAdaptiveDegreeBudget P := by
  have hp := affineComparisonPrimitive_bounds hepsilon hepsilon1 hP hL hT hC hLP hTP hCP hinverse
  have hcount := adaptiveAffineCountLog_le_budget A sourceDim siteDim hP hmod0 hA hsource hsite hmod
    (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1 hp.2.1
  have hs := adaptiveAffineShell_pos A sourceDim siteDim epsilon L T C modLog htotal
  have hsinv := adaptiveAffineShell_inverse_le_budget A sourceDim siteDim htotal htotalInv hcount
  have hlocal := affineComparisonDegree_le_polynomialBudget sourceDim siteDim hepsilon hepsilon1 hP
    hL hT hC hmod0 hLP hTP hsource hsite hmod hs hsinv hp.1 hp.2.1
  exact affineGlobalComparisonDegree_le_polynomialBudget A sourceDim siteDim hP hmod0 hA hsource hsite
    hmod hs hsinv hlocal

end Erdos3

end

section

namespace Erdos3

noncomputable def affineOrderPolynomialBudget (P : ℝ) : ℝ :=
  affinePrimitiveLogBudget P * (affinePrimitiveLogBudget P + 3) +
    2 * affineAdaptiveDegreeBudget P + affinePrimitiveLogBudget P

noncomputable def affineAccuracyPolynomialBudget (P : ℝ) : ℝ :=
  (affinePrimitiveLogBudget P + 3) ^ 3 +
    2 * affineAdaptiveDegreeBudget P * (affinePrimitiveLogBudget P + 2) + 2 * P + 4

noncomputable def affineSidePolynomialBudget (P : ℝ) : ℝ :=
  P ^ 2 + P * affineOrderPolynomialBudget P + affineAccuracyPolynomialBudget P + P + 3

theorem affineSidePolynomialBudgets_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineOrderPolynomialBudget P ∧ 0 ≤ affineAccuracyPolynomialBudget P ∧
      0 ≤ affineSidePolynomialBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  simp only [affineOrderPolynomialBudget, affineAccuracyPolynomialBudget, affineSidePolynomialBudget]
  constructor
  · positivity
  constructor <;> positivity

theorem affineComparisonRequiredOrder_le_budget (b : ℕ) {epsilon L T C P : ℝ}
    (hP : 0 ≤ P) (hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P)
    (hsum : ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ affinePrimitiveLogBudget P)
    (hmoment : (affineComparisonMoment (affineComparisonScale epsilon L T C) : ℝ) ≤ affinePrimitiveLogBudget P + 2) :
    (affineComparisonRequiredOrder b epsilon L T C : ℝ) ≤ affineOrderPolynomialBudget P := by
  have hH := affinePrimitiveLogBudget_nonneg hP
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  have hj : (affineRemovalDepth T : ℝ) ≤ affinePrimitiveLogBudget P :=
    (Nat.cast_le.mpr (Nat.le_add_right (affineRemovalDepth T) (affineComparisonTail epsilon L T))).trans hsum
  unfold affineComparisonRequiredOrder
  rw [Nat.cast_max]
  apply max_le
  · have hm := mul_le_mul hsum (add_le_add hmoment (le_refl (1 : ℝ)))
      (by positivity) hH
    push_cast at hm ⊢
    unfold affineOrderPolynomialBudget
    nlinarith
  · push_cast
    unfold affineOrderPolynomialBudget
    nlinarith [mul_nonneg hH (by linarith : 0 ≤ affinePrimitiveLogBudget P + 3)]

theorem affineComparisonAccuracyLog_le_budget (b : ℕ) {epsilon L T C P : ℝ}
    (hP : 0 ≤ P) (hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P)
    (hscale0 : 0 ≤ affineComparisonScale epsilon L T C)
    (hscale : affineComparisonScale epsilon L T C ≤ affinePrimitiveLogBudget P)
    (hLP : L ≤ P) (hTP : T ≤ P) :
    affineComparisonAccuracyLog b (affineComparisonScale epsilon L T C) L T ≤ affineAccuracyPolynomialBudget P := by
  have hB := (affineDegreeBudgets_nonneg hP).2.2.2
  have hp := pow_le_pow_left₀ (by linarith : 0 ≤ affineComparisonScale epsilon L T C + 3)
    (add_le_add hscale (le_refl (3 : ℝ))) 3
  have hm := mul_le_mul hb (add_le_add hscale (le_refl (2 : ℝ))) (by linarith) hB
  unfold affineComparisonAccuracyLog affineAccuracyPolynomialBudget
  nlinarith

theorem adaptiveAffineSideLog_le_polynomialBudget (A sourceDim siteDim : ℕ)
    {epsilon L T C totalShell modLog dimLog P : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) (hP : 0 ≤ P)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hC : 0 ≤ C) (hmod0 : 0 ≤ modLog)
    (hLP : L ≤ P) (hTP : T ≤ P) (hCP : C ≤ P) (hmod : modLog ≤ P) (hdim : dimLog ≤ P)
    (hA : (A : ℝ) ≤ P) (hsource : (sourceDim : ℝ) ≤ P) (hsite : (siteDim : ℝ) ≤ P)
    (hinverse : epsilon⁻¹ ≤ Real.exp P) (htotal : 0 < totalShell) (htotalInv : totalShell⁻¹ ≤ Real.exp P) :
    adaptiveAffineSideLog A sourceDim siteDim epsilon L T C totalShell modLog dimLog ≤
      affineSidePolynomialBudget P := by
  let b := adaptiveAffineCutoff A sourceDim siteDim epsilon L T C totalShell modLog
  have hb : (b : ℝ) ≤ affineAdaptiveDegreeBudget P :=
    adaptiveAffineCutoff_le_polynomialBudget A sourceDim siteDim hepsilon hepsilon1 hP hL hT hC hmod0
      hLP hTP hCP hmod hA hsource hsite hinverse htotal htotalInv
  have hp := affineComparisonPrimitive_bounds hepsilon hepsilon1 hP hL hT hC hLP hTP hCP hinverse
  have ho := affineComparisonRequiredOrder_le_budget b hP hb hp.1 hp.2.2
  have ha := affineComparisonAccuracyLog_le_budget b hP hb
    (affineComparisonScale_bounds (ε := epsilon) hL hT hC).1 hp.2.1 hLP hTP
  have hm := mul_le_mul hmod hA (Nat.cast_nonneg A) hP
  have horder := mul_le_mul hmod ho (Nat.cast_nonneg _) hP
  change modLog * A +
    (modLog * (affineComparisonRequiredOrder b epsilon L T C : ℝ) +
      affineComparisonAccuracyLog b (affineComparisonScale epsilon L T C) L T + dimLog + 1) + 2 ≤ _
  unfold affineSidePolynomialBudget
  nlinarith

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AllocatedInactiveNaturalCases
import OAI.Combinatorics.Progressions.Estimates.AllocatedPeriodicAmbientSiteExpansion
import OAI.Combinatorics.Progressions.Fourier.AllocatedSiteSpectrumBudget

namespace OAI

section

namespace Erdos3

def siteExponentialOutputLog {A : Type*} [Semiring A] (s : ℕ) (Q : A) : A :=
  s * (4 * Q + 8) + 8 * Q + 18

theorem siteExponentialOutputLog_nonneg (s : ℕ) {Q : ℝ} (hQ : 0 ≤ Q) :
    0 ≤ siteExponentialOutputLog s Q := by unfold siteExponentialOutputLog; positivity

theorem siteExponentialOutput_bounds (s k : ℕ) (hk : k ≤ s) {Q size period cap : ℝ}
    (hQ : 0 ≤ Q) (hsize : size ≤ Real.exp Q) (hperiod : period ≤ Real.exp Q)
    (hcap : cap ≤ Real.exp Q) :
    let O := siteExponentialOutputLog s Q
    size * Real.exp ((k : ℝ) * (4 * Q + 8)) ≤ Real.exp O ∧
      period ≤ Real.exp O ∧ cap * Real.exp ((k : ℝ) * (4 * Q + 8) + Q) ≤ Real.exp O ∧
      Real.exp (1 + 6 * Q + 12) + 4 ≤ Real.exp O ∧ Real.exp Q ≤ Real.exp O := by
  let N := (s : ℝ) * (4 * Q + 8)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hQO : Q ≤ siteExponentialOutputLog s Q := by
    change Q ≤ N + 8 * Q + 18
    linarith
  have hNO : N + 2 * Q ≤ siteExponentialOutputLog s Q := by
    change N + 2 * Q ≤ N + 8 * Q + 18
    linarith
  have hLO : 6 * Q + 18 ≤ siteExponentialOutputLog s Q := by
    change 6 * Q + 18 ≤ N + 8 * Q + 18
    linarith
  have hA : (k : ℝ) * (4 * Q + 8) ≤ N :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (by positivity)
  have hbase := Real.exp_le_exp.mpr hA
  have hbaseQ := Real.exp_le_exp.mpr (add_le_add hA (le_refl Q))
  have hT := (mul_le_mul hsize hbase (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hC := (mul_le_mul hcap hbaseQ (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hT' := hT.trans (Real.exp_le_exp.mpr
    (by linarith only [hNO, hQ] : Q + N ≤ siteExponentialOutputLog s Q))
  have hC' := hC.trans (Real.exp_le_exp.mpr
    (by linarith only [hNO] : Q + (N + Q) ≤ siteExponentialOutputLog s Q))
  have hL := add_le_exp_add_one (by positivity : 0 ≤ 1 + 6 * Q + 12)
    (by norm_num : (0 : ℝ) ≤ 4) (le_refl (Real.exp (1 + 6 * Q + 12)))
    (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)])
  have hL' := hL.trans (Real.exp_le_exp.mpr
    (by linarith only [hLO] : (1 + 6 * Q + 12) + 4 + 1 ≤ siteExponentialOutputLog s Q))
  exact ⟨hT', hperiod.trans (Real.exp_le_exp.mpr hQO), hC', hL', Real.exp_le_exp.mpr hQO⟩

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def allocatedInactiveSiteBudgetLog {A : Type*} [Semiring A]
    (m : ℕ) (D p v E : A) : A :=
  allocatedInactiveSpectrumLog m D p 0 + allocatedInactiveSpectrumLog m D p E + E +
    inactiveShortLipschitzLog D v + allocatedInactiveSupportLog D + 2 * D + 13

def allocatedInactiveSiteOutputLog {A : Type*} [Semiring A]
    (m : ℕ) (D p v E : A) : A :=
  let Q := allocatedInactiveSiteBudgetLog m D p v E
  (2 ^ (m + 1) : ℕ) * (4 * Q + 8) + 8 * Q + 18

noncomputable def allocatedInactiveSitePrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p v E : A) : A :=
  allocatedInactiveSiteOutputLog m (allocatedComparisonDimension m p) p v E

theorem allocatedInactiveSiteBudgetLog_bounds (m : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    let Q := allocatedInactiveSiteBudgetLog m D p v E
    0 ≤ Q ∧ allocatedInactiveSpectrumLog m D p 0 + E ≤ Q ∧
      allocatedInactiveSpectrumLog m D p E + 2 * D + 13 ≤ Q ∧
      inactiveShortLipschitzLog D v ≤ Q ∧ inactiveShortCapLog D v ≤ Q ∧
      allocatedInactiveSupportLog D ≤ Q ∧ E ≤ Q := by
  have hS := allocatedInactiveSpectrumLog_nonneg m hD hp hE
  have hC := allocatedInactiveSpectrumLog_nonneg m hD hp (le_refl (0 : ℝ))
  obtain ⟨hN, _, hL⟩ := inactiveShortLogs_nonneg hD hv
  have hH : 0 ≤ allocatedInactiveSupportLog D := by unfold allocatedInactiveSupportLog; positivity
  have hcap : inactiveShortCapLog D v ≤ inactiveShortLipschitzLog D v := by
    unfold inactiveShortCapLog inactiveShortLipschitzLog
    nlinarith only [hD, hN]
  dsimp only
  unfold allocatedInactiveSiteBudgetLog
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedInactiveSiteOutputLog_bounds (m : ℕ) {D p v E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    let Q := allocatedInactiveSiteBudgetLog m D p v E
    let O := allocatedInactiveSiteOutputLog m D p v E
    0 ≤ O ∧ Q ≤ O ∧ (2 ^ (m + 1) : ℕ) * (4 * Q + 8) + 2 * Q ≤ O ∧ 6 * Q + 18 ≤ O := by
  have hQ := (allocatedInactiveSiteBudgetLog_bounds m hD hp hv hE).1
  have hpart : 0 ≤ ((2 ^ (m + 1) : ℕ) : ℝ) * (4 * allocatedInactiveSiteBudgetLog m D p v E + 8) :=
    by positivity
  dsimp only [allocatedInactiveSiteOutputLog]
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem exists_allocatedInactiveSitePrimitiveLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedInactiveSitePrimitiveLog m p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedInactiveSitePrimitiveLog m Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedInactiveSitePrimitiveLog, allocatedInactiveSiteOutputLog,
    allocatedInactiveSiteBudgetLog, inactiveShortLipschitzLog, inactiveShortScaleLog,
    allocatedInactiveSupportLog, allocatedInactiveSpectrumLog, allocatedComparisonDimension,
    allocatedInactiveTorusLog, allocatedInactiveScaleLog, uniformRetainedComplexityLog,
    uniformSpectrumSizeLog, uniformSpectrumCardLog, uniformRetainedFrequencyLog,
    uniformRetainedDenominatorLog, uniformRetainedBiasLog, uniformBlockAccuracyLog,
    majorArcSpectrumLog, majorArcCoverLog, majorArcLengthLog, majorArcBiasLog,
    majorArcErrorLog, majorArcLocalizationLog, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_pow] using hbound p hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped NNReal

theorem siteCharacterLipschitz_exp_bound (c r : ℕ) {D F f : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hc : (c : ℝ) ≤ D) (hr : (r : ℝ) ≤ D)
    (hf : f ≤ Real.exp F) :
    (((CircleFourier.characterLipConstant * (r * Real.toNNReal f) + 4) *
      (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp (F + 2 * D + 13) := by
  have hfrequency : (Real.toNNReal f : ℝ) ≤ Real.exp F := coe_toNNReal_le_exp hf
  have hrow : (r : ℝ) ≤ Real.exp D := hr.trans (by linarith [Real.add_one_le_exp D])
  have hchar : (CircleFourier.characterLipConstant : ℝ) ≤ Real.exp 8 := by
    rw [CircleFourier.coe_characterLipConstant]
    linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ c ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) c hc
  have hrowFreq := (mul_le_mul hrow hfrequency (Real.toNNReal f).coe_nonneg (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hprod := (mul_le_mul hchar hrowFreq (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hplus := add_le_exp_add_one (by positivity : 0 ≤ 8 + (D + F))
    (by norm_num : (0 : ℝ) ≤ 4) hprod
    (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)])
  have htotal := (mul_le_mul hplus hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have htotal' : ((CircleFourier.characterLipConstant : ℝ) *
      ((r : ℝ) * (Real.toNNReal f : ℝ)) + 4) * (2 : ℝ) ^ c ≤ Real.exp (F + 2 * D + 13) :=
    htotal.trans_eq (by congr 1; ring)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow] using htotal'

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

noncomputable def allocatedInactiveSiteFactor (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  (blockTorusFactor (Fintype.card α) (a.1.val + 1) (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 2 : ℝ) *
    2 ^ (a.1.val + 2)

noncomputable def allocatedInactiveSiteCap (P : ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  uniformSpectrumAbsoluteCap a.1.val (rowSets a.1).card ((a.1.val + 1) * (rowSets a.1).card) P
    (allocatedInactiveSiteFactor (α := α) B a) ((allocatedInactiveSiteFactor (α := α) B a) ^ (rowSets a.1).card)

noncomputable def allocatedInactiveSiteBias (P ε : ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  uniformBlockRetainedBias a.1.val (rowSets a.1).card ((a.1.val + 1) * (rowSets a.1).card) P
    (allocatedInactiveSiteFactor (α := α) B a) ((allocatedInactiveSiteFactor (α := α) B a) ^ (rowSets a.1).card) ε

noncomputable def allocatedInactiveSiteSize (P ε : ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  uniformSpectrumSizeConstant a.1.val (rowSets a.1).card ((a.1.val + 1) * (rowSets a.1).card) P
    (allocatedInactiveSiteFactor (α := α) B a) ((allocatedInactiveSiteFactor (α := α) B a) ^ (rowSets a.1).card) /
      ε ^ max (majorArcSpectrumExponent a.1.val (rowSets a.1).card)
        (majorArcLengthExponent a.1.val * ((a.1.val + 1) * (rowSets a.1).card))

noncomputable def allocatedInactiveSiteFrequency (P ε : ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  2 * majorArcCoverConstant a.1.val (rowSets a.1).card P (allocatedInactiveSiteFactor (α := α) B a) /
    (allocatedInactiveSiteBias B rowSets P ε a) ^ majorArcCoverExponent a.1.val (rowSets a.1).card

noncomputable def allocatedInactiveSitePeriod (P ε : ℝ) (a : Σ j : Fin m, Fin (n j)) : ℝ :=
  uniformCharacterDenominatorBound a.1.val (rowSets a.1).card ((a.1.val + 1) * (rowSets a.1).card) P
    (allocatedInactiveSiteFactor (α := α) B a) ((allocatedInactiveSiteFactor (α := α) B a) ^ (rowSets a.1).card)
    (allocatedInactiveSiteBias B rowSets P ε a)

variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedInactiveSite_construction_bounds
    (hα : Fintype.card α ≤ m + 1) {P p v ε E : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (q : ℕ) (hq : (q : ℝ) ≤ Real.exp v) (a : Σ j : Fin m, Fin (n j)) :
    let Q := allocatedInactiveSiteBudgetLog m D p v E
    let N := inactiveNaturalShortScale (Fintype.card α) (a.1.val + 1) q
    allocatedInactiveSiteRadius (G := G) B rowSets a ≤ Real.exp Q ∧
      (ε / (allocatedInactiveSiteCap B rowSets P a + 1))⁻¹ ≤ Real.exp Q ∧
      (((CircleFourier.characterLipConstant *
        ((rowSets a.1).card * Real.toNNReal (allocatedInactiveSiteFrequency B rowSets P ε a)) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      (N : ℝ) ^ (rowSets a.1).card ≤ Real.exp Q ∧
      ((((rowSets a.1).card * (2 * (N : ℝ≥0) ^ 2) * (N : ℝ≥0) ^ (rowSets a.1).card) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) : ℝ) ≤ Real.exp Q ∧ ε⁻¹ ≤ Real.exp Q := by
  obtain ⟨_, hcapQ, hfreqQ, hshortLQ, hshortCQ, hsupportQ, hEQ⟩ :=
    allocatedInactiveSiteBudgetLog_bounds m h.nonneg hp hv hE
  have hs := allocatedInactiveSpectrum_exp_bounds B rowSets h hα hP hp hPp hε hε1 hE hεE a
  have hs0 := allocatedInactiveSpectrum_exp_bounds B rowSets h hα hP hp hPp
    (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ)) (le_refl (0 : ℝ))
    (by norm_num : (1 : ℝ)⁻¹ ≤ Real.exp 0) a
  have hcap : allocatedInactiveSiteCap B rowSets P a + 1 ≤
      Real.exp (allocatedInactiveSpectrumLog m D p 0) := hs0.1
  have hinv : (ε / (allocatedInactiveSiteCap B rowSets P a + 1))⁻¹ ≤
      Real.exp (allocatedInactiveSpectrumLog m D p 0 + E) := by
    rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul hcap hεE (inv_nonneg.mpr hε.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  have hrow : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using h.rows a.1
  have hf : allocatedInactiveSiteFrequency B rowSets P ε a ≤
      Real.exp (allocatedInactiveSpectrumLog m D p E) := hs.2.2.1
  have hLip := siteCharacterLipschitz_exp_bound (Fintype.card α) (rowSets a.1).card h.nonneg
    (allocatedInactiveSpectrumLog_nonneg m h.nonneg hp hE) h.cube hrow hf
  obtain ⟨hshortCap, hshortLip⟩ := inactiveNaturalShortResources_exp_bounds
    (Fintype.card α) (a.1.val + 1) q (rowSets a.1).card h.nonneg hv h.cube (h.layer_degree B a.1) hrow hq
  exact ⟨(allocatedInactiveSiteRadius_exp_bound B rowSets h a).trans (Real.exp_le_exp.mpr hsupportQ),
    hinv.trans (Real.exp_le_exp.mpr hcapQ), hLip.trans (Real.exp_le_exp.mpr hfreqQ),
    hshortCap.trans (Real.exp_le_exp.mpr hshortCQ), hshortLip.trans (Real.exp_le_exp.mpr hshortLQ),
    hεE.trans (Real.exp_le_exp.mpr hEQ)⟩

theorem allocatedInactiveSite_output_bounds
    (hα : Fintype.card α ≤ m + 1) {P p v ε E : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (a : Σ j : Fin m, Fin (n j)) :
    let Q := allocatedInactiveSiteBudgetLog m D p v E
    let O := allocatedInactiveSiteOutputLog m D p v E
    let A := (Fintype.card (Finset α) : ℝ) * (4 * Q + 8)
    max (allocatedInactiveSiteSize B rowSets P ε a * Real.exp A) (Real.exp A) ≤ Real.exp O ∧
      max (allocatedInactiveSitePeriod B rowSets P ε a) 1 ≤ Real.exp O ∧
      max (allocatedInactiveSiteCap B rowSets P a * Real.exp (A + Q)) (Real.exp (A + Q)) ≤ Real.exp O ∧
      Real.exp (1 + 6 * Q + 12) + 4 ≤ Real.exp O := by
  let Q := allocatedInactiveSiteBudgetLog m D p v E
  let O := allocatedInactiveSiteOutputLog m D p v E
  let N := ((2 ^ (m + 1) : ℕ) : ℝ) * (4 * Q + 8)
  obtain ⟨hQ, _, hSQ, _, _, _, _⟩ := allocatedInactiveSiteBudgetLog_bounds m h.nonneg hp hv hE
  obtain ⟨hO, hQO, hNO, hLO⟩ := allocatedInactiveSiteOutputLog_bounds m h.nonneg hp hv hE
  have hD := h.nonneg
  have hSQ' : allocatedInactiveSpectrumLog m D p E ≤ Q := by linarith only [hSQ, hD]
  have hs := allocatedInactiveSpectrum_exp_bounds B rowSets h hα hP hp hPp hε hε1 hE hεE a
  have hcap : allocatedInactiveSiteCap B rowSets P a ≤ Real.exp Q :=
    (le_trans (by linarith : allocatedInactiveSiteCap B rowSets P a ≤
      allocatedInactiveSiteCap B rowSets P a + 1) hs.1).trans (Real.exp_le_exp.mpr hSQ')
  have hsize : allocatedInactiveSiteSize B rowSets P ε a ≤ Real.exp Q :=
    hs.2.1.trans (Real.exp_le_exp.mpr hSQ')
  have hperiod : allocatedInactiveSitePeriod B rowSets P ε a ≤ Real.exp Q :=
    hs.2.2.2.trans (Real.exp_le_exp.mpr hSQ')
  have hsites : (Fintype.card (Finset α) : ℝ) ≤ (2 ^ (m + 1) : ℕ) := by
    exact_mod_cast (show Fintype.card (Finset α) ≤ 2 ^ (m + 1) by
      rw [Fintype.card_finset]
      exact Nat.pow_le_pow_right (by norm_num) hα)
  have hA : (Fintype.card (Finset α) : ℝ) * (4 * Q + 8) ≤ N :=
    mul_le_mul_of_nonneg_right hsites (by positivity)
  have hbase := Real.exp_le_exp.mpr hA
  have hbaseQ := Real.exp_le_exp.mpr (add_le_add hA (le_refl Q))
  have hT := (mul_le_mul hsize hbase (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hC := (mul_le_mul hcap hbaseQ (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hNO' : N + 2 * Q ≤ O := hNO
  have hT' := hT.trans (Real.exp_le_exp.mpr (by linarith only [hNO', hQ] : Q + N ≤ O))
  have hC' := hC.trans (Real.exp_le_exp.mpr (by linarith only [hNO'] : Q + (N + Q) ≤ O))
  have hbase' := hbase.trans (Real.exp_le_exp.mpr (by linarith only [hNO', hQ] : N ≤ O))
  have hbaseQ' := hbaseQ.trans (Real.exp_le_exp.mpr (by linarith only [hNO', hQ] : N + Q ≤ O))
  have hL := add_le_exp_add_one (by positivity : 0 ≤ 1 + 6 * Q + 12)
    (by norm_num : (0 : ℝ) ≤ 4) (le_refl (Real.exp (1 + 6 * Q + 12)))
    (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)])
  have hL' := hL.trans (Real.exp_le_exp.mpr
    (by linarith only [hLO] : (1 + 6 * Q + 12) + 4 + 1 ≤ O))
  exact ⟨max_le hT' hbase', max_le (hperiod.trans (Real.exp_le_exp.mpr hQO))
    (Real.one_le_exp_iff.mpr hO), max_le hC' hbaseQ', hL'⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

def allocatedActiveSpectrumLog {A : Type*} [Semiring A] (m : ℕ) (D p E : A) : A :=
  ∑ j : Fin m, ∑ k : Fin (2 ^ (m + 1) + 1),
    positiveRetainedComplexityLog j.val k.val ((layerTailDegree m + 2) * k.val)
      p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) E

def allocatedActivePointCapLog {A : Type*} [Semiring A] (m : ℕ) (D p : A) : A :=
  allocatedSpectrumCardEnvelope m D p + 2

def allocatedActiveSiteBudgetLog {A : Type*} [Semiring A] (m : ℕ) (D p E : A) : A :=
  allocatedActiveSpectrumLog m D p E + allocatedActivePointCapLog m D p + E +
    allocatedNaturalSiteLog D + 2 * D + 13

def allocatedActiveSiteOutputLog {A : Type*} [Semiring A] (m : ℕ) (D p E : A) : A :=
  siteExponentialOutputLog (2 ^ (m + 1)) (allocatedActiveSiteBudgetLog m D p E)

theorem allocatedActiveSpectrumLog_nonneg (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ allocatedActiveSpectrumLog m D p E := by
  obtain ⟨hV, hW⟩ := allocatedSpectrumScaleLogs_nonneg hD
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
    (positiveRetainedComplexityLog_bounds j.val k.val ((layerTailDegree m + 2) * k.val) hp hV hW hE).1))

theorem allocatedActiveSpectrumLog_member (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (j : Fin m) (k : ℕ) (hk : k ≤ 2 ^ (m + 1)) :
    positiveRetainedComplexityLog j.val k ((layerTailDegree m + 2) * k)
        p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) E ≤
      allocatedActiveSpectrumLog m D p E := by
  obtain ⟨hV, hW⟩ := allocatedSpectrumScaleLogs_nonneg hD
  have hn (a : Fin m) (b : Fin (2 ^ (m + 1) + 1)) :
      0 ≤ positiveRetainedComplexityLog a.val b.val ((layerTailDegree m + 2) * b.val)
        p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) E :=
    (positiveRetainedComplexityLog_bounds _ _ _ hp hV hW hE).1
  have hi := Finset.single_le_sum (fun b _ => hn j b)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (2 ^ (m + 1) + 1)))
  exact hi.trans (Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => hn a b)) (Finset.mem_univ j))

theorem allocatedActivePointCapLog_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedActivePointCapLog m D p := by
  have hC := allocatedSpectrumCardEnvelope_nonneg m hD hp
  unfold allocatedActivePointCapLog
  positivity

theorem allocatedActiveSiteBudgetLog_bounds (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    let Q := allocatedActiveSiteBudgetLog m D p E
    0 ≤ Q ∧ allocatedActivePointCapLog m D p + E ≤ Q ∧
      allocatedActiveSpectrumLog m D p E + 2 * D + 13 ≤ Q ∧ allocatedNaturalSiteLog D ≤ Q := by
  have hS := allocatedActiveSpectrumLog_nonneg m hD hp hE
  have hC := allocatedActivePointCapLog_nonneg m hD hp
  have hH := allocatedNaturalSiteLog_nonneg hD
  dsimp only
  unfold allocatedActiveSiteBudgetLog
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem allocatedActiveSiteOutputLog_nonneg (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ allocatedActiveSiteOutputLog m D p E :=
  siteExponentialOutputLog_nonneg _ (allocatedActiveSiteBudgetLog_bounds m hD hp hE).1

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedActivePointCap_exp_bound (hα : Fintype.card α ≤ m + 1) {P p : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p) (a : Σ j : Fin m, Fin (n j)) :
    allocatedGridPointCap B P a (rowSets a.1) + 1 ≤ Real.exp (allocatedActivePointCapLog m D p) := by
  have hcap := allocatedGridPointCap_exp_bound B rowSets h hα hP hp hPp a
  have hC := allocatedSpectrumCardEnvelope_nonneg m h.nonneg hp
  have hplus := one_add_le_exp_succ (by positivity : 0 ≤ allocatedSpectrumCardEnvelope m D p + 1) hcap
  calc
    _ = 1 + allocatedGridPointCap B P a (rowSets a.1) := add_comm _ _
    _ ≤ _ := hplus
    _ = _ := by unfold allocatedActivePointCapLog; congr 1; ring

theorem allocatedActiveSpectrum_exp_bounds (hα : Fintype.card α ≤ m + 1) {P p ε E : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (a : Σ j : Fin m, Fin (n j)) :
    let k := (rowSets a.1).card
    let t := (layerTailDegree m + 2) * k
    let V := (allocatedGridTorusFactor B α a : ℝ)
    let ζ := positiveModerateRetainedBias a.1.val k t P V ((2 * V) ^ k) ε
    let Q := allocatedActiveSpectrumLog m D p E
    positiveModerateSpectrumCardBudget a.1.val k t P V ((2 * V) ^ k) ε ≤ Real.exp Q ∧
      positiveRetainedFrequencyBound a.1.val k P V ζ ≤ Real.exp Q ∧
      positiveRetainedDenominatorBound a.1.val k t P V ((2 * V) ^ k) ζ ≤ Real.exp Q := by
  obtain ⟨hV, hW⟩ := allocatedSpectrum_scales B rowSets h a
  obtain ⟨hv, hw⟩ := allocatedSpectrumScaleLogs_nonneg h.nonneg
  obtain ⟨hC, hF, hQ⟩ := positiveRetainedComplexity_exp_bounds a.1.val (rowSets a.1).card
    ((layerTailDegree m + 2) * (rowSets a.1).card) hP (Nat.cast_nonneg _) (by positivity)
    hε hp hv hw hE hPp hV hW hεE
  have henv := Real.exp_le_exp.mpr (allocatedActiveSpectrumLog_member m h.nonneg hp hE
    a.1 (rowSets a.1).card (finiteBooleanRows_card_le (rowSets a.1) hα))
  exact ⟨hC.trans henv, hF.trans henv, hQ.trans henv⟩

theorem allocatedActiveSite_construction_bounds (hα : Fintype.card α ≤ m + 1) {P p ε E : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (a : Σ j : Fin m, Fin (n j)) :
    let k := (rowSets a.1).card
    let V := (allocatedGridTorusFactor B α a : ℝ)
    let ζ := positiveModerateRetainedBias a.1.val k ((layerTailDegree m + 2) * k) P V ((2 * V) ^ k) ε
    let Q := allocatedActiveSiteBudgetLog m D p E
    allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4 ≤ Real.exp Q ∧
      (ε / (allocatedGridPointCap B P a (rowSets a.1) + 1))⁻¹ ≤ Real.exp Q ∧
      (((CircleFourier.characterLipConstant *
        (k * Real.toNNReal (positiveRetainedFrequencyBound a.1.val k P V ζ)) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) : ℝ) ≤ Real.exp Q := by
  obtain ⟨_, hcapQ, hfreqQ, hsupportQ⟩ := allocatedActiveSiteBudgetLog_bounds m h.nonneg hp hE
  have hcap := allocatedActivePointCap_exp_bound B rowSets h hα hP hp hPp a
  have hinv : (ε / (allocatedGridPointCap B P a (rowSets a.1) + 1))⁻¹ ≤
      Real.exp (allocatedActivePointCapLog m D p + E) := by
    rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul hcap hεE (inv_nonneg.mpr hε.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
  have hs := allocatedActiveSpectrum_exp_bounds B rowSets h hα hP hp hPp hε hE hεE a
  have hrow : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using h.rows a.1
  have hLip := siteCharacterLipschitz_exp_bound (Fintype.card α) (rowSets a.1).card h.nonneg
    (allocatedActiveSpectrumLog_nonneg m h.nonneg hp hE) h.cube hrow hs.2.1
  exact ⟨(allocatedNaturalSiteRadius_exp_bound B rowSets h a.1 a.2).trans (Real.exp_le_exp.mpr hsupportQ),
    hinv.trans (Real.exp_le_exp.mpr hcapQ), hLip.trans (Real.exp_le_exp.mpr hfreqQ)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

def allocatedInactivePointCapLog {A : Type*} [Semiring A]
    (m : ℕ) (D p v : A) : A :=
  allocatedInactiveSpectrumLog m D p 0 + inactiveShortCapLog D v

theorem allocatedInactivePointCapLog_nonneg (m : ℕ) {D p v : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hv : 0 ≤ v) :
    0 ≤ allocatedInactivePointCapLog m D p v :=
  add_nonneg (allocatedInactiveSpectrumLog_nonneg m hD hp (le_refl (0 : ℝ)))
    (inactiveShortLogs_nonneg hD hv).2.1

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

local notation "degree" => Fin.val j + 1
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hq in
theorem allocatedInactiveGrid_norm_exp_bound
    [Nonempty (B ⟨j, Sum.inr i⟩)] {D P p v : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val (rowSets j).card (degree * (rowSets j).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rowSets j → ℤ) :
    ‖(((scale : ℝ) ^ (rowSets j).card *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x z).toReal : ℝ) : ℂ)‖ ≤
      Real.exp (allocatedInactivePointCapLog m D p v) := by
  have hb := allocatedInactiveNaturalGrid_normalized_norm_le B U b S j i q hq r hR hσ
    (rowSets j) P hsize hgamma hsmall hcell hgrid A hA hprimitive hrows hB x z
  have hs := allocatedInactiveSpectrum_exp_bounds B rowSets hD hα hP hp hPp
    (by norm_num : (0 : ℝ) < 1) (le_refl (1 : ℝ)) (le_refl (0 : ℝ))
    (by norm_num : (1 : ℝ)⁻¹ ≤ Real.exp 0) ⟨j, i⟩
  have hrow : ((rowSets j).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using hD.rows j
  have hshort := inactiveNaturalShortResources_exp_bounds (Fintype.card α) (j.val + 1) q
    (rowSets j).card hD.nonneg hv hD.cube (hD.layer_degree B j) hrow hqv
  have hC := allocatedInactiveSpectrumLog_nonneg m hD.nonneg hp (le_refl (0 : ℝ))
  have hN := (inactiveShortLogs_nonneg hD.nonneg hv).2.1
  apply hb.trans
  apply max_le
  · exact hs.1.trans (Real.exp_le_exp.mpr (by unfold allocatedInactivePointCapLog; linarith only [hN]))
  · exact hshort.1.trans (Real.exp_le_exp.mpr (by unfold allocatedInactivePointCapLog; linarith only [hC]))

include hq in
theorem exists_allocated_inactive_budgeted_site_expansion
    [Nonempty (B ⟨j, Sum.inr i⟩)] {D P p v ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hqv : (q : ℝ) ≤ Real.exp v)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ 1)
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ degree)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (hσ1 : σ j ≤ 1) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    (hprimitive : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val (rowSets j).card (degree * (rowSets j).card) ≤
      Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let O := allocatedInactiveSiteOutputLog m D p v E
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp O) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rowSets j, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ (rowSets j).card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ 2 * ε := by
  let Q := allocatedInactiveSiteBudgetLog m D p v E
  have hQ := (allocatedInactiveSiteBudgetLog_bounds m hD.nonneg hp hv hE).1
  obtain ⟨hHQ, hεQ, hLQ, hshortCap, hshortLip, herror⟩ :=
    allocatedInactiveSite_construction_bounds B rowSets hD hα hP hp hv hPp hε hε1 hE hεE q hqv ⟨j, i⟩
  obtain ⟨e, he, herr⟩ := exists_allocated_inactive_natural_site_expansion_all_cases
    B U b S j i q hq r hR hσ (rowSets j) P ε hsize hgamma hsmall hcell hgrid hσ1 A hA
    hprimitive hε hε1 hrows hB hε hQ hHQ hεQ hLQ hshortCap hshortLip herror
  obtain ⟨hT, hperiod, hC, hL⟩ := allocatedInactiveSite_output_bounds B rowSets hD hα hP hp hv hPp
    hε hε1 hE hεE ⟨j, i⟩
  have hQO := (allocatedInactiveSiteOutputLog_bounds m hD.nonneg hp hv hE).2.1
  refine ⟨e, he.mono hT hperiod hC ?_ (hHQ.trans (Real.exp_le_exp.mpr hQO)), ?_⟩
  · exact_mod_cast hL
  · intro x y hy
    simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

local notation "degree" => Fin.val j + 1
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i
local notation "torus" => allocatedGridTorusFactor B α (Sigma.mk j i)
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hq in
theorem allocatedActiveGrid_norm_exp_bound
    {D P p : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hactive : S.value ^ degree < basisAxisScale (b j) i)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ S.value)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 2) * (rowSets j).card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rowSets j → ℤ) :
    ‖(((scale : ℝ) ^ (rowSets j).card *
      (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x z).toReal : ℝ) : ℂ)‖ ≤
      Real.exp (allocatedActivePointCapLog m D p) := by
  let M : ℕ := torus * scale
  have htorus : 0 < torus := blockTorusFactor_pos _ _ _ _
  let : NeZero M := ⟨(Nat.mul_pos htorus (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)).ne'⟩
  exact (allocatedPhysicalGrid_normalized_norm_le (M := M) B U b hR hσ S q r j i
    hactive hq hsize (rowSets j) P hcell hgrid hgamma L hL hcP hsP rfl hrows hB x z).trans
      (allocatedActivePointCap_exp_bound B rowSets hD hα hP hp hPp ⟨j, i⟩)

include hq in
theorem exists_allocated_active_budgeted_site_expansion
    {D P p ε E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B α (fun a => (rowSets a : Type _)) D)
    (hα : Fintype.card α ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (hactive : S.value ^ degree < basisAxisScale (b j) i)
    (hsize : (Fintype.card α + 1) * q ≤ S.value) (hgamma : gamma ≤ S.value)
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
    (hgrid : allocatedGridAxis (I := I) U b S.value ⟨j, Sum.inr i⟩)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hrows : ∀ t ∈ rowSets j, t.card ≤ degree)
    (hB : positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 2) * (rowSets j).card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    let O := allocatedActiveSiteOutputLog m D p E
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds (Real.exp O) (Real.exp O) (Real.exp O) ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp O) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rowSets j, booleanCoefficient y t = 0) →
        ‖(((scale : ℝ) ^ (rowSets j).card *
          (allocatedSupportedPhysicalGridPMF B U b hR hσ S q r hcell j i (rowSets j) x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval scale y‖ ≤ 2 * ε := by
  let M : ℕ := torus * scale
  have htorus : 0 < torus := blockTorusFactor_pos _ _ _ _
  let : NeZero M := ⟨(Nat.mul_pos htorus (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)).ne'⟩
  let Q := allocatedActiveSiteBudgetLog m D p E
  obtain ⟨hQ, hcapQ, hspecQ, _⟩ := allocatedActiveSiteBudgetLog_bounds m hD.nonneg hp hE
  obtain ⟨hHQ, hεQ, hLQ⟩ := allocatedActiveSite_construction_bounds B rowSets hD hα hP hp hPp hε hE hεE ⟨j, i⟩
  obtain ⟨e, he, herr⟩ := exists_allocated_scalar_site_expansion (M := M) B U b hR hσ S q r j i
    hactive hq hsize (rowSets j) P ε hcell hgrid hgamma L hL hcP hsP rfl hrows hB hε hε1 hε hQ hHQ hεQ hLQ
  have hcard := allocatedNaturalGridSpectrum_cover_card (M := M) B U b hR S j i hactive hgrid hgamma hP
    (Nat.cast_nonneg torus) (by simp only [M, Nat.cast_mul]; exact le_rfl) (rowSets j) hε hε1
  have hs := allocatedActiveSpectrum_exp_bounds B rowSets hD hα hP hp hPp hε hE hεE ⟨j, i⟩
  have hspecQ' : allocatedActiveSpectrumLog m D p E ≤ Q := by
    have hnonneg := hD.nonneg
    linarith only [hspecQ, hnonneg]
  have hcardQ := hcard.trans (hs.1.trans (Real.exp_le_exp.mpr hspecQ'))
  have hperiodQ := hs.2.2.trans (Real.exp_le_exp.mpr hspecQ')
  have hcap := allocatedActivePointCap_exp_bound B rowSets hD hα hP hp hPp ⟨j, i⟩
  have hcapQ' : allocatedGridPointCap B P ⟨j, i⟩ (rowSets j) ≤ Real.exp Q :=
    (le_trans (by linarith : allocatedGridPointCap B P ⟨j, i⟩ (rowSets j) ≤
      allocatedGridPointCap B P ⟨j, i⟩ (rowSets j) + 1) hcap).trans
      (Real.exp_le_exp.mpr (by linarith only [hcapQ, hE]))
  have hsites : Fintype.card (Finset α) ≤ 2 ^ (m + 1) := by
    rw [Fintype.card_finset]
    exact Nat.pow_le_pow_right (by norm_num) hα
  obtain ⟨hT, hperiod, hC, hLip, hsupport⟩ := siteExponentialOutput_bounds
    (2 ^ (m + 1)) (Fintype.card (Finset α)) hsites hQ hcardQ hperiodQ hcapQ'
  refine ⟨e, he.mono hT hperiod hC ?_ (hHQ.trans hsupport), ?_⟩
  · exact_mod_cast hLip
  · intro x y hy
    simpa only [two_mul] using herr x y hy

end Erdos3.VectorPolynomial

end

end OAI

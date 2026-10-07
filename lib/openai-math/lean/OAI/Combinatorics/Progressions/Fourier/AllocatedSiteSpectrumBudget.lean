import OAI.Combinatorics.Progressions.Dynamics.AllocatedIdealCoverErrorBudget
import OAI.Combinatorics.Progressions.Dynamics.UniformRetainedComplexityBudget
import OAI.Combinatorics.Progressions.Estimates.PositiveRetainedDenominatorLog

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedGridTorusLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 2 * D + 8

def allocatedSpectrumScaleLog {A : Type*} [Semiring A] (D : A) : A :=
  D * (allocatedGridTorusLog D + 1)

def allocatedSpectrumCardEnvelope {A : Type*} [Semiring A] (m : ℕ) (D p : A) : A :=
  ∑ j : Fin m, ∑ k : Fin (2 ^ (m + 1) + 1),
    positiveSpectrumCardLog j.val k.val ((layerTailDegree m + 2) * k.val)
      p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) 0

def allocatedSpectrumFrequencyEnvelope {A : Type*} [Semiring A] (m : ℕ) (D p E : A) : A :=
  ∑ j : Fin m, ∑ k : Fin (2 ^ (m + 1) + 1),
    positiveRetainedFrequencyLog j.val k.val ((layerTailDegree m + 2) * k.val)
      p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) E

def allocatedGridFamilyLog {A : Type*} [Semiring A] (m : ℕ) (D p : A) : A :=
  D + D * (allocatedSpectrumCardEnvelope m D p + 1) + 1

theorem allocatedSpectrumScaleLogs_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedGridTorusLog D ∧ 0 ≤ allocatedSpectrumScaleLog D := by
  unfold allocatedSpectrumScaleLog allocatedGridTorusLog
  exact ⟨by positivity, by positivity⟩

theorem allocatedSpectrumCardEnvelope_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedSpectrumCardEnvelope m D p := by
  obtain ⟨hT, hW⟩ := allocatedSpectrumScaleLogs_nonneg hD
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
    (positiveRetainedLogs_nonneg j.val k.val ((layerTailDegree m + 2) * k.val)
      hp hT hW (le_refl (0 : ℝ))).2.1))

theorem allocatedSpectrumFrequencyEnvelope_nonneg (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ allocatedSpectrumFrequencyEnvelope m D p E := by
  obtain ⟨hT, hW⟩ := allocatedSpectrumScaleLogs_nonneg hD
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
    (positiveRetainedLogs_nonneg j.val k.val ((layerTailDegree m + 2) * k.val)
      hp hT hW hE).2.2))

theorem allocatedGridFamilyLog_nonneg (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p) :
    0 ≤ allocatedGridFamilyLog m D p := by
  have hC := allocatedSpectrumCardEnvelope_nonneg m hD hp
  unfold allocatedGridFamilyLog
  positivity

theorem allocatedSpectrumCardEnvelope_member (m : ℕ) {D p : ℝ} (hD : 0 ≤ D) (hp : 0 ≤ p)
    (j : Fin m) (k : ℕ) (hk : k ≤ 2 ^ (m + 1)) :
    positiveSpectrumCardLog j.val k ((layerTailDegree m + 2) * k)
        p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) 0 ≤
      allocatedSpectrumCardEnvelope m D p := by
  obtain ⟨hT, hW⟩ := allocatedSpectrumScaleLogs_nonneg hD
  have hn (a : Fin m) (b : Fin (2 ^ (m + 1) + 1)) :
      0 ≤ positiveSpectrumCardLog a.val b.val ((layerTailDegree m + 2) * b.val)
        p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) 0 :=
    (positiveRetainedLogs_nonneg _ _ _ hp hT hW (le_refl (0 : ℝ))).2.1
  have hinner := Finset.single_le_sum (fun b _ => hn j b)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (2 ^ (m + 1) + 1)))
  exact hinner.trans (Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => hn a b)) (Finset.mem_univ j))

theorem allocatedSpectrumFrequencyEnvelope_member (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (j : Fin m) (k : ℕ) (hk : k ≤ 2 ^ (m + 1)) :
    positiveRetainedFrequencyLog j.val k ((layerTailDegree m + 2) * k)
        p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) E ≤
      allocatedSpectrumFrequencyEnvelope m D p E := by
  obtain ⟨hT, hW⟩ := allocatedSpectrumScaleLogs_nonneg hD
  have hn (a : Fin m) (b : Fin (2 ^ (m + 1) + 1)) :
      0 ≤ positiveRetainedFrequencyLog a.val b.val ((layerTailDegree m + 2) * b.val)
        p (allocatedGridTorusLog D) (allocatedSpectrumScaleLog D) E :=
    (positiveRetainedLogs_nonneg _ _ _ hp hT hW hE).2.2
  have hinner := Finset.single_le_sum (fun b _ => hn j b)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (2 ^ (m + 1) + 1)))
  exact hinner.trans (Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => hn a b)) (Finset.mem_univ j))

theorem finiteBooleanRows_card_le {α : Type*} [Fintype α] (rows : Finset (Finset α))
    {m : ℕ} (hq : Fintype.card α ≤ m + 1) : rows.card ≤ 2 ^ (m + 1) := by
  have hc : rows.card ≤ 2 ^ Fintype.card α := by
    simpa only [Fintype.card_finset] using rows.card_le_univ
  exact hc.trans (Nat.pow_le_pow_right (by norm_num) hq)

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedSpectrum_scales (a : Σ j : Fin m, Fin (n j)) :
    (allocatedGridTorusFactor B α a : ℝ) ≤ Real.exp (allocatedGridTorusLog D) ∧
      (2 * (allocatedGridTorusFactor B α a : ℝ)) ^ (rowSets a.1).card ≤
        Real.exp (allocatedSpectrumScaleLog D) := by
  have ht := allocatedGridTorusFactor_exp_bound B rowSets h a.1 a.2
  have hT := (allocatedSpectrumScaleLogs_nonneg h.nonneg).1
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase : 2 * (allocatedGridTorusFactor B α a : ℝ) ≤ Real.exp (allocatedGridTorusLog D + 1) :=
    (mul_le_mul htwo ht (Nat.cast_nonneg _) (Real.exp_pos _).le).trans_eq
      (by rw [← Real.exp_add, add_comm]; rfl)
  have hrows : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using h.rows a.1
  exact ⟨ht, pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) _ hrows⟩

theorem allocatedGridPointCap_exp_bound (hq : Fintype.card α ≤ m + 1) {P p : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p) (a : Σ j : Fin m, Fin (n j)) :
    allocatedGridPointCap B P a (rowSets a.1) ≤ Real.exp (allocatedSpectrumCardEnvelope m D p + 1) := by
  obtain ⟨hV, hW⟩ := allocatedSpectrum_scales B rowSets h a
  obtain ⟨hT, hScale⟩ := allocatedSpectrumScaleLogs_nonneg h.nonneg
  have hc := positiveModerateSpectrumCardBudget_exp_bound a.1.val (rowSets a.1).card
    ((layerTailDegree m + 2) * (rowSets a.1).card) hP (Nat.cast_nonneg _) (by positivity)
    (by norm_num : (0 : ℝ) < 1) hp hT hScale (le_refl (0 : ℝ)) hPp hV hW
    (by norm_num : (1 : ℝ)⁻¹ ≤ Real.exp 0)
  have henv := allocatedSpectrumCardEnvelope_member m h.nonneg hp a.1 (rowSets a.1).card
    (finiteBooleanRows_card_le (rowSets a.1) hq)
  have hplus := one_add_le_exp_succ (allocatedSpectrumCardEnvelope_nonneg m h.nonneg hp)
    (hc.trans (Real.exp_le_exp.mpr henv))
  change _ + 1 ≤ _
  rw [add_comm]
  exact hplus

theorem allocatedGridFamilyCap_exp_bound (hq : Fintype.card α ≤ m + 1) {P p : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p) :
    allocatedGridFamilyCap B (fun a => rowSets a.1) P + 1 ≤ Real.exp (allocatedGridFamilyLog m D p) := by
  have hC := allocatedSpectrumCardEnvelope_nonneg m h.nonneg hp
  have hD := h.nonneg
  have hs := sum_le_exp_of_card_and_uniform_bound
    (fun a => allocatedGridPointCap B P a (rowSets a.1)) (by positivity : 0 ≤ allocatedSpectrumCardEnvelope m D p + 1)
    (allocatedIntegerAxes_card_le B rowSets h) (allocatedGridPointCap_exp_bound B rowSets h hq hP hp hPp)
  have hplus := one_add_le_exp_succ
    (by positivity : 0 ≤ D + D * (allocatedSpectrumCardEnvelope m D p + 1)) hs
  rw [add_comm]
  exact hplus

theorem allocatedGridRetainedFrequency_exp_bound (hq : Fintype.card α ≤ m + 1) {P p ε E : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p) (hε : 0 < ε) (hE : 0 ≤ E)
    (hεE : ε⁻¹ ≤ Real.exp E) (a : Σ j : Fin m, Fin (n j)) :
    positiveRetainedFrequencyBound a.1.val (rowSets a.1).card P (allocatedGridTorusFactor B α a)
      (positiveModerateRetainedBias a.1.val (rowSets a.1).card
        ((layerTailDegree m + 2) * (rowSets a.1).card) P (allocatedGridTorusFactor B α a)
        ((2 * (allocatedGridTorusFactor B α a : ℝ)) ^ (rowSets a.1).card) ε) ≤
      Real.exp (allocatedSpectrumFrequencyEnvelope m D p E) := by
  obtain ⟨hV, hW⟩ := allocatedSpectrum_scales B rowSets h a
  obtain ⟨hT, hScale⟩ := allocatedSpectrumScaleLogs_nonneg h.nonneg
  have hf := positiveRetainedFrequencyBound_exp_bound a.1.val (rowSets a.1).card
    ((layerTailDegree m + 2) * (rowSets a.1).card) hP (Nat.cast_nonneg _) (by positivity) hε
    hp hT hScale hE hPp hV hW hεE
  exact hf.trans (Real.exp_le_exp.mpr (allocatedSpectrumFrequencyEnvelope_member m h.nonneg hp hE
    a.1 (rowSets a.1).card (finiteBooleanRows_card_le (rowSets a.1) hq)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

def allocatedInactiveTorusLog {A : Type*} [Semiring A] (D : A) : A := D ^ 2 + 3 * D + 9

def allocatedInactiveScaleLog {A : Type*} [Semiring A] (D : A) : A :=
  D * allocatedInactiveTorusLog D

def allocatedInactiveSpectrumLog {A : Type*} [Semiring A] (m : ℕ) (D p E : A) : A :=
  ∑ j : Fin m, ∑ k : Fin (2 ^ (m + 1) + 1),
    uniformRetainedComplexityLog j.val k.val ((j.val + 1) * k.val)
      p (allocatedInactiveTorusLog D) (allocatedInactiveScaleLog D) E

noncomputable def allocatedInactiveSpectrumPrimitiveLog {A : Type*} [Semiring A]
    (m : ℕ) (p E : A) : A :=
  allocatedInactiveSpectrumLog m (allocatedComparisonDimension m p) p E

theorem allocatedInactiveScaleLogs_nonneg {D : ℝ} (hD : 0 ≤ D) :
    0 ≤ allocatedInactiveTorusLog D ∧ 0 ≤ allocatedInactiveScaleLog D := by
  unfold allocatedInactiveScaleLog allocatedInactiveTorusLog
  exact ⟨by positivity, by positivity⟩

theorem allocatedInactiveSpectrumLog_nonneg (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 ≤ allocatedInactiveSpectrumLog m D p E := by
  obtain ⟨hV, hW⟩ := allocatedInactiveScaleLogs_nonneg hD
  exact Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun k _ =>
    (uniformRetainedComplexityLog_bounds j.val k.val ((j.val + 1) * k.val) hp hV hW hE).1))

theorem allocatedInactiveSpectrumLog_member (m : ℕ) {D p E : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (j : Fin m) (k : ℕ) (hk : k ≤ 2 ^ (m + 1)) :
    uniformRetainedComplexityLog j.val k ((j.val + 1) * k)
        p (allocatedInactiveTorusLog D) (allocatedInactiveScaleLog D) E ≤
      allocatedInactiveSpectrumLog m D p E := by
  obtain ⟨hV, hW⟩ := allocatedInactiveScaleLogs_nonneg hD
  have hn (a : Fin m) (b : Fin (2 ^ (m + 1) + 1)) :
      0 ≤ uniformRetainedComplexityLog a.val b.val ((a.val + 1) * b.val)
        p (allocatedInactiveTorusLog D) (allocatedInactiveScaleLog D) E :=
    (uniformRetainedComplexityLog_bounds _ _ _ hp hV hW hE).1
  have hinner := Finset.single_le_sum (fun b _ => hn j b)
    (Finset.mem_univ (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (2 ^ (m + 1) + 1)))
  exact hinner.trans (Finset.single_le_sum
    (fun a _ => Finset.sum_nonneg (fun b _ => hn a b)) (Finset.mem_univ j))

theorem exists_allocatedInactiveSpectrumPrimitiveLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedInactiveSpectrumPrimitiveLog m p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedInactiveSpectrumPrimitiveLog m Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedInactiveSpectrumPrimitiveLog, allocatedInactiveSpectrumLog,
    allocatedComparisonDimension, allocatedInactiveTorusLog, allocatedInactiveScaleLog,
    uniformRetainedComplexityLog, uniformSpectrumSizeLog, uniformSpectrumCardLog,
    uniformRetainedFrequencyLog, uniformRetainedDenominatorLog, uniformRetainedBiasLog,
    uniformBlockAccuracyLog, majorArcSpectrumLog, majorArcCoverLog, majorArcLengthLog,
    majorArcBiasLog, majorArcErrorLog, majorArcLocalizationLog,
    Polynomial.eval₂_finsetSum, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α (fun j => (rowSets j : Type _)) D)

include h

theorem allocatedInactiveSpectrum_scales (a : Σ j : Fin m, Fin (n j)) :
    let V := (blockTorusFactor (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 2 : ℝ) * 2 ^ (a.1.val + 2)
    V ≤ Real.exp (allocatedInactiveTorusLog D) ∧
      V ^ (rowSets a.1).card ≤ Real.exp (allocatedInactiveScaleLog D) := by
  have hD := h.nonneg
  have hblock := blockJetScaleBound_four_exp (Fintype.card α) (a.1.val + 1)
    (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) hD h.cube (h.layer_degree B a.1)
    (allocatedIntegerBlock_card_le B rowSets h a.1 a.2)
  have h24 : blockJetScaleBound (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 2 ≤
      blockJetScaleBound (Fintype.card α) (a.1.val + 1)
        (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 4 := by
    unfold blockJetScaleBound
    exact mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
  have ht : (blockTorusFactor (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 2 : ℝ) ≤ Real.exp (D ^ 2 + 2 * D + 8) := by
    have hraw := blockTorusFactor_upper (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) (by norm_num : (0 : ℝ) ≤ 2)
    have hupper := two_mul_add_three_exp_bound
      (by positivity : 0 ≤ D ^ 2 + 2 * D + 4) hblock
    have hupper' : 2 * blockJetScaleBound (Fintype.card α) (a.1.val + 1)
        (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 4 + 3 ≤ Real.exp (D ^ 2 + 2 * D + 8) :=
      hupper.trans_eq (by congr 1; ring)
    linarith only [hraw, h24, hupper']
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hdegree : ((a.1.val + 2 : ℕ) : ℝ) ≤ D + 1 := by
    have hdeg := h.layer_degree B a.1
    push_cast at hdeg ⊢
    linarith
  have hcost : (2 : ℝ) ^ (a.1.val + 2) ≤ Real.exp (D + 1) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (a.1.val + 2) hdegree
  have hV : (blockTorusFactor (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 2 : ℝ) * 2 ^ (a.1.val + 2) ≤
      Real.exp (allocatedInactiveTorusLog D) := by
    have hh := (mul_le_mul ht hcost (by positivity) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hh.trans_eq (by unfold allocatedInactiveTorusLog; congr 1; ring)
  have hrows : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using h.rows a.1
  exact ⟨hV, pow_le_exp_mul_of_le_exp (by positivity) hV
    (allocatedInactiveScaleLogs_nonneg hD).1 (rowSets a.1).card hrows⟩

theorem allocatedInactiveSpectrum_exp_bounds (hq : Fintype.card α ≤ m + 1) {P p ε E : ℝ}
    (hP : 1 ≤ P) (hp : 0 ≤ p) (hPp : P ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE : 0 ≤ E) (hεE : ε⁻¹ ≤ Real.exp E)
    (a : Σ j : Fin m, Fin (n j)) :
    let k := (rowSets a.1).card
    let t := (a.1.val + 1) * k
    let V := (blockTorusFactor (Fintype.card α) (a.1.val + 1)
      (Fintype.card (B ⟨a.1, Sum.inr a.2⟩)) 2 : ℝ) * 2 ^ (a.1.val + 2)
    let ζ := uniformBlockRetainedBias a.1.val k t P V (V ^ k) ε
    let Λ := allocatedInactiveSpectrumLog m D p E
    uniformSpectrumAbsoluteCap a.1.val k t P V (V ^ k) + 1 ≤ Real.exp Λ ∧
      uniformSpectrumSizeConstant a.1.val k t P V (V ^ k) /
        ε ^ max (majorArcSpectrumExponent a.1.val k) (majorArcLengthExponent a.1.val * t) ≤ Real.exp Λ ∧
      2 * majorArcCoverConstant a.1.val k P V / ζ ^ majorArcCoverExponent a.1.val k ≤ Real.exp Λ ∧
      uniformCharacterDenominatorBound a.1.val k t P V (V ^ k) ζ ≤ Real.exp Λ := by
  obtain ⟨hV, hW⟩ := allocatedInactiveSpectrum_scales B rowSets h a
  obtain ⟨hv, hw⟩ := allocatedInactiveScaleLogs_nonneg h.nonneg
  obtain ⟨hcap, hcard, hfreq, hden⟩ := uniformRetainedComplexity_exp_bounds a.1.val
    (rowSets a.1).card ((a.1.val + 1) * (rowSets a.1).card)
    hP (by positivity) (by positivity) hε hε1 hp hv hw hE hPp hV hW hεE
  have henv := Real.exp_le_exp.mpr (allocatedInactiveSpectrumLog_member m h.nonneg hp hE
    a.1 (rowSets a.1).card (finiteBooleanRows_card_le (rowSets a.1) hq))
  exact ⟨hcap.trans henv, hcard.trans henv, hfreq.trans henv, hden.trans henv⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

noncomputable def allocatedSiteSpectrumCapLog {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  allocatedGridFamilyLog m (allocatedComparisonDimension m p) p

noncomputable def allocatedSiteSpectrumInput {A : Type*} [Semiring A] (m : ℕ) (p w v E : A) : A :=
  allocatedSiteConstructionLog m p w v E (allocatedSiteSpectrumCapLog m p)

noncomputable def allocatedSiteSpectrumFrequencyLog {A : Type*} [Semiring A]
    (m : ℕ) (p w v E : A) : A :=
  allocatedSpectrumFrequencyEnvelope m (allocatedComparisonDimension m p) p
    (allocatedSiteSpectrumInput m p w v E)

noncomputable def allocatedSiteSpectrumLog {A : Type*} [Semiring A] (m : ℕ) (p w v E : A) : A :=
  allocatedSiteSpectrumInput m p w v E + allocatedSiteSpectrumFrequencyLog m p w v E +
    2 * allocatedComparisonDimension m p + 13

theorem allocatedSiteSpectrumLog_bounds (m : ℕ) {p w v E : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedSiteSpectrumCapLog m p ∧ 0 ≤ allocatedSiteSpectrumInput m p w v E ∧
      0 ≤ allocatedSiteSpectrumFrequencyLog m p w v E ∧ 0 ≤ allocatedSiteSpectrumLog m p w v E ∧
      allocatedSiteSpectrumInput m p w v E ≤ allocatedSiteSpectrumLog m p w v E ∧
      allocatedSiteSpectrumFrequencyLog m p w v E + 2 * allocatedComparisonDimension m p + 13 ≤
        allocatedSiteSpectrumLog m p w v E := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hC : 0 ≤ allocatedSiteSpectrumCapLog m p := allocatedGridFamilyLog_nonneg m hD hp
  have hI : 0 ≤ allocatedSiteSpectrumInput m p w v E :=
    (allocatedSiteConstructionLog_bounds m hp hw hv hE hC).1
  have hF : 0 ≤ allocatedSiteSpectrumFrequencyLog m p w v E :=
    allocatedSpectrumFrequencyEnvelope_nonneg m hD hp hI
  refine ⟨hC, hI, hF, ?_, ?_, ?_⟩
  all_goals unfold allocatedSiteSpectrumLog; linarith

theorem exists_allocatedSiteSpectrumLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedSiteSpectrumLog m p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ :=
    allocatedSiteSpectrumLog m Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedSiteSpectrumLog, allocatedSiteSpectrumInput, allocatedSiteSpectrumCapLog,
    allocatedSiteSpectrumFrequencyLog, allocatedSpectrumFrequencyEnvelope, allocatedGridFamilyLog,
    allocatedSpectrumCardEnvelope, allocatedGridTorusLog, allocatedSpectrumScaleLog,
    positiveRetainedFrequencyLog, positiveSpectrumCardLog, positiveRetainedBiasLog,
    positiveModerateAccuracyLog, positiveModerateSpectrumLog, positiveModerateCoverLog,
    positiveModerateLengthLog, majorArcCoverLog, majorArcErrorLog, majorArcLengthLog,
    majorArcLocalizationLog, majorArcBiasLog, allocatedSiteConstructionLog, allocatedComparisonDimension,
    allocatedNaturalSiteLog, uniformProductAccuracyLog, allocatedSitePointToleranceLog,
    allocatedSiteFamilyWindowLog, allocatedSiteAxisWindowLog, allocatedSiteCoefficientLog,
    allocatedSiteSpatialMassLog, coefficientMajorantMassLog, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

theorem allocatedSiteSpectrum_primitive_budget
    (hq : Fintype.card α ≤ m + 1) {p w v E P : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) (hP : 1 ≤ P) (hPp : P ≤ Real.exp p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p) :
    let δ := allocatedSitePrimitiveTolerance m p w v E
    let halfAccuracy := uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j)))
      (allocatedGridFamilyCap B (fun a => rowSets a.1) P + 1)
      (allocatedSitePointTolerance (G := G) B rowSets δ) / 2
    let frequency := fun a : Σ j : Fin m, Fin (n j) => Real.toNNReal
      (positiveRetainedFrequencyBound a.1.val (rowSets a.1).card P (allocatedGridTorusFactor B α a)
        (positiveModerateRetainedBias a.1.val (rowSets a.1).card ((layerTailDegree m + 2) * (rowSets a.1).card)
          P (allocatedGridTorusFactor B α a) ((2 * (allocatedGridTorusFactor B α a : ℝ)) ^ (rowSets a.1).card)
          halfAccuracy))
    let Λ := allocatedSiteSpectrumLog m p w v E
    ∀ a : Σ j : Fin m, Fin (n j),
      allocatedNaturalSiteRadius (G := G) B a.1 a.2 (rowSets a.1) + 1 / 4 ≤ Real.exp Λ ∧
      (halfAccuracy / (allocatedGridPointCap B P a (rowSets a.1) + 1))⁻¹ ≤ Real.exp Λ ∧
      (((CircleFourier.characterLipConstant * ((rowSets a.1).card * frequency a) + 4) *
        (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) : ℝ) ≤ Real.exp Λ := by
  let D := allocatedComparisonDimension m p
  let δ := allocatedSitePrimitiveTolerance m p w v E
  let halfAccuracy := uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j)))
    (allocatedGridFamilyCap B (fun a => rowSets a.1) P + 1)
    (allocatedSitePointTolerance (G := G) B rowSets δ) / 2
  let frequency := fun a : Σ j : Fin m, Fin (n j) => Real.toNNReal
    (positiveRetainedFrequencyBound a.1.val (rowSets a.1).card P (allocatedGridTorusFactor B α a)
      (positiveModerateRetainedBias a.1.val (rowSets a.1).card ((layerTailDegree m + 2) * (rowSets a.1).card)
        P (allocatedGridTorusFactor B α a) ((2 * (allocatedGridTorusFactor B α a : ℝ)) ^ (rowSets a.1).card)
        halfAccuracy))
  have hd := allocatedComparisonDimensions_of_primitive B
    (O := fun j => (rowSets j : Type _)) (fun _ => Subtype.val) hq
    (fun _ => Subtype.val_injective) hp hvars hI hn
  obtain ⟨hT, hInput, hF, _, hInputΛ, hFreqΛ⟩ := allocatedSiteSpectrumLog_bounds m hp hw hv hE
  have hcap := allocatedGridFamilyCap_exp_bound B rowSets hd hq hP hp hPp
  have hsite := allocatedSiteConstruction_primitive_budget B rowSets hq hp hw hv hE hT hP hvars hI hn hcap
  have hδ := allocatedSitePrimitiveTolerance_pos m p w v E
  have hpoint := (allocatedSitePointTolerance_spec (G := G) B rowSets hδ).1
  have hfamily := allocatedGridFamilyCap_nonneg B (fun a => rowSets a.1) hP
  have hhalf : 0 < halfAccuracy := div_pos
    (uniformProductAccuracy_spec _ (by positivity) hpoint).1 (by norm_num)
  dsimp only
  intro a
  have hlocal := hsite a
  have hcap0 : 0 ≤ allocatedGridPointCap B P a (rowSets a.1) :=
    zero_le_one.trans (allocatedGridPointCap_one_le B hP a (rowSets a.1))
  have hhalfInv : halfAccuracy⁻¹ ≤ Real.exp (allocatedSiteSpectrumInput m p w v E) := by
    calc
      _ ≤ (halfAccuracy / (allocatedGridPointCap B P a (rowSets a.1) + 1))⁻¹ := by
        have hstep : halfAccuracy⁻¹ ≤
            (allocatedGridPointCap B P a (rowSets a.1) + 1) * halfAccuracy⁻¹ := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ allocatedGridPointCap B P a (rowSets a.1) + 1 by linarith)
            (inv_nonneg.mpr hhalf.le)
        have heq : (halfAccuracy / (allocatedGridPointCap B P a (rowSets a.1) + 1))⁻¹ =
            (allocatedGridPointCap B P a (rowSets a.1) + 1) * halfAccuracy⁻¹ :=
          (inv_div _ _).trans (div_eq_mul_inv _ _)
        exact hstep.trans_eq heq.symm
      _ ≤ _ := hlocal.2
  have hf := allocatedGridRetainedFrequency_exp_bound B rowSets hd hq hP hp hPp hhalf hInput hhalfInv a
  have hfrequency : (frequency a : ℝ) ≤ Real.exp (allocatedSiteSpectrumFrequencyLog m p w v E) :=
    coe_toNNReal_le_exp hf
  have hrow : ((rowSets a.1).card : ℝ) ≤ D := by simpa only [Fintype.card_coe] using hd.rows a.1
  have hrowexp : ((rowSets a.1).card : ℝ) ≤ Real.exp D :=
    hrow.trans (by linarith [Real.add_one_le_exp D])
  have hchar : (CircleFourier.characterLipConstant : ℝ) ≤ Real.exp 8 := by
    rw [CircleFourier.coe_characterLipConstant]
    linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ Fintype.card α ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (Fintype.card α) hd.cube
  have hrowFreq := (mul_le_mul hrowexp hfrequency (frequency a).coe_nonneg (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hprod := (mul_le_mul hchar hrowFreq (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hD := hd.nonneg
  have hplus := add_le_exp_add_one
    (by positivity : 0 ≤ 8 + (D + allocatedSiteSpectrumFrequencyLog m p w v E))
    (by norm_num : (0 : ℝ) ≤ 4) hprod
    (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)])
  have htotal := (mul_le_mul hplus hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have htotal' : ((CircleFourier.characterLipConstant : ℝ) *
      ((rowSets a.1).card * (frequency a : ℝ)) + 4) * (2 : ℝ) ^ Fintype.card α ≤
      Real.exp (allocatedSiteSpectrumFrequencyLog m p w v E + 2 * D + 13) :=
    htotal.trans_eq (by congr 1; ring)
  refine ⟨hlocal.1.trans (Real.exp_le_exp.mpr hInputΛ),
    hlocal.2.trans (Real.exp_le_exp.mpr hInputΛ), ?_⟩
  have hout := htotal'.trans (Real.exp_le_exp.mpr hFreqΛ)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow] using hout

end Erdos3.VectorPolynomial

end

end OAI

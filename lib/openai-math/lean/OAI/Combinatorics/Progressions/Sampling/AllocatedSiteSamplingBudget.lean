import OAI.Combinatorics.Progressions.Dynamics.NormalizedTupleLargerBudget
import OAI.Combinatorics.Progressions.Dynamics.SiteReferenceErrorBudget
import OAI.Combinatorics.Progressions.Fourier.AllocatedSiteBufferFourier

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedSourceSamplingBudget (m dim A : ℕ) (P E l F : ℝ) : ℝ :=
  1 + P + E + l + F + allocatedJetFourierBudget m dim A P +
    tupleSideLogEnvelope P (E + 2) l + (P + 1) * P

theorem allocatedSourceSamplingBudget_bounds (m dim A : ℕ) {P E l F : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hl : 0 ≤ l) (hF : 0 ≤ F) :
    let Q := allocatedSourceSamplingBudget m dim A P E l F
    1 ≤ Q ∧ P ≤ Q ∧ E + 1 ≤ Q ∧ l ≤ Q ∧ F ≤ Q ∧
      allocatedJetFourierBudget m dim A P ≤ Q ∧ (P + 1) * P ≤ Q ∧
      tupleWidthLogEnvelope P (E + 2) ≤ Q ∧ tupleSideLogEnvelope P (E + 2) l ≤ Q := by
  have hjet := allocatedJetFourierBudget_nonneg m dim A hP
  obtain ⟨_, hwidth, hlate, hside⟩ := tupleLogEnvelopes_nonneg hP (by linarith : 0 ≤ E + 2) hl
  have hwidthSide : tupleWidthLogEnvelope P (E + 2) ≤ tupleSideLogEnvelope P (E + 2) l := by
    unfold tupleSideLogEnvelope
    linarith
  have hprod : 0 ≤ (P + 1) * P := by positivity
  dsimp only [allocatedSourceSamplingBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedSourceSamplingBudget_spatial (m A : ℕ)
    (X N : Type*) [Fintype X] [Fintype N]
    {G : Type*} [Fintype G] {dim : ℕ} (s : Fin dim ↪ G)
    {p P E l F : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hl : 0 ≤ l) (hF : 0 ≤ F)
    (hpP : p ≤ P) (hq : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ P)
    (hvars : (Fintype.card (G ⊕ N) : ℝ) ≤ P) (hX : (Fintype.card X : ℝ) ≤ P) :
    let Q := allocatedSourceSamplingBudget m dim A P E l F
    normalizedTupleWidthLog N s p (E + 2) ≤ Q ∧
      normalizedTupleSideLog X N s p (E + 2) l ≤ Q ∧
      (Fintype.card (Option (G ⊕ N) × X) : ℝ) ≤ Q := by
  have hP := hp.trans hpP
  have hG : (Fintype.card G : ℝ) ≤ P := by
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card N)]
  have hN : (Fintype.card N : ℝ) ≤ P := by
    simp only [Fintype.card_sum, Nat.cast_add] at hvars
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card G)]
  obtain ⟨hw, hs⟩ := normalizedTuple_log_envelopes_of_le X N s hp (by linarith : 0 ≤ E + 2)
    hl hpP hq hG hN hX
  obtain ⟨_, _, _, _, _, _, hprod, hwQ, hsQ⟩ := allocatedSourceSamplingBudget_bounds m dim A hP hE hl hF
  refine ⟨hw.trans hwQ, hs.trans hsQ, ?_⟩
  apply le_trans ?_ hprod
  simp only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  exact mul_le_mul (add_le_add hvars le_rfl) hX (Nat.cast_nonneg _) (by linarith)

theorem allocatedSourceSamplingBudget_cutoffs (m dim A : ℕ) {P E l F : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hl : 0 ≤ l) (hF : 0 ≤ F)
    (T Kproj Kideal : ℕ) (hT : 1 ≤ T) (hKproj : 1 ≤ Kproj) (hKideal : 1 ≤ Kideal) :
    let Q := allocatedSourceSamplingBudget m dim A P E l F
    let K := max T (max Kproj Kideal)
    Q ≤ (Q + K) ^ K ∧ (Q + T) ^ T ≤ (Q + K) ^ K ∧
      (Q + Kproj) ^ Kproj ≤ (Q + K) ^ K ∧ (F + Kideal) ^ Kideal ≤ (Q + K) ^ K := by
  intro Q K
  have hb := allocatedSourceSamplingBudget_bounds m dim A hP hE hl hF
  have hQ : 0 ≤ Q := (by norm_num : (0 : ℝ) ≤ 1).trans hb.1
  have hTK : T ≤ K := le_max_left _ _
  have hPK : Kproj ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hIK : Kideal ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have hK : 1 ≤ K := hT.trans hTK
  refine ⟨?_, shifted_power_self_mono hQ hT hTK, shifted_power_self_mono hQ hKproj hPK, ?_⟩
  · have h := shifted_power_self_mono hQ (le_refl 1) hK
    simp only [Nat.cast_one, pow_one] at h
    linarith
  · apply (pow_le_pow_left₀ (by positivity) (add_le_add hb.2.2.2.2.1 le_rfl) Kideal).trans
    exact shifted_power_self_mono hQ hKideal hIK

theorem exists_allocatedSourceSamplingBudget_bound (m dim A : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {P E l F : ℝ}, 0 ≤ P → 0 ≤ E → 0 ≤ l → 0 ≤ F →
      allocatedSourceSamplingBudget m dim A P E l F ≤ (P + E + l + F + a) ^ a := by
  obtain ⟨b, _, hjet⟩ := exists_allocatedJetFourierBudget_bound m dim A
  let poly : Polynomial ℕ := 1 + Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b +
    tupleSideLogEnvelope Polynomial.X (Polynomial.X + 2) Polynomial.X + (Polynomial.X + 1) * Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro P E l F hP hE hl hF
  let R := P + E + l + F
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hPR : P ≤ R := by dsimp [R]; linarith
  have hER : E + 2 ≤ R + 2 := by dsimp [R]; linarith
  have hlR : l ≤ R := by dsimp [R]; linarith
  have hjetR : allocatedJetFourierBudget m dim A P ≤ (R + b) ^ b :=
    (hjet P hP).trans (pow_le_pow_left₀ (by positivity) (add_le_add hPR le_rfl) b)
  have hside := tupleSideLogEnvelope_mono hP (by linarith : 0 ≤ E + 2) hl hPR hER hlR
  have hprod : (P + 1) * P ≤ (R + 1) * R := by gcongr
  have hQ : allocatedSourceSamplingBudget m dim A P E l F ≤
      1 + R + (R + b) ^ b + tupleSideLogEnvelope R (R + 2) R + (R + 1) * R := by
    dsimp only [allocatedSourceSamplingBudget, R] at *
    linarith
  apply hQ.trans
  simpa [poly, R, tupleSideLogEnvelope, tupleLateLogEnvelope, tupleWidthLogEnvelope,
    tupleEarlyLogEnvelope, spatialTupleToleranceLog, spatialDiscretizationEnvelope,
    spatialMeshEnvelope, spatialLipschitzCostEnvelope, spatialLipschitzEnvelope,
    spatialDisplacementEnvelope, spatialFixedProfileEnvelope, anisotropicSpatialCapLog,
    coefficientErrorVolumeLog, Polynomial.eval₂_pow] using hbound R hR

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def allocatedSiteApproximationInput {A : Type*} [Semiring A]
    (m dim : ℕ) (D P E e : A) : A :=
  e + siteReferenceErrorLog m D P (E + 1) + ((m : A) + 2) * (dim : A) + 3

theorem allocatedSiteApproximationInput_bounds (m dim : ℕ) {D P E e : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (he : 0 ≤ e) :
    let p := allocatedSiteApproximationInput m dim D P E e
    0 ≤ p ∧ e ≤ p ∧ siteReferenceErrorLog m D P (E + 1) ≤ p ∧
      ((m : ℝ) + 2) * dim + 3 ≤ p := by
  have hmass := siteReferenceMassLog_nonneg m hD hP
  have herror : 0 ≤ siteReferenceErrorLog m D P (E + 1) := by
    unfold siteReferenceErrorLog
    linarith
  have hbox : 0 ≤ ((m : ℝ) + 2) * dim := by positivity
  dsimp only [allocatedSiteApproximationInput]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedProfileFourierOutput_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedProfileFourierOutput P := by
  have hlog := allocatedProfileErrorLog_nonneg hP
  dsimp only [allocatedProfileFourierOutput, allocatedProfileFourierInput]
  positivity

theorem allocatedSourceSamplingBudget_fourier_mono (m dim A : ℕ) (P E l : ℝ)
    {F H : ℝ} (hFH : F ≤ H) :
    allocatedSourceSamplingBudget m dim A P E l F ≤
      allocatedSourceSamplingBudget m dim A P E l H := by
  unfold allocatedSourceSamplingBudget
  linarith

theorem allocatedSourceSamplingBudget_site_cutoffs (m dim A : ℕ) {P E l F H : ℝ}
    (hP : 0 ≤ P) (hE : 0 ≤ E) (hl : 0 ≤ l) (hF : 0 ≤ F) (hH : 0 ≤ H)
    (T Kproj Kideal Kbuf : ℕ) (hT : 1 ≤ T) (hKbuf : 1 ≤ Kbuf) :
    let Q₀ := allocatedSourceSamplingBudget m dim A P (E + 1) l F
    let Q := allocatedSourceSamplingBudget m dim A P (E + 1) l (F + H)
    let K₀ := max T (max Kproj Kideal)
    let K := max Kbuf K₀
    (Q₀ + K₀) ^ K₀ ≤ (Q + K) ^ K ∧ Q ≤ (Q + K) ^ K ∧
      (Q + Kbuf) ^ Kbuf ≤ (Q + K) ^ K := by
  intro Q₀ Q K₀ K
  have hE1 : 0 ≤ E + 1 := by linarith
  have hQ₀ := (allocatedSourceSamplingBudget_bounds m dim A hP hE1 hl hF).1
  have hQ : 0 ≤ Q := zero_le_one.trans
    (allocatedSourceSamplingBudget_bounds m dim A hP hE1 hl (add_nonneg hF hH)).1
  have hmono : Q₀ ≤ Q := allocatedSourceSamplingBudget_fourier_mono m dim A P (E + 1) l
    (le_add_of_nonneg_right hH)
  have hK₀ : 1 ≤ K₀ := hT.trans (le_max_left _ _)
  have hK : 1 ≤ K := hKbuf.trans (le_max_left _ _)
  refine ⟨?_, ?_, shifted_power_self_mono hQ hKbuf (le_max_left _ _)⟩
  · exact (pow_le_pow_left₀ (by positivity) (add_le_add hmono le_rfl) K₀).trans
      (shifted_power_self_mono hQ hK₀ (le_max_right _ _))
  · have h := shifted_power_self_mono hQ (le_refl 1) hK
    simp only [Nat.cast_one, pow_one] at h
    linarith

end Erdos3.VectorPolynomial

end

end OAI

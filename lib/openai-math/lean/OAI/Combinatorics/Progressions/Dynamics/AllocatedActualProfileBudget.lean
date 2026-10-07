import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealRefinedPointwise
import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileErrorLogBounds

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem diagonalProfileCap_le_exp {Q : Type*} [Fintype Q]
    (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q) {D p e : ℝ} {δ : ℝ≥0}
    (hp : 0 ≤ p) (he : 0 ≤ e) (hcard : (Fintype.card Q : ℝ) ≤ D)
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e) :
    (‖(∏ q, R q)⁻¹‖₊ * δ⁻¹ ^ Fintype.card Q : ℝ≥0) ≤ Real.exp (D * (p + e)) := by
  have hJ : ‖(∏ q, R q)⁻¹‖ ≤ Real.exp (D * p) :=
    (inverseProduct_norm_le_exp R hR hRi).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hcard hp))
  have hpow : ((δ : ℝ)⁻¹) ^ Fintype.card Q ≤ Real.exp (D * e) :=
    pow_le_exp_mul_of_le_exp (inv_nonneg.mpr δ.coe_nonneg) hδ he _ hcard
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_inv, coe_nnnorm]
  calc
    _ ≤ Real.exp (D * p) * Real.exp (D * e) := by gcongr
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

def allocatedActualProfileInput {A : Type*} [Semiring A] (m : ℕ) (D p e g s : A) : A :=
  D + p + g + (layerTailDegree m + 1 : ℕ) * s +
    D * allocatedDensityEnvelope m D p + D * (p + e) +
    allocatedProxyLipEnvelope m D p + allocatedIdealLipEnvelope D p e

theorem allocatedActualProfileInput_bounds (m : ℕ) {D p e g s : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) (hg : 0 ≤ g) (hs : 0 ≤ s) :
    let T := allocatedActualProfileInput m D p e g s
    0 ≤ T ∧ D ≤ T ∧ p ≤ T ∧ g ≤ T ∧ (layerTailDegree m + 1 : ℕ) * s ≤ T ∧
      D * allocatedDensityEnvelope m D p ≤ T ∧ D * (p + e) ≤ T ∧
      allocatedProxyLipEnvelope m D p ≤ T ∧ allocatedIdealLipEnvelope D p e ≤ T := by
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  have hdc : 0 ≤ D * allocatedDensityEnvelope m D p := mul_nonneg hD hd
  have hic : 0 ≤ D * (p + e) := by positivity
  have hsc : 0 ≤ ((layerTailDegree m + 1 : ℕ) : ℝ) * s := by positivity
  have hpl : 0 ≤ allocatedProxyLipEnvelope m D p := by unfold allocatedProxyLipEnvelope; positivity
  have hil : 0 ≤ allocatedIdealLipEnvelope D p e := by unfold allocatedIdealLipEnvelope; positivity
  dsimp only [allocatedActualProfileInput]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

include h

theorem allocatedActualProfile_fourier_budget
    {p e g s δF : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hg : 0 ≤ g) (hs : 0 ≤ s)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    {δ : ℝ≥0} (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp g)
    (hS : (S.value : ℝ) ≤ Real.exp s)
    (C V : Fin m → ℝ≥0) (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hδF : δF⁻¹ ≤ Real.exp p) :
    let active := {a // ¬allocatedGridAxis (I := I) U b S.value a}
    let output := Σ a : active, O a.val.1
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
    let Cp : ℝ≥0 := bound ^ Fintype.card (LayerSamplerAxis I n)
    let Ci : ℝ≥0 := ‖(∏ q : output, R q.1.val.1)⁻¹‖₊ * δ⁻¹ ^ Fintype.card output
    let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound *
      bound ^ Fintype.card (LayerSamplerAxis I n)
    let Ki : ℝ≥0 := ‖(∏ q : output, R q.1.val.1)⁻¹‖₊ *
      (affineProductProfileLip output δ * NNReal.mk (Real.exp p) (Real.exp_pos p).le)
    let T := allocatedActualProfileInput m D p e g s
    let L := allocatedProfileFourierInput T
    let Q := allocatedProfileFourierOutput T
    0 ≤ L ∧ p ≤ Q ∧ (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L ∧
      δF⁻¹ ≤ Real.exp L ∧
      (allocatedProfileErrorLip B U b S (O := O) A Cp Ci Kp Ki C V : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp Q ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := O) A Cp Ci V ≤ Real.exp Q := by
  dsimp only
  obtain ⟨hT, hDT, hpT, hgT, hsT, hcpT, hciT, hkpT, hkiT⟩ :=
    allocatedActualProfileInput_bounds m h.nonneg hp he hg hs
  have hcp : (Real.exp (allocatedDensityLog (G := G) B α O p)) ^ Fintype.card (LayerSamplerAxis I n) ≤
      Real.exp (D * allocatedDensityEnvelope m D p) := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right h.axes (allocatedDensityLog_bounds (G := G) B α O hp).1).trans
      (mul_le_mul_of_nonneg_left (allocatedDensityLog_le_envelope B h hp) h.nonneg)
  have hci := diagonalProfileCap_le_exp
    (fun q : (Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) => R q.1.val.1)
    (fun q => hR q.1.val.1) hp he (h.active_outputs B _) (fun q => hRi q.1.val.1) hδ
  have hki := diagonalProfileLip_le_exp
    (fun q : (Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a}, O a.val.1) => R q.1.val.1)
    (fun q => hR q.1.val.1) hp he (h.active_outputs B _) h.profile (fun q => hRi q.1.val.1) hδ
  have hk : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp (allocatedActualProfileInput m D p e g s) := by
    calc
      _ ≤ Real.exp s ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp ((layerTailDegree m + 1 : ℕ) * s) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsT
  have hbudget := allocatedProfileError_fourier_budget B U b S A
    ((⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩ : ℝ≥0) ^
      Fintype.card (LayerSamplerAxis I n)) _ _ _ C V hT
    (h.degree.trans hDT) (h.axes.trans hDT) (h.outputs.trans hDT)
    (fun j => (h.rows j).trans hDT) (fun j => (hJ j).trans hDT)
    (hA.trans (Real.exp_le_exp.mpr hgT)) hk
    (fun j => (hC j).trans (Real.exp_le_exp.mpr hpT))
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hpT))
    (hcp.trans (Real.exp_le_exp.mpr hcpT))
    (hci.trans (Real.exp_le_exp.mpr hciT))
    ((allocatedProxyLip_le_exp B h hp).trans (Real.exp_le_exp.mpr hkpT))
    (hki.trans (Real.exp_le_exp.mpr hkiT))
    (hδF.trans (Real.exp_le_exp.mpr hpT))
  exact ⟨hbudget.1, hpT.trans hbudget.2.1, hbudget.2.2⟩

end Erdos3.VectorPolynomial

end

end OAI

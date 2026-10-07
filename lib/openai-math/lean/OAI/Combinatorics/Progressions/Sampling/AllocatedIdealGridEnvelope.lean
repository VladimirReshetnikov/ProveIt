import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
import OAI.Combinatorics.Progressions.Estimates.PhysicalActiveIdealSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

section Envelopes

variable {A : Type*} [Semiring A]

def allocatedIdealRadiusEnvelope (m : ℕ) (D p : A) : A :=
  allocatedSupportEnvelope m D p + p + (m + 1) * D + 2

def allocatedProxyLipEnvelope (m : ℕ) (D p : A) : A :=
  D + (D + 1) * allocatedDensityEnvelope m D p

def allocatedIdealLipEnvelope (D p e : A) : A :=
  D * p + 2 * D + (D + 1) * e + p

def allocatedIdealGridEnvelope (m : ℕ) (D p e : A) : A :=
  allocatedIdealRadiusEnvelope m D p + allocatedProxyLipEnvelope m D p +
    allocatedIdealLipEnvelope D p e + 1

def allocatedIdealMeshEnvelope (m : ℕ) (D p e : A) : A :=
  D * (allocatedIdealGridEnvelope m D p e + 4) + allocatedIdealGridEnvelope m D p e

def allocatedIdealVolumeEnvelope (m : ℕ) (D p : A) : A :=
  D * (allocatedSupportEnvelope m D p + 2)

end Envelopes

theorem allocatedIdealGridEnvelope_nonneg (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) :
    0 ≤ allocatedIdealGridEnvelope m D p e := by
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  unfold allocatedIdealGridEnvelope allocatedIdealRadiusEnvelope
    allocatedProxyLipEnvelope allocatedIdealLipEnvelope
  positivity

theorem allocatedIdealGridEnvelope_bounds (m : ℕ) {D p e : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (he : 0 ≤ e) :
    allocatedIdealRadiusEnvelope m D p ≤ allocatedIdealGridEnvelope m D p e ∧
    allocatedProxyLipEnvelope m D p + allocatedIdealLipEnvelope D p e + 1 ≤
      allocatedIdealGridEnvelope m D p e := by
  have hs := allocatedSupportEnvelope_nonneg m hD hp
  have hd := allocatedDensityEnvelope_nonneg m hD hp
  have hr : 0 ≤ allocatedIdealRadiusEnvelope m D p := by
    unfold allocatedIdealRadiusEnvelope; positivity
  have hpr : 0 ≤ allocatedProxyLipEnvelope m D p := by
    unfold allocatedProxyLipEnvelope; positivity
  have hi : 0 ≤ allocatedIdealLipEnvelope D p e := by
    unfold allocatedIdealLipEnvelope; positivity
  unfold allocatedIdealGridEnvelope
  constructor <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D p : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D) (hp : 0 ≤ p)

include h hp

theorem allocatedIdealRadius_le_exp :
    (Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O p))
      (Real.exp p * (partitionedIdealRadius α m + 1))) : ℝ) ≤
      Real.exp (allocatedIdealRadiusEnvelope m D p) := by
  have hs := allocatedSupportEnvelope_nonneg m h.nonneg hp
  have hD := h.nonneg
  apply coe_toNNReal_le_exp
  apply max_le
  · apply Real.exp_le_exp.mpr
    apply (allocatedJetSupportLog_le_envelope B h hp).trans
    unfold allocatedIdealRadiusEnvelope
    nlinarith [Nat.cast_nonneg m (α := ℝ)]
  · calc
      _ ≤ Real.exp p * Real.exp (((m : ℝ) + 1) * (Fintype.card α : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left (partitionedIdealRadius_add_one_le_exp α m) (Real.exp_pos p).le
      _ = Real.exp (p + ((m : ℝ) + 1) * (Fintype.card α : ℝ) + 2) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hc := mul_le_mul_of_nonneg_left h.cube (show 0 ≤ (m : ℝ) + 1 by positivity)
        unfold allocatedIdealRadiusEnvelope
        linarith

theorem allocatedProxyLip_le_exp :
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
    ((Fintype.card (LayerSamplerAxis I n) : ℝ≥0) * bound *
      bound ^ Fintype.card (LayerSamplerAxis I n) : ℝ≥0) ≤
      Real.exp (allocatedProxyLipEnvelope m D p) := by
  dsimp only
  simp only [NNReal.coe_mul]
  apply (jointDensityLip_le_exp _ _).trans
  apply Real.exp_le_exp.mpr
  have hd := (allocatedDensityLog_bounds (G := G) B α O hp).1
  have hb := allocatedDensityLog_le_envelope B h hp
  have ha := h.axes
  have hD := h.nonneg
  unfold allocatedProxyLipEnvelope
  gcongr

theorem allocatedCoefficientErrorVolume_le_exp :
    (2 * Real.exp (allocatedJetSupportLog (G := G) B α O p) + 1) ^
      Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) ≤
      Real.exp (allocatedIdealVolumeEnvelope m D p) := by
  have hv := (allocatedJetTestAccuracy_spec (G := G) B α O hp
    (η := 1) (E := 0) (by norm_num) (by norm_num) (by simp)).2.2.1
  have ht := hv.trans (Real.exp_le_exp.mpr (allocatedJetTestLog_le_envelope B h hp))
  simpa only [one_div, inv_inv, allocatedTestEnvelope, zero_add,
    allocatedIdealVolumeEnvelope] using ht

theorem allocatedIdealGridAllowance_le_exp {Q J : Type*} [Fintype Q] [Fintype J]
    (s : J ↪ Q) (R : Q → ℝ) (hR : ∀ q, 0 ≤ R q)
    {δ : ℝ≥0} {e : ℝ} (he : 0 ≤ e)
    (hQ : (Fintype.card Q : ℝ) ≤ D)
    (hRi : ∀ q, (R q)⁻¹ ≤ Real.exp p) (hδ : (δ : ℝ)⁻¹ ≤ Real.exp e) :
    let bound : ℝ≥0 := ⟨Real.exp (allocatedDensityLog (G := G) B α O p), (Real.exp_pos _).le⟩
    let Kp : ℝ≥0 := Fintype.card (LayerSamplerAxis I n) * bound *
      bound ^ Fintype.card (LayerSamplerAxis I n)
    let Ki : ℝ≥0 := ‖(∏ q, R q)⁻¹‖₊ *
      (affineProductProfileLip Q δ * NNReal.mk (Real.exp p) (Real.exp_pos p).le)
    let Ro := Real.toNNReal (max (Real.exp (allocatedJetSupportLog (G := G) B α O p))
      (Real.exp p * (partitionedIdealRadius α m + 1)))
    mixedOutputGridAllowance s Ro ((Kp : ℝ) + Ki) ≤
      Real.exp (allocatedIdealMeshEnvelope m D p e) := by
  dsimp only
  have hg := allocatedIdealGridEnvelope_bounds m h.nonneg hp he
  have hr := (allocatedIdealRadius_le_exp B h hp).trans (Real.exp_le_exp.mpr hg.1)
  have hk := (add_le_exp_add_one
    (show 0 ≤ allocatedProxyLipEnvelope m D p by
      have hd := allocatedDensityEnvelope_nonneg m h.nonneg hp
      have hD := h.nonneg
      unfold allocatedProxyLipEnvelope; positivity)
    (show 0 ≤ allocatedIdealLipEnvelope D p e by
      have hD := h.nonneg
      unfold allocatedIdealLipEnvelope; positivity)
    (allocatedProxyLip_le_exp B h hp)
    (diagonalProfileLip_le_exp R hR hp he hQ h.profile hRi hδ)).trans
      (Real.exp_le_exp.mpr hg.2)
  apply (mixedOutputGridAllowance_le_exp s (NNReal.coe_nonneg _) (by positivity)
    (allocatedIdealGridEnvelope_nonneg m h.nonneg hp he) hr hk).trans
  apply Real.exp_le_exp.mpr
  unfold allocatedIdealMeshEnvelope
  have hL : 0 ≤ allocatedIdealGridEnvelope m D p e + 4 := by
    linarith [allocatedIdealGridEnvelope_nonneg m h.nonneg hp he]
  exact add_le_add (mul_le_mul_of_nonneg_right hQ hL) le_rfl

end Erdos3.VectorPolynomial

end

end OAI

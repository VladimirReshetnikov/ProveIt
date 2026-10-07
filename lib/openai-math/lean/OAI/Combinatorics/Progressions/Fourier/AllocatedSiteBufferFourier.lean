import OAI.Combinatorics.Progressions.Estimates.AllocatedSiteBufferLog

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical BigOperators NNReal

def allocatedSiteBufferInput {A : Type*} [Semiring A] (m : ℕ) (D p g s c : A) : A :=
  D + p + g + (layerTailDegree m + 1 : ℕ) * s + D * p + (D * p + D + c + p) + 4

theorem allocatedSiteBufferInput_bounds (m : ℕ) {D p g s c : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hg : 0 ≤ g) (hs : 0 ≤ s) (hc : 0 ≤ c) :
    let T := allocatedSiteBufferInput m D p g s c
    0 ≤ T ∧ D ≤ T ∧ p ≤ T ∧ g ≤ T ∧ (layerTailDegree m + 1 : ℕ) * s ≤ T ∧
      D * p ≤ T ∧ D * p + D + c + p ≤ T ∧ 4 ≤ T := by
  have hprod : 0 ≤ D * p := mul_nonneg hD hp
  have hscale : 0 ≤ (layerTailDegree m + 1 : ℕ) * s := mul_nonneg (Nat.cast_nonneg _) hs
  dsimp only [allocatedSiteBufferInput]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "invVolume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))⁻¹

theorem allocatedSiteBuffer_fourier_budget {D p g s : ℝ}
    (h : AllocatedComparisonDimensions (G := G) B α jets D)
    (hp : 0 ≤ p) (hg : 0 ≤ g) (hs : 0 ≤ s)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (hR : ∀ j, 0 ≤ R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p)
    (A : ℝ≥0) (hA : (A : ℝ) ≤ Real.exp g)
    (hS : (S.value : ℝ) ≤ Real.exp s)
    (C V : Fin m → ℝ≥0) (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p) :
    let cap : ℝ≥0 := ‖invVolume‖₊
    let lip := allocatedSiteBufferLip (α := α) B U b S ⟨Real.exp p, (Real.exp_pos p).le⟩
    let T := allocatedSiteBufferInput m D p g s (normalizedSiteCutoffBound : ℝ)
    let L := allocatedProfileFourierInput T
    let Q := allocatedProfileFourierOutput T
    0 ≤ L ∧ 4 ≤ Q ∧ p ≤ Q ∧ D ≤ Q ∧ (Fintype.card (JetAmbientIndex jets J) : ℝ) ≤ L ∧
      (1 / 4 : ℝ)⁻¹ ≤ Real.exp L ∧
      (allocatedProfileErrorLip B U b S (O := jets) A cap 0 lip 0 C V : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp Q ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := jets) A cap 0 V ≤ Real.exp Q := by
  dsimp only
  obtain ⟨hT, hDT, hpT, hgT, hsT, hcapT, hlipT, h4T⟩ :=
    allocatedSiteBufferInput_bounds m h.nonneg hp hg hs normalizedSiteCutoffBound.coe_nonneg
  have hcap := allocatedSiteBuffer_cap_le_exp (α := α) B U b S hp (h.active_outputs B _) hR hRi
  have hlip := allocatedSiteBuffer_lip_le_exp (α := α) B U b S hp (h.active_outputs B _) hR hRi
  have hscale : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      Real.exp (allocatedSiteBufferInput m D p g s (normalizedSiteCutoffBound : ℝ)) := by
    calc
      _ ≤ (Real.exp s) ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp ((layerTailDegree m + 1 : ℕ) * s) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsT
  have hquarter : (1 / 4 : ℝ)⁻¹ ≤
      Real.exp (allocatedSiteBufferInput m D p g s (normalizedSiteCutoffBound : ℝ)) := by
    norm_num
    linarith [Real.add_one_le_exp (allocatedSiteBufferInput m D p g s (normalizedSiteCutoffBound : ℝ))]
  obtain ⟨hL, hTQ, hamb, hδ, hLip, hfreq, hcoeff⟩ :=
    allocatedProfileError_fourier_budget (O := jets) B U b S A ‖invVolume‖₊ 0
      (allocatedSiteBufferLip (α := α) B U b S ⟨Real.exp p, (Real.exp_pos p).le⟩) 0 C V hT
      (h.degree.trans hDT) (h.axes.trans hDT) (h.outputs.trans hDT)
      (fun j => (h.rows j).trans hDT) (fun j => (hJ j).trans hDT)
      (hA.trans (Real.exp_le_exp.mpr hgT)) hscale
      (fun j => (hC j).trans (Real.exp_le_exp.mpr hpT))
      (fun j => (hV j).trans (Real.exp_le_exp.mpr hpT))
      (hcap.trans (Real.exp_le_exp.mpr hcapT)) (by exact (Real.exp_pos _).le)
      (hlip.trans (Real.exp_le_exp.mpr hlipT)) (by exact (Real.exp_pos _).le) hquarter
  exact ⟨hL, h4T.trans hTQ, hpT.trans hTQ, hDT.trans hTQ, hamb, hδ, hLip, hfreq, hcoeff⟩

end Erdos3.VectorPolynomial

end

end OAI

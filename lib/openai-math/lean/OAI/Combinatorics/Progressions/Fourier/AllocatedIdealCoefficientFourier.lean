import OAI.Combinatorics.Progressions.Dynamics.AllocatedActualProfileBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {D : ℝ} (h : AllocatedComparisonDimensions (G := G) B α O D)
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

include h

theorem allocatedIdealCoefficient_fourier_budget
    {p e g s δF : ℝ} (hp : 0 ≤ p) (he : 0 ≤ e) (hg : 0 ≤ g) (hs : 0 ≤ s)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ D)
    (η A : ℝ≥0) (hη : η ≤ 1) (hA : (A : ℝ) ≤ Real.exp g)
    (hS : (S.value : ℝ) ≤ Real.exp s)
    (C V : Fin m → ℝ≥0) (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    (hV : ∀ j, (V j : ℝ) ≤ Real.exp p) (hδF : δF⁻¹ ≤ Real.exp p) :
    let T := allocatedActualProfileInput m D p e g s
    let L := allocatedProfileFourierInput T
    let Q := allocatedProfileFourierOutput T
    0 ≤ L ∧ p ≤ Q ∧ (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L ∧
      δF⁻¹ ≤ Real.exp L ∧
      (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp Q ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) *
        allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp Q := by
  dsimp only
  obtain ⟨hT, hDT, hpT, hgT, hsT, _hcap, _hideal, _hproxyLip, _hidealLip⟩ :=
    allocatedActualProfileInput_bounds m h.nonneg hp he hg hs
  have hk : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤
      Real.exp (allocatedActualProfileInput m D p e g s) := by
    calc
      _ ≤ Real.exp s ^ (layerTailDegree m + 1) := pow_le_pow_left₀ (Nat.cast_nonneg _) hS _
      _ = Real.exp ((layerTailDegree m + 1 : ℕ) * s) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsT
  obtain ⟨hL, hQ, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedProfileError_fourier_budget B U b S (O := O) A 1 0 0 0 C V hT
      (h.degree.trans hDT) (h.axes.trans hDT) (h.outputs.trans hDT)
      (fun j => (h.rows j).trans hDT) (fun j => (hJ j).trans hDT)
      (hA.trans (Real.exp_le_exp.mpr hgT)) hk
      (fun j => (hC j).trans (Real.exp_le_exp.mpr hpT))
      (fun j => (hV j).trans (Real.exp_le_exp.mpr hpT))
      (Real.one_le_exp hT) (Real.exp_nonneg _) (Real.exp_nonneg _) (Real.exp_nonneg _)
      (hδF.trans (Real.exp_le_exp.mpr hpT))
  simp only [allocatedProfileErrorLip, add_zero, zero_add, zero_mul, mul_zero, one_mul] at hLip
  simp only [allocatedProfileErrorCap, add_zero, mul_one] at hcoeff
  have hLipMono : allocatedErrorKernelLip B U b S (O := O) η A C V ≤
      allocatedErrorKernelLip B U b S (O := O) 1 A C V := by
    dsimp only [allocatedErrorKernelLip]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hη zero_le) zero_le)
      zero_le
  have hCapMono : allocatedErrorKernelCap B U b S (O := O) η A V ≤
      allocatedErrorKernelCap B U b S (O := O) 1 A V := by
    dsimp only [allocatedErrorKernelCap]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hη zero_le) zero_le)
      zero_le
  exact ⟨hL, hpT.trans hQ, hamb, hδL, (NNReal.coe_le_coe.mpr hLipMono).trans hLip,
    hfreq, (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hCapMono)
      (Real.exp_pos _).le).trans hcoeff⟩

end Erdos3.VectorPolynomial

end

end OAI

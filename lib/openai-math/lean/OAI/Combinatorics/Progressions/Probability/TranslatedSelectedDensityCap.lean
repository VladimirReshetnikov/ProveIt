import OAI.Combinatorics.Progressions.Sampling.ExplicitSpatialSampler

namespace OAI

section

namespace Erdos3

noncomputable def selectedDensityLog (m : ℕ) (P : ℝ) : ℝ :=
  (P + VectorPolynomial.selectedFourierExponent m)^VectorPolynomial.selectedFourierExponent m + 1

theorem selectedDensityLog_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ selectedDensityLog m P := by
  unfold selectedDensityLog
  positivity

namespace VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
variable (L₀ : ℕ) {P : ℝ} (hP : 0 ≤ P)
variable (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
variable (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
variable (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
variable (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
variable (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
variable (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)

include hC hV hσ1 hCinv hchart hsmall hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP in
theorem selectedCoefficientDensity_le_exp
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    selectedCoefficientDensity B U b hb o R σ hR hσ L₀ x ≤ Real.exp (selectedDensityLog m P) := by
  obtain ⟨F, inst, frequency, c, _, _, hc, herr⟩ :=
    exists_selected_coefficient_uniform_fourier B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP
      (δ := 1) (by norm_num) (by simpa using Real.one_le_exp_iff.mpr hP)
  let _ := inst
  let E := (P + selectedFourierExponent m)^selectedFourierExponent m
  have hcap : selectedCoefficientDensity B U b hb o R σ hR hσ L₀ x ≤ 1 + Real.exp E :=
    coefficientDensity_cap_of_fourier U _ frequency c hc herr x
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have h1 : 1 ≤ Real.exp E := Real.one_le_exp_iff.mpr hE
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ ≤ 1 + Real.exp E := hcap
    _ ≤ Real.exp E * 2 := by linarith
    _ ≤ Real.exp E * Real.exp 1 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    _ = Real.exp (selectedDensityLog m P) := (Real.exp_add E 1).symm

include hC hV hσ1 hCinv hchart hsmall hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP in
theorem selectedPhysicalDensity_le_exp {X : Type*}
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    selectedPhysicalDensity B U b hb o R σ hR hσ L₀ p hm z ≤ Real.exp (selectedDensityLog m P) :=
  selectedCoefficientDensity_le_exp B U b hb o C V hC hV R σ hR hσ hσ1 Cinv hCinv
    hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP _

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
variable (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
variable (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
variable (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
variable (L₀ : ℕ) {P : ℝ} (hP : 0 ≤ P)
variable (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
variable (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
variable (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
variable (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
variable (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
variable (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)

include hC hV hσ1 hCinv hchart hsmall hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP in
theorem translatedSelectedPhysicalDensity_le_exp {X : Type*}
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
    translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ center p hm z ≤
      Real.exp (selectedDensityLog m P) :=
  selectedCoefficientDensity_le_exp B U b hb o C V hC hV R σ hR hσ hσ1 Cinv hCinv
    hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP _

end Erdos3.VectorPolynomial

end

end OAI

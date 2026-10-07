import OAI.Combinatorics.Progressions.Fourier.AllocatedMaskedCoefficientFourier
import OAI.Combinatorics.Progressions.Probability.CanonicalCoverLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {K F G : Type*} [Fintype K] [Fintype F] [Fintype G] {m : ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientTorusCharacter_frequency_add
    (frequency₁ frequency₂ : ∀ j, (K →₀ ℕ) → J j → ℤ)
    (x : CoefficientTorus (K := K) U) :
    coefficientTorusCharacter U (frequency₁ + frequency₂) x =
      coefficientTorusCharacter U frequency₁ x * coefficientTorusCharacter U frequency₂ x := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  simp only [coefficientTorusCharacter_mk]
  have hsum : coefficientArrayFunctional U (frequency₁ + frequency₂) y =
      coefficientArrayFunctional U frequency₁ y + coefficientArrayFunctional U frequency₂ y := by
    change (∑ s : CoefficientSlot K m, ∑ a,
      ((frequency₁ s.1 s.2.val a + frequency₂ s.1 s.2.val a : ℤ) : ℝ) * (y s).val a) =
      (∑ s : CoefficientSlot K m, ∑ a, (frequency₁ s.1 s.2.val a : ℝ) * (y s).val a) +
        ∑ s : CoefficientSlot K m, ∑ a, (frequency₂ s.1 s.2.val a : ℝ) * (y s).val a
    simp only [Int.cast_add, add_mul, Finset.sum_add_distrib]
  rw [hsum, AddCircle.coe_add, CircleFourier.character_add]

theorem coefficientTorusFourierSum_mul
    (frequency₁ : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c₁ : F → ℂ)
    (frequency₂ : G → ∀ j, (K →₀ ℕ) → J j → ℤ) (c₂ : G → ℂ)
    (x : CoefficientTorus (K := K) U) :
    coefficientTorusFourierSum U frequency₁ c₁ x * coefficientTorusFourierSum U frequency₂ c₂ x =
      coefficientTorusFourierSum U (fun a : F × G => frequency₁ a.1 + frequency₂ a.2)
        (fun a => c₁ a.1 * c₂ a.2) x := by
  simp only [coefficientTorusFourierSum, Fintype.sum_prod_type,
    coefficientTorusCharacter_frequency_add, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem coefficientFourierProduct_mass (c₁ : F → ℂ) (c₂ : G → ℂ) :
    (∑ a : F × G, ‖c₁ a.1 * c₂ a.2‖) = (∑ a, ‖c₁ a‖) * ∑ b, ‖c₂ b‖ := by
  simp only [Fintype.sum_prod_type, norm_mul, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem coefficientFourierProduct_mass_le (c₁ : F → ℂ) (c₂ : G → ℂ)
    {C₁ C₂ : ℝ} (hc₁ : (∑ a, ‖c₁ a‖) ≤ C₁) (hc₂ : (∑ b, ‖c₂ b‖) ≤ C₂) :
    (∑ a : F × G, ‖c₁ a.1 * c₂ a.2‖) ≤ C₁ * C₂ := by
  rw [coefficientFourierProduct_mass]
  exact mul_le_mul hc₁ hc₂ (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
    ((Finset.sum_nonneg (fun _ _ => norm_nonneg _)).trans hc₁)

omit [Fintype K] [Fintype F] [Fintype G] [∀ j, Fintype (J j)] in
theorem coefficientFourierProduct_frequency_bound
    (frequency₁ : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (frequency₂ : G → ∀ j, (K →₀ ℕ) → J j → ℤ) {M₁ M₂ : ℝ}
    (h₁ : ∀ a j d, d.degree ≤ j.val + 1 → ∀ i, |(frequency₁ a j d i : ℝ)| ≤ M₁)
    (h₂ : ∀ b j d, d.degree ≤ j.val + 1 → ∀ i, |(frequency₂ b j d i : ℝ)| ≤ M₂) :
    ∀ a : F × G, ∀ j d, d.degree ≤ j.val + 1 → ∀ i,
      |((frequency₁ a.1 + frequency₂ a.2) j d i : ℝ)| ≤ M₁ + M₂ := by
  intro a j d hd i
  simp only [Pi.add_apply, Int.cast_add]
  exact (abs_add_le _ _).trans (add_le_add (h₁ a.1 j d hd i) (h₂ a.2 j d hd i))

theorem coefficientFourierProduct_approximation
    (D : CoefficientTorus (K := K) U → ℝ) (f : CoefficientTorus (K := K) U → ℂ)
    (frequencyD : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (cD : F → ℂ)
    (frequencyF : G → ∀ j, (K →₀ ℕ) → J j → ℤ) (cF : G → ℂ)
    {ηD ηf : ℝ}
    (hD : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequencyD cD x‖ ≤ ηD)
    (hf : ∀ x, ‖f x‖ ≤ 1)
    (happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequencyF cF x‖ ≤ ηf)
    (x : CoefficientTorus (K := K) U) :
    ‖(D x : ℂ) * f x -
      coefficientTorusFourierSum U (fun a : F × G => frequencyD a.1 + frequencyF a.2)
        (fun a => cD a.1 * cF a.2) x‖ ≤ ηD + (∑ a, ‖cD a‖) * ηf := by
  rw [← coefficientTorusFourierSum_mul]
  let PD := coefficientTorusFourierSum U frequencyD cD x
  let Pf := coefficientTorusFourierSum U frequencyF cF x
  have heq : (D x : ℂ) * f x - PD * Pf = ((D x : ℂ) - PD) * f x + PD * (f x - Pf) := by ring
  change ‖(D x : ℂ) * f x - PD * Pf‖ ≤ _
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_left (hf x) (norm_nonneg _)).trans_eq (mul_one _)).trans (hD x)
  · rw [norm_mul]
    exact mul_le_mul (coefficientTorusFourierSum_norm_le U frequencyD cD x) (happrox x)
      (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

theorem selectedLayerSamplerScale_input_bound (R σ : Fin m → ℝ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (L₀ : ℕ)
    {P : ℝ} (hP : 0 ≤ P) (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hn : ∀ j, (n j : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hL₀ : (L₀ : ℝ) ≤ Real.exp P) :
    ((selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀).value : ℝ) ≤
      Real.exp (selectedFourierInputBudget m P) := by
  have hPT := le_selectedScaleDimensionBudget m hP
  have he := Real.exp_le_exp.mpr hPT
  apply selectedLayerSamplerScale_exp_bound B U b R σ hR hσ L₀
    (selectedScaleDimensionBudget_nonneg m hP) (degree_le_selectedScaleDimensionBudget m hP)
    (fun j => (hn j).trans hPT) (fun j => (hRP j).trans he) (fun j => (hσP j).trans he)
    _ (hA.trans he) (hL₀.trans he)
  intro j
  exact coefficientCount_le_selectedScaleDimensionBudget m (by omega) hP hK

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_selected_coefficient_uniform_fourier (R σ : Fin m → ℝ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P) :
    let S := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    let E := (P+selectedFourierExponent m)^selectedFourierExponent m
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp E ∧
      (∀ t j d, d.degree ≤ j.val+1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp E) ∧
      (∑ t, ‖a t‖) ≤ Real.exp E ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  let S := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
  have hT := selectedScaleDimensionBudget_nonneg m hP
  have hTQ := le_allocatedScaleLog hT
  have hQ := selectedFourierInputBudget_nonneg m hP
  have hPQ := le_selectedFourierInputBudget m hP
  have he := Real.exp_le_exp.mpr hPQ
  have hcount (j : Fin m) :
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤
        selectedFourierInputBudget m P :=
    (coefficientCount_le_selectedScaleDimensionBudget m (by omega) hP hK).trans hTQ
  have hLP := selectedLayerSamplerScale_input_bound B U b R σ hR hσ L₀ hP hK hn hRP hσP hAP hL₀P
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_allocated_coefficient_uniform_fourier B U b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hQ
      ((degree_le_selectedScaleDimensionBudget m hP).trans hTQ) (hK.trans hPQ)
      (fun j => (hRP j).trans he) (fun j => (hσP j).trans he) hcount
      (fun j => (hI j).trans hPQ) (fun j => (hn j).trans hPQ) (fun j => (hJ j).trans hPQ)
      (hAP.trans he) hLP (fun j => (hCP j).trans he) (fun j => (hVP j).trans he) hδ (hδP.trans he)
  let _ := inst
  have hd := allocatedFourierOutputBudget_dominates m hQ
  have hout := selectedFourierOutputBudget_bound m hP
  refine ⟨F, inst, frequency, a, ?_, ?_, ?_, herr⟩
  · exact hcard.trans (Real.exp_le_exp.mpr (hd.1.trans hout))
  · intro t j d hdg i
    exact (hfreq t j d hdg i).trans (Real.exp_le_exp.mpr (hd.2.1.trans hout))
  · exact hsum.trans (Real.exp_le_exp.mpr (hd.2.2.trans hout))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators Classical NNReal

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

include hC hV in
theorem exists_selected_density_ambient_product_fourier (R σ : Fin m → ℝ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (hP : 0 ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (cover : ℕ)
    (f : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → UnitAddCircle) → ℂ)
    (Lf : ℝ≥0) (hf : LipschitzWith Lf f) (hfb : ∀ x, ‖f x‖ ≤ 1)
    {η Q : ℝ} (hη : 0 < η) (hQ : 0 ≤ Q)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ Q)
    (hLf : (Lf : ℝ) ≤ Real.exp Q) (hηQ : η⁻¹ ≤ Real.exp Q) :
    let S := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    let ED := (P + selectedFourierExponent m) ^ selectedFourierExponent m
    let EF := 2 * Q * (2 * Q + 2) ^ 4
    ∃ (T : Type) (inst : Fintype T), letI := inst
    ∃ (frequency : T → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
      (a : T → ℂ),
      (Fintype.card T : ℝ) ≤ Real.exp ED * Real.exp EF ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ cover * Real.exp ED + Real.exp ((2 * Q + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp ED * Real.exp EF ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S
        (quotientIntegerCover (coefficientIntegerLattice U) cover x) : ℂ) *
          f (coefficientAmbientTorus U x) - coefficientTorusFourierSum U frequency a x‖ ≤
            δ + Real.exp ED * η := by
  dsimp only
  obtain ⟨FD, instD, frequencyD, cD, hcardD, hfreqD, hmassD, happD⟩ :=
    exists_selected_coefficient_uniform_fourier B U b hb o C V hC hV R σ hR hσ hσ1
      Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP hδ hδP
  let _ := instD
  obtain ⟨FF, instF, frequencyF, cF, hcardF, hfreqF, hmassF, happF⟩ :=
    exists_ambient_torus_fourier_approximation f Lf 1 hf hfb hη hQ hdim hLf hηQ
  let _ := instF
  let fD := fun a => dilateCoefficientFrequency cover (frequencyD a)
  let fF := fun a => coefficientSlotFrequency (fun s i => frequencyF a ⟨s, i⟩)
  refine ⟨FD × FF, inferInstance, fun a => fD a.1 + fF a.2,
    fun a => cD a.1 * cF a.2, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_prod, Nat.cast_mul]
    exact mul_le_mul hcardD hcardF (Nat.cast_nonneg _) (Real.exp_nonneg _)
  · intro a j d hd i
    change |((fD a.1 j d i + fF a.2 j d i : ℤ) : ℝ)| ≤ _
    rw [Int.cast_add]
    exact (abs_add_le _ _).trans (add_le_add
      (dilateCoefficientFrequency_bound cover (frequencyD a.1) (hfreqD a.1) j d hd i)
      (coefficientSlotFrequency_bound _ (fun s i => hfreqF a.2 ⟨s, i⟩) j d hd i))
  · apply coefficientFourierProduct_mass_le cD cF hmassD
    simpa only [NNReal.coe_one, mul_one] using hmassF
  · intro x
    have hD := coefficientCover_density_approximation U cover _ frequencyD cD happD
    have hF (y : CoefficientTorus (K := LayerSamplerVariables G I n B) U) : ‖f (coefficientAmbientTorus U y) - coefficientTorusFourierSum U fF cF y‖ ≤ η := by
      simpa only [coefficientAmbientTorus_character, coefficientTorusFourierSum, fF] using
        happF (coefficientAmbientTorus U y)
    exact (coefficientFourierProduct_approximation U _ (fun y => f (coefficientAmbientTorus U y))
      fD cD fF cF hD (fun y => hfb _) hF x).trans
        (add_le_add le_rfl (mul_le_mul_of_nonneg_right hmassD hη.le))

end Erdos3.VectorPolynomial

end

end OAI

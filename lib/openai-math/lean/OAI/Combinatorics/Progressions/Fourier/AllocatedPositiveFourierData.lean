import OAI.Combinatorics.Progressions.Dynamics.PositiveComparisonDataBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)

include hC hV in
theorem exists_allocated_positive_fourier_data (q : ℕ)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp p) (hLP : (S.value : ℝ) ≤ Real.exp p)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp p) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp p) :
    let Q := positiveComparisonDataBudget m q p
    let b := allocatedFourierLogBudget m (2 * p + 4)
    ((allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ≤ Real.exp b) ∧
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (coeff : F → ℂ),
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp Q) ∧
      (∑ t, ‖coeff t‖) ≤ Real.exp Q ∧
      ∀ z, ‖(allocatedCoefficientDensity B U basis hb o hR hσ S z : ℂ) -
        coefficientTorusFourierSum U frequency coeff z‖ ≤ positiveProjectionAccuracy p := by
  let P := 2 * p + 4
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hE := Real.exp_le_exp.mpr hpP
  have hdata := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP (hm.trans hpP) (hK.trans hpP) hR hσ
    (fun j => (hRP j).trans hE) (fun j => (hσP j).trans hE)
    (fun j => (hcount j).trans hpP) (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP)
    (fun j => (hJ j).trans hpP) (hAP.trans hE) (hLP.trans hE)
    (fun j => (hCP j).trans hE) (fun j => (hVP j).trans hE)
  refine ⟨hdata.2.2.1, ?_⟩
  obtain ⟨F, inst, frequency, coeff, _, hfreq, hcoeff, happ⟩ :=
    exists_allocated_coefficient_uniform_fourier B U basis hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hP (hm.trans hpP) (hK.trans hpP)
      (fun j => (hRP j).trans hE) (fun j => (hσP j).trans hE)
      (fun j => (hcount j).trans hpP) (fun j => (hI j).trans hpP) (fun j => (hn j).trans hpP)
      (fun j => (hJ j).trans hpP) (hAP.trans hE) (hLP.trans hE)
      (fun j => (hCP j).trans hE) (fun j => (hVP j).trans hE)
      (show 0 < positiveProjectionAccuracy p from Real.exp_pos _)
      (by simp only [positiveProjectionAccuracy, Real.exp_neg, inv_inv]; exact le_rfl)
  let _ := inst
  have hQ := (positiveComparisonDataBudget_bounds m q hp).2.2.2.1
  have hF := allocatedFourierOutputBudget_dominates m hP
  refine ⟨F, inst, frequency, coeff, ?_, ?_, happ⟩
  · exact fun t j d hd i => (hfreq t j d hd i).trans (Real.exp_le_exp.mpr (hF.2.1.trans hQ))
  · exact hcoeff.trans (Real.exp_le_exp.mpr (hF.2.2.trans hQ))

end Erdos3.VectorPolynomial

end

end OAI

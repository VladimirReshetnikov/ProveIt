import OAI.Combinatorics.Progressions.Dynamics.CoefficientAmbientBudget
import OAI.Combinatorics.Progressions.Geometry.GeometricRetainedCommonCover
import OAI.Combinatorics.Progressions.Lattices.MaskedIntegerPeriodization
import OAI.Combinatorics.Progressions.Probability.AllocatedJointAmbientDensity

namespace OAI

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
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem allocatedCoefficientAmbientDensity_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
    let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    (∀ x, 0 ≤ allocatedCoefficientAmbientDensity B U b o S x ∧
      allocatedCoefficientAmbientDensity B U b o S x ≤ (A : ℝ)^N) ∧
    LipschitzWith (N * L * A^N) (allocatedCoefficientAmbientDensity B U b o S) := by
  have h := allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ
  exact coefficientAmbientDensity_bounds U b o _ _ _
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2)

include hC hV in
theorem exists_allocated_coefficient_fourier_approximation
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ P)
    (hLP : let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
      let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
      let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
      ((N * L * A^N : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have h := allocatedAmbientFactor_bounds B U b S o C V hC hV hR hσ
  exact exists_coefficient_ambient_fourier_approximation U b hb o _ _ _ _
    (fun j i d => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 Cinv hCinv hchart hsmall)
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2) hδ hP hdim hLP hδP

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

noncomputable def coefficientAmbientBudgetExponent (m : ℕ) : ℕ :=
  (exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)).choose

theorem coefficientAmbientBudgetExponent_bound (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) * (m+1) * (P+1)^m * (P+1) + P + 1 ≤
      (P + coefficientAmbientBudgetExponent m)^coefficientAmbientBudgetExponent m := by
  simpa [coefficientAmbientInputPolynomial, coefficientAmbientBudgetExponent, Polynomial.eval₂_pow]
    using (exists_natPolynomial_eval_budget (coefficientAmbientInputPolynomial m)).choose_spec.2 P hP

noncomputable def allocatedFourierLogBudget (m : ℕ) (P : ℝ) : ℝ :=
  (P + allocatedAmbientLog m P + coefficientAmbientBudgetExponent m)^coefficientAmbientBudgetExponent m

theorem allocatedFourierLogBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedFourierLogBudget m P := by
  have h := allocatedAmbientLog_nonneg m hP
  unfold allocatedFourierLogBudget
  positivity

theorem exists_allocatedFourierLogBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedFourierLogBudget m P ≤ (P+a)^a := by
  let e := coefficientAmbientBudgetExponent m
  let scalar : Polynomial ℕ := 7 * (Polynomial.C (layerTailDegree m+1) * (4 * (Polynomial.X+8)) + 8)
  let common : Polynomial ℕ := Polynomial.X + Polynomial.X * scalar + 1
  let width : Polynomial ℕ := Polynomial.C (m+4) * (Polynomial.X+8)
  let mixed : Polynomial ℕ := (2*Polynomial.X+1)*(width+common)+3*Polynomial.X+1
  let ambient : Polynomial ℕ := Polynomial.X + Polynomial.X*(2*mixed+4*Polynomial.X+9)+1
  let budget : Polynomial ℕ := (Polynomial.X+ambient+Polynomial.C e)^e
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨a, ha, ?_⟩
  intro P hP
  simpa [budget, ambient, mixed, width, common, scalar, e, allocatedFourierLogBudget,
    allocatedAmbientLog, allocatedMixedLog, allocatedWidthLog, allocatedCommonLog,
    allocatedScalarLog, integerInterpolationLogEnvelope, Polynomial.eval₂_pow] using hbound P hP

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

theorem allocatedCoefficient_fourier_input_budget
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (R σ : Fin m → ℝ) (L : ℕ) (hL : 0 < L) (C V : Fin m → ℝ≥0)
    {P : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (L : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    let A := allocatedAmbientFactorCap (G := G) B R σ L V
    let F := allocatedAmbientFactorLip (G := G) B R σ L (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    P ≤ allocatedFourierLogBudget m P ∧
      (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ allocatedFourierLogBudget m P ∧
      (A : ℝ)^N ≤ Real.exp (allocatedFourierLogBudget m P) ∧
      (N : ℝ)*F*(A : ℝ)^N ≤ Real.exp (allocatedFourierLogBudget m P) := by
  let A := allocatedAmbientFactorCap (G := G) B R σ L V
  let F := allocatedAmbientFactorLip (G := G) B R σ L (fun j => Fintype.card (J j)) C V
  let T := P + allocatedAmbientLog m P
  have hPT : P ≤ T := le_add_of_nonneg_right (allocatedAmbientLog_nonneg m hP)
  have hT : 0 ≤ T := hP.trans hPT
  obtain ⟨ha, hf⟩ := allocatedAmbientConstants_exp_bounds B R σ L hL _ C V hP hm
    hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have he : Real.exp (allocatedAmbientLog m P) ≤ Real.exp T :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_left hP)
  have h := coefficient_ambient_input_exp_bounds
    hT (hK.trans hPT) (fun j => (hJ j).trans hPT) A.coe_nonneg (ha.trans he) F.coe_nonneg (hf.trans he)
    (coefficientAmbientBudgetExponent_bound m hT)
  exact ⟨hPT.trans h.1, h.2.1, h.2.2.1, h.2.2.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedFourierOutputBudget (m : ℕ) (P : ℝ) : ℝ :=
  let Q := allocatedFourierLogBudget m P
  2*Q*(2*Q+2)^4+Q+(2*Q+2)^4

theorem allocatedFourierOutputBudget_dominates (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    2*Q*(2*Q+2)^4 ≤ allocatedFourierOutputBudget m P ∧
      (2*Q+2)^4 ≤ allocatedFourierOutputBudget m P ∧
      2*Q*(2*Q+2)^4+Q ≤ allocatedFourierOutputBudget m P := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hpow : 0 ≤ (2*allocatedFourierLogBudget m P+2)^4 := by positivity
  have hprod : 0 ≤ 2*allocatedFourierLogBudget m P*(2*allocatedFourierLogBudget m P+2)^4 := by positivity
  dsimp only [allocatedFourierOutputBudget]
  constructor
  · linarith
  constructor <;> linarith

theorem exists_allocatedFourierOutputBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → allocatedFourierOutputBudget m P ≤ (P+a)^a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b)^b
  let output : Polynomial ℕ := 2*q*(2*q+2)^4+q+(2*q+2)^4
  obtain ⟨a, ha, hout⟩ := exists_natPolynomial_eval_budget output
  refine ⟨a, ha, ?_⟩
  intro P hP
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hqb := hb P hP
  have hbound : 2*((P+b)^b)*(2*((P+b)^b)+2)^4+(P+b)^b+(2*((P+b)^b)+2)^4 ≤ (P+a)^a := by
    simpa [output, q, Polynomial.eval₂_pow] using hout P hP
  apply le_trans _ hbound
  dsimp only [allocatedFourierOutputBudget]
  gcongr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedMaskedFourierBudget (m : ℕ) (P : ℝ) : ℝ :=
  let Q := allocatedFourierLogBudget m P
  P + (4 * Q + 2) ^ 4 + (4 * Q * (4 * Q + 2) ^ 4 + Q)

theorem allocatedMaskedFourierBudget_bounds (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    let Ps := allocatedMaskedFourierBudget m P
    0 ≤ Ps ∧ P ≤ Ps ∧ (4 * Q + 2) ^ 4 ≤ Ps ∧
      4 * Q * (4 * Q + 2) ^ 4 + Q ≤ Ps := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hF : 0 ≤ (4 * allocatedFourierLogBudget m P + 2) ^ 4 := by positivity
  have hM : 0 ≤ 4 * allocatedFourierLogBudget m P *
      (4 * allocatedFourierLogBudget m P + 2) ^ 4 + allocatedFourierLogBudget m P := by positivity
  dsimp only [allocatedMaskedFourierBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_allocatedMaskedFourierBudget_bound (m A : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ P : ℝ, 0 ≤ P →
      allocatedMaskedFourierBudget m P ≤ (P + C) ^ C ∧
      (allocatedMaskedFourierBudget m P + A) ^ A ≤ (P + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b
  let f : Polynomial ℕ := Polynomial.X + (4 * q + 2) ^ 4 + (4 * q * (4 * q + 2) ^ 4 + q)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget (f + (f + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro P hP
  let F : ℝ := P + (4 * (P + b) ^ b + 2) ^ 4 +
    (4 * (P + b) ^ b * (4 * (P + b) ^ b + 2) ^ 4 + (P + b) ^ b)
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hPs0 := (allocatedMaskedFourierBudget_bounds m hP).1
  have hPs : allocatedMaskedFourierBudget m P ≤ F := by
    have hQ := allocatedFourierLogBudget_nonneg m hP
    have hQB := hb P hP
    dsimp only [allocatedMaskedFourierBudget, F]
    gcongr
  have hpow : (allocatedMaskedFourierBudget m P + A) ^ A ≤ (F + A) ^ A := by gcongr
  have hpow0 : 0 ≤ (F + A) ^ A := by positivity
  have htotal : F + (F + A) ^ A ≤ (P + C) ^ C := by
    simpa [F, f, q, Polynomial.eval₂_pow] using hbound P hP
  exact ⟨by linarith, by linarith⟩

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
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_allocated_coefficient_uniform_fourier
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P) :
    let Q := allocatedFourierLogBudget m P
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ) (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2*Q*(2*Q+2)^4) ∧
      (∀ t j d, d.degree ≤ j.val+1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp ((2*Q+2)^4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2*Q*(2*Q+2)^4+Q) ∧
      ∀ x, ‖(allocatedCoefficientDensity B U b hb o hR hσ S x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have hbudget := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have hLip :
      ((Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) *
        allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ≥0) : ℝ) ≤
      Real.exp (allocatedFourierLogBudget m P) := by
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast] using hbudget.2.2.2
  obtain ⟨F, inst, frequency, a, hcard, hfreq, hsum, herr⟩ :=
    exists_allocated_coefficient_fourier_approximation B U b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall hδ (allocatedFourierLogBudget_nonneg m hP)
      hbudget.2.1 hLip (hδP.trans (Real.exp_le_exp.mpr hbudget.1))
  let _ := inst
  refine ⟨F, inst, frequency, a, hcard, hfreq, ?_, herr⟩
  exact hsum.trans ((mul_le_mul_of_nonneg_left hbudget.2.2.1 (Real.exp_nonneg _)).trans_eq
    (Real.exp_add _ _).symm)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedJetFourierBudget (m q A : ℕ) (P : ℝ) : ℝ :=
  q + (P + A) ^ A + allocatedFourierOutputBudget m P

theorem allocatedJetFourierBudget_nonneg (m q A : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ allocatedJetFourierBudget m q A P := by
  have hQ := allocatedFourierLogBudget_nonneg m hP
  unfold allocatedJetFourierBudget allocatedFourierOutputBudget
  positivity

theorem allocatedJetFourierBudget_dominates (m q A : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    let Q := allocatedFourierLogBudget m P
    (P + A) ^ A ≤ allocatedJetFourierBudget m q A P ∧
      (2 : ℝ) ^ q * (Real.exp ((P + A) ^ A) * Real.exp ((2 * Q + 2) ^ 4)) ≤
        Real.exp (allocatedJetFourierBudget m q A P) ∧
      Real.exp (2 * Q * (2 * Q + 2) ^ 4 + Q) ≤ Real.exp (allocatedJetFourierBudget m q A P) := by
  intro Q
  have hQ := allocatedFourierLogBudget_nonneg m hP
  have hF : 0 ≤ allocatedFourierOutputBudget m P := by
    unfold allocatedFourierOutputBudget
    positivity
  have hA : 0 ≤ (P + A) ^ A := pow_nonneg (by positivity) _
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hdom := allocatedFourierOutputBudget_dominates m hP
  have h2 : (2 : ℝ) ^ q ≤ Real.exp (q : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ q := pow_le_pow_left₀ (by norm_num)
        (by linarith [Real.add_one_le_exp (1 : ℝ)]) q
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · unfold allocatedJetFourierBudget
    linarith
  · calc
      _ ≤ Real.exp (q : ℝ) * (Real.exp ((P + A) ^ A) * Real.exp (allocatedFourierOutputBudget m P)) :=
        mul_le_mul h2 (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hdom.2.1) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; unfold allocatedJetFourierBudget; ring
  · apply Real.exp_le_exp.mpr
    unfold allocatedJetFourierBudget
    exact hdom.2.2.trans (by linarith)

theorem exists_allocatedJetFourierBudget_bound (m q A : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ P : ℝ, 0 ≤ P → allocatedJetFourierBudget m q A P ≤ (P + B) ^ B := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierOutputBudget_bound m
  obtain ⟨B, hB, hbound⟩ := exists_natPolynomial_eval_budget
    (Polynomial.C q + (Polynomial.X + Polynomial.C A) ^ A + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨B, hB, ?_⟩
  intro P hP
  have hpoly : (q : ℝ) + (P + A) ^ A + (P + b) ^ b ≤ (P + B) ^ B := by
    simpa [Polynomial.eval₂_pow] using hbound P hP
  unfold allocatedJetFourierBudget
  linarith [hb P hP]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def selectedScaleDimensionBudget (m : ℕ) (P : ℝ) : ℝ :=
  (m : ℝ) + geometricSiteBudget m 0 P

theorem selectedScaleDimensionBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ selectedScaleDimensionBudget m P :=
  add_nonneg (Nat.cast_nonneg _) (geometricSiteBudget_nonneg m 0 hP)

theorem le_selectedScaleDimensionBudget (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ selectedScaleDimensionBudget m P :=
  (le_geometricSiteBudget m 0 hP).trans (le_add_of_nonneg_left (Nat.cast_nonneg _))

theorem degree_le_selectedScaleDimensionBudget (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    (m : ℝ) ≤ selectedScaleDimensionBudget m P :=
  le_add_of_nonneg_right (geometricSiteBudget_nonneg m 0 hP)

theorem coefficientCount_le_selectedScaleDimensionBudget {K : Type*} [Fintype K]
    (m : ℕ) {h : ℕ} (hh : h ≤ m) {P : ℝ} (hP : 0 ≤ P) (hK : (Fintype.card K : ℝ) ≤ P) :
    (Fintype.card (BoundedCoefficientExponent K h) : ℝ) ≤ selectedScaleDimensionBudget m P :=
  (boundedCoefficientExponent_card_le_geometricSiteBudget m 0 hh hP hK).trans
    (le_add_of_nonneg_left (Nat.cast_nonneg _))

def selectedFourierInputBudget (m : ℕ) (P : ℝ) : ℝ :=
  allocatedScaleLog (selectedScaleDimensionBudget m P)

theorem selectedFourierInputBudget_nonneg (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ selectedFourierInputBudget m P :=
  allocatedScaleLog_nonneg (selectedScaleDimensionBudget_nonneg m hP)

theorem le_selectedFourierInputBudget (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ selectedFourierInputBudget m P :=
  (le_selectedScaleDimensionBudget m hP).trans
    (le_allocatedScaleLog (selectedScaleDimensionBudget_nonneg m hP))

noncomputable def selectedFourierOutputBudget (m : ℕ) (P : ℝ) : ℝ :=
  allocatedFourierOutputBudget m (selectedFourierInputBudget m P)

theorem exists_selectedFourierOutputBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ P : ℝ, 0 ≤ P → selectedFourierOutputBudget m P ≤ (P+a)^a := by
  obtain ⟨b, _, hb⟩ := exists_allocatedFourierOutputBudget_bound m
  let t : Polynomial ℕ := Polynomial.C m +
    (Polynomial.C (m+1) * (Polynomial.X+1)^(m+1) + 1)
  let q : Polynomial ℕ := (1+t^2)*(5*t+49)
  let budget : Polynomial ℕ := (q+Polynomial.C b)^b
  obtain ⟨a, ha, hbudget⟩ := exists_natPolynomial_eval_budget budget
  refine ⟨a, ha, ?_⟩
  intro P hP
  apply (hb _ (selectedFourierInputBudget_nonneg m hP)).trans
  simpa [budget, q, t, selectedFourierInputBudget, selectedScaleDimensionBudget,
    geometricSiteBudget, allocatedScaleLog, Polynomial.eval₂_pow] using hbudget P hP

noncomputable def selectedFourierExponent (m : ℕ) : ℕ :=
  (exists_selectedFourierOutputBudget_bound m).choose

theorem selectedFourierExponent_two_le (m : ℕ) : 2 ≤ selectedFourierExponent m :=
  (exists_selectedFourierOutputBudget_bound m).choose_spec.1

theorem selectedFourierOutputBudget_bound (m : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    selectedFourierOutputBudget m P ≤ (P+selectedFourierExponent m)^selectedFourierExponent m :=
  (exists_selectedFourierOutputBudget_bound m).choose_spec.2 P hP

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
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedMaskedCoefficientDensity (q : ℕ)
    (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) : ℝ :=
  maskedIntegerTorusKernel q mask (allocatedCoefficientJointAmbientKernel B U b S o)
    (coefficientAmbientTorus U x)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in
theorem exists_allocated_masked_coefficient_fourier
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    {δ P : ℝ} (hδ : 0 < δ) (hP : 0 ≤ P)
    (hdim : (Fintype.card (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J) : ℝ) ≤ P)
    (hLP : let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
      let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
      let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
      (q : ℝ) * ((N * L * A^N : ℝ≥0) : ℝ) ≤ Real.exp P)
    (hδP : δ⁻¹ ≤ Real.exp P) :
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
      (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) ∧
      (∀ t j d, d.degree ≤ j.val + 1 → ∀ i,
        |(frequency t j d i : ℝ)| ≤ Real.exp ((2 * P + 2) ^ 4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (2 * P * (2 * P + 2) ^ 4) *
        (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ)^
          Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) ∧
      ∀ x, ‖(allocatedMaskedCoefficientDensity B U b o S q mask x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  have hk := allocatedCoefficientJointAmbientKernel_bounds B U b S o C V hC hV hR hσ
  obtain ⟨F,inst,frequency,a,hcard,hfreq,hsum,herr⟩ :=
    exists_masked_integer_fourier_approximation q mask hmask
      (allocatedCoefficientJointAmbientKernel B U b S o) _
      ((allocatedAmbientFactorCap (G := G) B R σ S.value V)^
        Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)) hk.2
      (fun x => by simpa only [NNReal.coe_pow, Set.mem_Icc] using hk.1 x)
      (allocatedCoefficientJointAmbientKernel_support B U b S o) hδ hP hdim hLP hδP
  let _ := inst
  refine ⟨F,inst,fun t => coefficientSlotFrequency (fun s i => frequency t ⟨s,i⟩),
    a,hcard,?_,?_,?_⟩
  · intro t
    exact coefficientSlotFrequency_bound (fun s i => frequency t ⟨s,i⟩)
      (fun s i => hfreq t ⟨s,i⟩)
  · simpa only [NNReal.coe_pow] using hsum
  · intro x
    simpa only [allocatedMaskedCoefficientDensity, coefficientAmbientTorus_character,
      coefficientTorusFourierSum] using herr (coefficientAmbientTorus U x)

include hC hV in
theorem exists_allocated_masked_coefficient_uniform_fourier
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (q : ℕ) (mask : (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r, mask r ∈ Set.Icc (0 : ℝ) 1)
    {P δ : ℝ} (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P) :
    let Q := allocatedFourierLogBudget m P
    ∃ (F : Type) (inst : Fintype F), letI := inst
    ∃ (frequency : F → ∀ j : Fin m, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
      (a : F → ℂ),
      (Fintype.card F : ℝ) ≤ Real.exp (4*Q*(4*Q+2)^4) ∧
      (∀ t j d, d.degree ≤ j.val+1 → ∀ i, |(frequency t j d i : ℝ)| ≤ Real.exp ((4*Q+2)^4)) ∧
      (∑ t, ‖a t‖) ≤ Real.exp (4*Q*(4*Q+2)^4+Q) ∧
      ∀ x, ‖(allocatedMaskedCoefficientDensity B U b o S q mask x : ℂ) -
        coefficientTorusFourierSum U frequency a x‖ ≤ δ := by
  let Q := allocatedFourierLogBudget m P
  have hbudget := allocatedCoefficient_fourier_input_budget B (J := J) R σ S.value S.positive C V
    hP hm hK hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP
  have hQ : 0 ≤ Q := allocatedFourierLogBudget_nonneg m hP
  have hP2 : P ≤ 2 * Q := hbudget.1.trans (by linarith)
  have hscaled : let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
      let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
      let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
      (q : ℝ) * ((N * L * A^N : ℝ≥0) : ℝ) ≤ Real.exp (2 * Q) := by
    have hLip := hbudget.2.2.2
    simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast]
    calc
      _ ≤ Real.exp Q * Real.exp Q := mul_le_mul
        (hqP.trans (Real.exp_le_exp.mpr hbudget.1)) hLip (by positivity) (Real.exp_nonneg _)
      _ = Real.exp (2 * Q) := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨F,inst,frequency,a,hcard,hfreq,hsum,herr⟩ :=
    exists_allocated_masked_coefficient_fourier B U b o S C V hC hV hR hσ q mask hmask
      hδ (by positivity : 0 ≤ 2*Q) (hbudget.2.1.trans (by linarith)) hscaled
      (hδP.trans (Real.exp_le_exp.mpr hP2))
  let _ := inst
  have hfour : 2 * (2 * Q) = 4 * Q := by ring
  refine ⟨F,inst,frequency,a,?_,?_,?_,herr⟩
  · simpa only [hfour] using hcard
  · simpa only [hfour] using hfreq
  · have hh := hsum.trans (mul_le_mul_of_nonneg_left hbudget.2.2.1 (Real.exp_nonneg _))
    simpa only [hfour, ← Real.exp_add] using hh

end Erdos3.VectorPolynomial

end

end OAI

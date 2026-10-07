import OAI.Combinatorics.Progressions.Polynomial.AllocatedNormalizedScalePolynomial

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem allocatedNormalizedCoefficientInput {m : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {p : ℝ} (hp : 0 ≤ p) (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p) :
    let D := allocatedComparisonDimension m p
    0 ≤ D ∧ p ≤ D ∧ ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤
        Real.exp D := by
  obtain ⟨hD, _, hpD, _, hc, _⟩ := allocatedComparisonDimension_bounds m hp
  refine ⟨hD, hpD, ?_⟩
  intro j
  have hcount := (boundedCoefficientExponent_card_le_geometricSiteBudget m 0
    (Nat.succ_le_of_lt j.isLt) hp hvars).trans hc
  linarith [Real.add_one_le_exp (allocatedComparisonDimension m p)]

noncomputable def allocatedPrimitiveNormalizedScaleLog {A : Type*} [Semiring A]
    (m : ℕ) (p E T : A) : A :=
  allocatedNormalizedScaleLog m p (allocatedComparisonDimension m p) E T

theorem exists_allocatedPrimitiveNormalizedScaleLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E T : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ T →
      allocatedPrimitiveNormalizedScaleLog m p E T ≤ (p + E + T + a) ^ a := by
  let poly : Polynomial ℕ := allocatedPrimitiveNormalizedScaleLog m Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p E T hp hE hT
  have hpq : p ≤ p + E + T := by linarith
  have hD : allocatedComparisonDimension m p ≤ allocatedComparisonDimension m (p + E + T) := by
    unfold allocatedComparisonDimension
    gcongr
  have hmono := allocatedNormalizedScaleLog_mono m hp (allocatedComparisonDimension_bounds m hp).1
    hE hT hpq hD (show E ≤ p + E + T by linarith) (show T ≤ p + E + T by linarith)
  apply hmono.trans
  simpa [poly, allocatedPrimitiveNormalizedScaleLog, allocatedNormalizedScaleLog,
    allocatedNormalizedScaleInput, allocatedNormalizedInitialLog, allocatedJointLengthEnvelope,
    allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope, allocatedKernelEnvelope,
    allocatedDensityEnvelope, kernelOutputEnvelope, kernelGeometryEnvelope, kernelInverseEnvelope,
    coefficientErrorAccuracyLog, coefficientErrorSpatialLog, coefficientMajorantMassLog,
    coefficientErrorVolumeLog, anisotropicSpatialCapLog, allocatedComparisonDimension,
    Polynomial.eval₂_pow] using hbound (p + E + T) (by positivity)

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

noncomputable def allocatedPrimitiveNormalizedScale (p E T : ℝ) :
    LayerSamplerScale (G := G) B U b R σ :=
  allocatedNormalizedScale B U b hR hσ p (allocatedComparisonDimension m p) E T

theorem allocatedPrimitiveNormalizedScale_upper {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hn : ∀ j, (n j : ℝ) ≤ p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    ((allocatedPrimitiveNormalizedScale (G := G) B U b hR hσ p E T).value : ℝ) ≤
      Real.exp (allocatedPrimitiveNormalizedScaleLog m p E T) := by
  obtain ⟨hD, hpD, _⟩ := allocatedNormalizedCoefficientInput B hp hvars
  exact allocatedNormalizedScale_upper B U b hR hσ hp hD hE hT hvars hn
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpD))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpD))

theorem allocatedPrimitiveNormalizedScale_ready
    {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset α) (hq : Fintype.card α ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j)) (X : Type*) [Fintype X]
    {p E T : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hX : (Fintype.card X : ℝ) ≤ p) :
    Real.exp (allocatedRefinedJointLengthLog (G := G) B α O (allocatedComparisonDimension m p)
      (allocatedCoefficientAccuracyLog m p (E + 3))
      ((m + 1 : ℕ) * allocatedComparisonDimension m p + Fintype.card X * T)) ≤
        ((allocatedPrimitiveNormalizedScale (G := G) B U b hR hσ p E T).value : ℝ) :=
  allocatedNormalizedScale_ready B U b hR hσ rows hq hinj X hp
    (allocatedComparisonDimension_bounds m hp).1 hE hT hvars hI hn hX

theorem exists_allocatedPrimitiveNormalizedScale_upper (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {G : Type*} [Fintype G]
      {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ v, Fintype (B v)]
      {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
      (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      {p E T : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ T →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
      (∀ j, (n j : ℝ) ≤ p) → (∀ j, (R j)⁻¹ ≤ Real.exp p) → (∀ j, (σ j)⁻¹ ≤ Real.exp p) →
      ((allocatedPrimitiveNormalizedScale (G := G) B U b hR hσ p E T).value : ℝ) ≤
        Real.exp ((p + E + T + a) ^ a) := by
  obtain ⟨a, ha, hlog⟩ := exists_allocatedPrimitiveNormalizedScaleLog_bound m
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ J _ U b R σ hR hσ p E T hp hE hT hvars hn hRi hσi
  exact (allocatedPrimitiveNormalizedScale_upper B U b hR hσ hp hE hT hvars hn hRi hσi).trans
    (Real.exp_le_exp.mpr (hlog hp hE hT))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem exists_allocatedNormalizedScale_refined_data
    {p E T : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hσ1 : ∀ j, σ j ≤ 1) (hRP : ∀ j, R j ≤ Real.exp p)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp p) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p) :
    ∃ S : LayerSamplerScale (G := G) B U b R σ,
      S = allocatedPrimitiveNormalizedScale B U b hR hσ p E T ∧
      (S.value : ℝ) ≤ Real.exp (allocatedPrimitiveNormalizedScaleLog m p E T) ∧
      ∀ {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
        {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
        (rows : ∀ j, O j → Finset α) (X : Type*) [Fintype X],
        (Fintype.card X : ℝ) ≤ p → ∀ {M : ℕ}, 0 < M →
        ∀ (selection : α ↪ G), GoodScalarKernelTuple selection (1 / (M : ℝ)) M x →
        Fintype.card α ≤ m + 1 → (∀ j, Function.Injective (rows j)) →
        (∀ j o, (rows j o).card ≤ j.val + 1) → (M : ℝ) ≤ Real.exp p →
        allocatedStrideRefinedStatement B U b hR hσ S x rows X M selection hσ1
          (allocatedComparisonDimension m p) T (allocatedCoefficientAccuracy m p (E + 3)) := by
  classical
  let S := allocatedPrimitiveNormalizedScale (G := G) B U b hR hσ p E T
  obtain ⟨hP, hpP, hcount⟩ := allocatedNormalizedCoefficientInput B hp hvars
  have hEP : 0 ≤ E + 3 := by positivity
  obtain ⟨hη, hη1, hηE⟩ := allocatedCoefficientAccuracy_bounds m hp hEP
  refine ⟨S, rfl, allocatedPrimitiveNormalizedScale_upper B U b hR hσ hp hE hT hvars hn hRi hσi, ?_⟩
  intro α _ _ x O _ _ rows X _ hX M hM selection hx hq hinj hrows hMP
  exact allocatedStrideRefinedStatement_of_data B U b hR hσ S x rows X
    hM selection hx hq hinj hrows hσ1 hP (allocatedCoefficientAccuracyLog_nonneg m hp hEP)
    hT hη hη1 (hMP.trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hRP j).trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hpP))
    (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpP)) hcount hηE.le
    (allocatedPrimitiveNormalizedScale_ready B U b hR hσ rows hq hinj X
      hp hE hT hvars hI hn hX)

end Erdos3.VectorPolynomial

end

end OAI

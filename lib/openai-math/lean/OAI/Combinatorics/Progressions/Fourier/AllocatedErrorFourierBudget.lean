import OAI.Combinatorics.Progressions.Dynamics.AllocatedReferenceIdealBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

noncomputable def allocatedErrorFourierInput {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  allocatedErrorPrimitiveLog m p + allocatedErrorKernelLog (allocatedErrorPrimitiveLog m p)

noncomputable def allocatedErrorFourierOutput {A : Type*} [Semiring A] (m : ℕ) (p : A) : A :=
  let L := allocatedErrorFourierInput m p
  p + 2 * L * (2 * L + 2) ^ 4 + L + (2 * L + 2) ^ 4

theorem allocatedErrorFourier_budgets (m : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let T := allocatedErrorPrimitiveLog m p
    let L := allocatedErrorFourierInput m p
    let P := allocatedErrorFourierOutput m p
    0 ≤ L ∧ p ≤ L ∧ T ≤ L ∧ allocatedErrorKernelLog T ≤ L ∧ p ≤ P ∧
      (2 * L + 2) ^ 4 ≤ P ∧ 2 * L * (2 * L + 2) ^ 4 + L ≤ P := by
  have hT := (allocatedErrorPrimitiveLog_bounds m hp).1
  have hpT := (allocatedErrorPrimitiveLog_bounds m hp).2.1
  have hlog := allocatedErrorKernelLog_nonneg hT
  have hL : 0 ≤ allocatedErrorFourierInput m p := add_nonneg hT hlog
  have hf : 0 ≤ (2 * allocatedErrorFourierInput m p + 2) ^ 4 := by positivity
  have hc : 0 ≤ 2 * allocatedErrorFourierInput m p * (2 * allocatedErrorFourierInput m p + 2) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) hL) hf
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change p ≤ allocatedErrorPrimitiveLog m p + allocatedErrorKernelLog (allocatedErrorPrimitiveLog m p)
    linarith
  · exact le_add_of_nonneg_right hlog
  · exact le_add_of_nonneg_left hT
  all_goals dsimp only [allocatedErrorFourierOutput]; linarith

theorem exists_allocatedErrorFourierOutput_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedErrorFourierOutput m p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedErrorFourierOutput m Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedErrorFourierOutput, allocatedErrorFourierInput, allocatedErrorPrimitiveLog,
    allocatedErrorKernelLog, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedErrorPrimitive_fourier_budget
    {α : Type*} [Fintype α] (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1))
    (η : ℝ≥0) (C V : Fin m → ℝ≥0) {p δ : ℝ} (hp : 0 ≤ p)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hη : η ≤ 1) (hM : (M : ℝ) ≤ Real.exp p) (hS : (S.value : ℝ) ≤ Real.exp p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hδ : δ⁻¹ ≤ Real.exp p) :
    let L := allocatedErrorFourierInput m p
    let P := allocatedErrorFourierOutput m p
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period)
    0 ≤ L ∧ p ≤ P ∧ (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L ∧ δ⁻¹ ≤ Real.exp L ∧
      (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp P := by
  obtain ⟨hamb, hcap, hlip⟩ := allocatedErrorPrimitive_constants B U b S rows hq hinj hb bW M period
    hperiod η C V hp hvars hI hn hJ hη hM hS hC hV
  obtain ⟨hL, hpL, hTL, hlogL, hpP, hfreq, hcoeff⟩ := allocatedErrorFourier_budgets m hp
  have he := Real.exp_le_exp.mpr hlogL
  refine ⟨hL, hpP, hamb.trans hTL, hδ.trans (Real.exp_le_exp.mpr hpL), hlip.trans he,
    Real.exp_le_exp.mpr hfreq, ?_⟩
  calc
    _ ≤ Real.exp (2 * allocatedErrorFourierInput m p * (2 * allocatedErrorFourierInput m p + 2) ^ 4) *
        Real.exp (allocatedErrorFourierInput m p) :=
      mul_le_mul_of_nonneg_left (hcap.trans he) (Real.exp_pos _).le
    _ = Real.exp (2 * allocatedErrorFourierInput m p * (2 * allocatedErrorFourierInput m p + 2) ^ 4 +
        allocatedErrorFourierInput m p) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcoeff

end Erdos3.VectorPolynomial

end

end OAI

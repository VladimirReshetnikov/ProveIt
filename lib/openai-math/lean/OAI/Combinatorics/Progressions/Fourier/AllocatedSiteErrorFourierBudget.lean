import OAI.Combinatorics.Progressions.Dynamics.AllocatedReferenceIdealBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

noncomputable def allocatedSiteErrorFourierInput {A : Type*} [Semiring A]
    (m : ℕ) (p w v : A) : A :=
  let T := allocatedSiteErrorPrimitiveLog m p w v
  T + allocatedErrorKernelLog T

noncomputable def allocatedSiteErrorFourierOutput {A : Type*} [Semiring A]
    (m : ℕ) (p w v : A) : A :=
  let L := allocatedSiteErrorFourierInput m p w v
  p + 2 * L * (2 * L + 2) ^ 4 + L + (2 * L + 2) ^ 4

theorem allocatedSiteErrorFourier_budgets (m : ℕ) {p w v : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    let T := allocatedSiteErrorPrimitiveLog m p w v
    let L := allocatedSiteErrorFourierInput m p w v
    let P := allocatedSiteErrorFourierOutput m p w v
    0 ≤ L ∧ p ≤ L ∧ T ≤ L ∧ allocatedErrorKernelLog T ≤ L ∧ p ≤ P ∧
      (2 * L + 2) ^ 4 ≤ P ∧ 2 * L * (2 * L + 2) ^ 4 + L ≤ P := by
  have hT := (allocatedSiteErrorPrimitiveLog_bounds m hp hw hv).1
  have hpT := (allocatedSiteErrorPrimitiveLog_bounds m hp hw hv).2.1
  have hlog := allocatedErrorKernelLog_nonneg hT
  have hL : 0 ≤ allocatedSiteErrorFourierInput m p w v := add_nonneg hT hlog
  have hf : 0 ≤ (2 * allocatedSiteErrorFourierInput m p w v + 2) ^ 4 := by positivity
  have hc : 0 ≤ 2 * allocatedSiteErrorFourierInput m p w v *
      (2 * allocatedSiteErrorFourierInput m p w v + 2) ^ 4 :=
    mul_nonneg (mul_nonneg (by norm_num) hL) hf
  refine ⟨hL, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change p ≤ allocatedSiteErrorPrimitiveLog m p w v +
      allocatedErrorKernelLog (allocatedSiteErrorPrimitiveLog m p w v)
    linarith
  · exact le_add_of_nonneg_right hlog
  · exact le_add_of_nonneg_left hT
  all_goals dsimp only [allocatedSiteErrorFourierOutput]; linarith

theorem exists_allocatedSiteErrorFourierOutput_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p →
      allocatedSiteErrorFourierOutput m p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedSiteErrorFourierOutput m Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedSiteErrorFourierOutput, allocatedSiteErrorFourierInput,
    allocatedSiteErrorPrimitiveLog, allocatedErrorPrimitiveLog, allocatedErrorKernelLog,
    allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]

theorem allocatedSiteErrorPrimitive_fourier_budget
    {α : Type*} [Fintype α] (rows : ∀ j, O j → Finset α)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (M period : ℕ) (hperiod : period ≤ M ^ (m + 1))
    (η CM Cf : ℝ≥0) (C V : Fin m → ℝ≥0) {p w v δ : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hη : η ≤ 1) (hM : (M : ℝ) ≤ Real.exp p) (hS : (S.value : ℝ) ≤ Real.exp p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p) (hV : ∀ j, (V j : ℝ) ≤ Real.exp p)
    (hCM : (CM : ℝ) ≤ Real.exp w) (hCf : (Cf : ℝ) ≤ Real.exp v)
    (hδ : δ⁻¹ ≤ Real.exp p) :
    let L := allocatedSiteErrorFourierInput m p w v
    let P := allocatedSiteErrorFourierOutput m p w v
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    0 ≤ L ∧ p ≤ P ∧ (Fintype.card (JetAmbientIndex O J) : ℝ) ≤ L ∧ δ⁻¹ ≤ Real.exp L ∧
      (allocatedErrorKernelLip B U b S (O := O) η A C V : ℝ) ≤ Real.exp L ∧
      Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P ∧
      Real.exp (2 * L * (2 * L + 2) ^ 4) *
        allocatedErrorKernelCap B U b S (O := O) η A V ≤ Real.exp P := by
  obtain ⟨hamb, hcap, hlip⟩ := allocatedSiteErrorPrimitive_constants B U b S rows hq hinj hb bW
    M period hperiod η CM Cf C V hp hw hv hvars hI hn hJ hη hM hS hC hV hCM hCf
  obtain ⟨hL, hpL, hTL, hlogL, hpP, hfreq, hcoeff⟩ := allocatedSiteErrorFourier_budgets m hp hw hv
  have he := Real.exp_le_exp.mpr hlogL
  refine ⟨hL, hpP, hamb.trans hTL, hδ.trans (Real.exp_le_exp.mpr hpL), hlip.trans he,
    Real.exp_le_exp.mpr hfreq, ?_⟩
  calc
    _ ≤ Real.exp (2 * allocatedSiteErrorFourierInput m p w v *
        (2 * allocatedSiteErrorFourierInput m p w v + 2) ^ 4) *
        Real.exp (allocatedSiteErrorFourierInput m p w v) :=
      mul_le_mul_of_nonneg_left (hcap.trans he) (Real.exp_pos _).le
    _ = Real.exp (2 * allocatedSiteErrorFourierInput m p w v *
        (2 * allocatedSiteErrorFourierInput m p w v + 2) ^ 4 +
        allocatedSiteErrorFourierInput m p w v) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcoeff

end Erdos3.VectorPolynomial

end

end OAI

/- Modified for ProveIt: give the full-chart grade quotient conversion a
finite local checking budget on Lean 4.32. All upstream theorem statements
and mathematical proof bodies are unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.RestrictedMajorCorrectionOnSet
import OAI.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (N : X → ℕ) (budget : ℝ)

def FullChartDetectedMajorGradeConclusion
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (N : X → ℕ) (budget : ℝ) : Prop :=

  ∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
    (gen : η → Fin (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J k) k) M)) → weightedSubalgebra (lowTaggedWeight J k) k)
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) (q : ℕ),
    (∀ i, (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J k) k) M) : ℝ) ≤ budget ∧
      Submodule.span ℚ (Set.range (gen i)) = (detectedfast i).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k))
        (weightedBasisGrade (lowTaggedWeight J k) k) (detectedfast i).toSubmodule ∧
      ∀ j a, rationalLogHeight
        ((weightedBasis (lowTaggedWeight J k) k (lowTaggedWeight_pos J k)).repr (gen i j) a) ≤ budget) ∧
    (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ (Fin (Fintype.card (LowTaggedIndex J k)))) (lowTaggedWeight J k)
      (majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    (∀ i h, lowTaggedRetained J k Utag h ≤ majorPhaseDetectedRealBase J k (detectedfast i)) ∧
    (∀ i α, |basis.coord i (coefficients slow α)| ≤ Real.exp budget) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    (∀ i, realPolynomialCoefficientGrid q (coordinate (basis.coord i).toAddMonoidHom rat)) ∧
    RestrictedMajorGradeCorrectionConclusion (σ := X ⊕ (Σ j, J j)) F b ω hF (fullTaggedVariableWeight (X := X) J) fast lift k Z left right
      (fullTaggedGradedBaseIntersection J k K₀ (fun i => majorPhaseDetectedRealBase J k (detectedfast i)))
      (realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (lowTaggedVectorExtend J k slow)) (lowTaggedVectorExtend J k rat)

theorem fullChartDetectedMajorGradeConclusion_of_fullTagged
    (h : FullTaggedDetectedMajorGradeConclusion (M := M)
      F b ω hF J k fast basis lift Z left right K₀ Utag poly c N budget) :
    FullChartDetectedMajorGradeConclusion (M := M)
      F b ω hF J k fast basis lift Z left right K₀ Utag poly c N budget := by
  unfold FullTaggedDetectedMajorGradeConclusion at h
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, hcoeff,
    hq, hqB, hgrid, hstep⟩ := h
  rw [lowTaggedVectorExtend_majorChart] at hstep
  unfold FullChartDetectedMajorGradeConclusion
  refine ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, hcoeff,
    hq, hqB, hgrid, ?_⟩
  with_reducible exact hstep

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def FullChartGradeCorrectionData : Prop :=
  ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    K' ⊆ K₀ ∧
    (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
    (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
    (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
    (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
    (∀ t ∈ K', ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
            (realChartSubstitute chart pS))⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
        fast.baseChange ℝ) ∧
    ∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
      (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
      pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
      K' = fullTaggedGradedBaseIntersection J k K₀
        (fun i => majorPhaseDetectedRealBase J k (detectedfast i))

theorem fullChartGradeCorrectionData_of_detected
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (h : FullChartDetectedMajorGradeConclusion (M := M)
      F b ω hF J k fast basis lift Z left right K₀ Utag poly c N budget) :
    FullChartGradeCorrectionData F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  unfold FullChartDetectedMajorGradeConclusion at h
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, hcoeff,
    hq, hqB, hgrid, hstep⟩ := h
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  have hcap := lowTaggedVectorExtend_coordinate_coefficient_bound J k
    (fun i => (basis.coord i).toAddMonoidHom) slow (Real.exp budget)
    (Real.exp_pos budget).le hcoeff
  have hden := lowTaggedVectorExtend_coefficients_grid J k
    (fun i => (basis.coord i).toAddMonoidHom) rat q hgrid
  unfold RestrictedMajorGradeCorrectionConclusion at hstep
  obtain ⟨A, D, hA, hD, _, _, _, _, hnext⟩ := hstep
  have hAc : A = F.restrictedMajorCorrection b ω hF wt fast lift k
      (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hA
  have hDc : D = F.restrictedMajorCorrection b ω hF wt fast lift k
      (lowTaggedVectorExtend J k rat) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hD
  rw [hAc, hDc] at hnext
  unfold FullChartGradeCorrectionData
  refine ⟨lowTaggedVectorExtend J k slow, lowTaggedVectorExtend J k rat, q,
    fullTaggedGradedBaseIntersection J k K₀ K, hq, hqB,
    fullTaggedGradedBaseIntersection_subset J k K₀ K,
    fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀,
    ?_, hcap, hden, ?_, ?_⟩
  · intro t ht hU
    refine ⟨ht, ?_⟩
    intro i
    change lowTaggedCoordinates J k (fun j a => t (Sum.inr ⟨j, a⟩)) ∈ K i
    apply (lowTaggedCoordinates_mem_iff J k (K i) (hgrade i) _).mpr
    intro j
    exact le_lowTaggedSubspaceFamily J k Utag (K i) (hretain i) j (hU j)
  · with_reducible exact hnext
  · exact ⟨detectedfast, slow, rat, rfl, rfl, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def CertifiedFullChartGradeCorrectionData : Prop :=
  ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    K' ⊆ K₀ ∧
    (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
    (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
    (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
    (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
    (∀ t ∈ K', ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
            (realChartSubstitute chart pS))⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
        fast.baseChange ℝ) ∧
    (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
      (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
      pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
      K' = fullTaggedGradedBaseIntersection J k K₀
        (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m)

theorem certifiedFullChartGradeCorrectionData_of_detected
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (h : FullChartDetectedMajorGradeConclusion (M := M)
      F b ω hF J k fast basis lift Z left right K₀ Utag poly c N budget) :
    CertifiedFullChartGradeCorrectionData F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  unfold FullChartDetectedMajorGradeConclusion at h
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, hcoeff,
    hq, hqB, hgrid, hstep⟩ := h
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  have hcap := lowTaggedVectorExtend_coordinate_coefficient_bound J k
    (fun i => (basis.coord i).toAddMonoidHom) slow (Real.exp budget)
    (Real.exp_pos budget).le hcoeff
  have hden := lowTaggedVectorExtend_coefficients_grid J k
    (fun i => (basis.coord i).toAddMonoidHom) rat q hgrid
  unfold RestrictedMajorGradeCorrectionConclusion at hstep
  obtain ⟨A, D, hA, hD, _, _, _, _, hnext⟩ := hstep
  have hAc : A = F.restrictedMajorCorrection b ω hF wt fast lift k
      (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hA
  have hDc : D = F.restrictedMajorCorrection b ω hF wt fast lift k
      (lowTaggedVectorExtend J k rat) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hD
  rw [hAc, hDc] at hnext
  have hcertificate := majorPhase_rationalTaggedConstraintCertificate J k
    detectedfast gen K₀ budget hgen
  unfold CertifiedFullChartGradeCorrectionData
  refine ⟨lowTaggedVectorExtend J k slow, lowTaggedVectorExtend J k rat, q,
    fullTaggedGradedBaseIntersection J k K₀ K, hq, hqB,
    fullTaggedGradedBaseIntersection_subset J k K₀ K,
    fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀,
    ?_, hcap, hden, ?_, ?_, hcertificate⟩
  · intro t ht hU
    refine ⟨ht, ?_⟩
    intro i
    change lowTaggedCoordinates J k (fun j a => t (Sum.inr ⟨j, a⟩)) ∈ K i
    apply (lowTaggedCoordinates_mem_iff J k (K i) (hgrade i) _).mpr
    intro j
    exact le_lowTaggedSubspaceFamily J k Utag (K i) (hretain i) j (hU j)
  · with_reducible exact hnext
  · exact ⟨detectedfast, slow, rat, rfl, rfl, rfl⟩

theorem CertifiedFullChartGradeCorrectionData.to_uncertified
    (h : CertifiedFullChartGradeCorrectionData F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    FullChartGradeCorrectionData F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    hnext, horigin, _⟩ := h
  refine ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    ?_, horigin⟩
  with_reducible exact hnext

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

structure FullChartFiniteHistory
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (N : X → ℕ) (Bphase : ℝ) (n : ℕ) where
  slow : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  rat : ℕ → VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
  q : ℕ → ℕ
  K : Set (X ⊕ (Σ j, J j) → ℝ)
  subset : K ⊆ Kinitial
  dilation : ∀ t ∈ K, ∀ r : ℚ,
    (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K
  retained : ∀ t ∈ Kinitial, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K
  slow_bound : ∀ j < n, ∀ α i, |basis.coord i (coefficients (slow j) α)| ≤ Real.exp Bphase
  q_pos : ∀ j < n, 0 < q j
  q_bound : ∀ j < n, (q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase)
  rat_grid : ∀ j < n, ∀ α,
    (fun i => basis.coord i (coefficients (rat j) α)) ∈ realDenominatorGrid (q j)
  invariant :
    let outer := F.restrictedMajorOuterFactors b ω hF (fullTaggedVariableWeight J) fast lift
      (fun j => realChartSubstitute (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly)) (slow j)) rat n
    ∀ t ∈ K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (outer.1⁻¹ * Z * outer.2⁻¹).coord ∈ fast.baseChange ℝ

namespace FullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)
local notation "State" => FullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

noncomputable def outer {n : ℕ} (H : State n) :
    F.RealPolynomialSymbolGroup wt × F.RealPolynomialSymbolGroup wt :=
  F.restrictedMajorOuterFactors b ω hF wt fast lift
    (fun j => realChartSubstitute chart (H.slow j)) H.rat n

noncomputable def initial
    (hK : ∀ t ∈ Kinitial, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ Kinitial) :
    State 0 where
  slow := fun _ => 0
  rat := fun _ => 0
  q := fun _ => 1
  K := Kinitial
  subset := fun _ ht => ht
  dilation := hK
  retained := fun _ ht _ => ht
  slow_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  q_pos := fun j hj => (Nat.not_lt_zero j hj).elim
  q_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  rat_grid := fun j hj => (Nat.not_lt_zero j hj).elim
  invariant := by
    dsimp only
    intro t ht j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [F.realSymbolGradeEvaluation_zero]
    exact Submodule.zero_mem _

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

noncomputable def mono_bound {n : ℕ} (H : State n) {B' : ℝ} (hBB' : Bphase ≤ B') :
    FullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N B' n where
  slow := H.slow
  rat := H.rat
  q := H.q
  K := H.K
  subset := H.subset
  dilation := H.dilation
  retained := H.retained
  slow_bound := fun j hj α i => (H.slow_bound j hj α i).trans (Real.exp_le_exp.mpr hBB')
  q_pos := H.q_pos
  q_bound := fun j hj => (H.q_bound j hj).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hBB' (Nat.cast_nonneg _)))
  rat_grid := H.rat_grid
  invariant := H.invariant

theorem outer_mono_bound {n : ℕ} (H : State n) {B' : ℝ} (hBB' : Bphase ≤ B') :
    (H.mono_bound hBB').outer = H.outer := by
  dsimp only [outer, mono_bound]

theorem mono_bound_K {n : ℕ} (H : State n) {B' : ℝ} (hBB' : Bphase ≤ B') :
    (H.mono_bound hBB').K = H.K := rfl

theorem invariant_outer {n : ℕ} (H : State n) :
    ∀ t ∈ H.K, ∀ j ≤ n,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
  dsimp only [outer]
  have h := H.invariant
  dsimp only at h
  with_reducible exact h

theorem exists_step {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase)
    (hdata : FullChartGradeCorrectionData F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget) :
    ∃ Hnext : State (n + 1),
      (∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j) ∧
      Hnext.K ⊆ H.K := by
  classical
  unfold FullChartGradeCorrectionData at hdata
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid, hnext, _⟩ := hdata
  let slow' := Function.update H.slow n pS
  let rat' := Function.update H.rat n pR
  let q' := Function.update H.q n q
  have hslow (j : ℕ) (hj : j < n) : slow' j = H.slow j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hrat (j : ℕ) (hj : j < n) : rat' j = H.rat j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hqold (j : ℕ) (hj : j < n) : q' j = H.q j :=
    Function.update_of_ne (Nat.ne_of_lt hj) _ _
  have hprefix : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' n = H.outer := by
    apply F.restrictedMajorOuterFactors_congr
    · intro j hj
      rw [hslow j hj]
    · exact hrat
  have houter : F.restrictedMajorOuterFactors b ω hF wt fast lift
      (fun j => realChartSubstitute chart (slow' j)) rat' (n + 1) =
      (H.outer.1 * F.restrictedMajorCorrection b ω hF wt fast lift (n + 1)
        (realChartSubstitute chart pS),
       F.restrictedMajorCorrection b ω hF wt fast lift (n + 1) pR * H.outer.2) := by
    rw [restrictedMajorOuterFactors, hprefix]
    simp only [slow', rat', Function.update_self]
  have hcapB : ∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp Bphase :=
    fun α i => (hcap α i).trans (Real.exp_le_exp.mpr hbudget)
  have hqBB : (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * Bphase) :=
    hqB.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg _)))
  let Hnext : State (n + 1) := {
    slow := slow'
    rat := rat'
    q := q'
    K := K'
    subset := fun t ht => H.subset (hsub ht)
    dilation := hdilate
    retained := fun t ht hU => hretain t (H.retained t ht hU) hU
    slow_bound := by
      intro j hj α i
      by_cases hjn : j = n
      · subst j
        simpa only [slow', Function.update_self] using hcapB α i
      · rw [hslow j (by omega)]
        exact H.slow_bound j (by omega) α i
    q_pos := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hq
      · rw [hqold j (by omega)]
        exact H.q_pos j (by omega)
    q_bound := by
      intro j hj
      by_cases hjn : j = n
      · subst j
        simpa only [q', Function.update_self] using hqBB
      · rw [hqold j (by omega)]
        exact H.q_bound j (by omega)
    rat_grid := by
      intro j hj α
      by_cases hjn : j = n
      · subst j
        simpa only [rat', q', Function.update_self] using hgrid α
      · rw [hrat j (by omega), hqold j (by omega)]
        exact H.rat_grid j (by omega) α
    invariant := by
      dsimp only
      rw [houter]
      with_reducible exact hnext }
  exact ⟨Hnext, fun j hj => ⟨hslow j hj, hrat j hj, hqold j hj⟩, hsub⟩

end FullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

theorem certifiedFullChartGradeCorrectionData_of_representative
    (K' : Set (X ⊕ (Σ j, J j) → ℝ))
    (pS pR qS qR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
    (q : ℕ) (hq : 0 < q) (hqB : (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget))
    (hsub : K' ⊆ K₀)
    (hdilate : ∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K')
    (hretain : ∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K')
    (hcap : ∀ α i, |basis.coord i (coefficients qS α)| ≤ Real.exp budget)
    (hgrid : ∀ α, (fun i => basis.coord i (coefficients qR α)) ∈ realDenominatorGrid q)
    (horigin : ∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
      qS = lowTaggedVectorExtend J k slow ∧ qR = lowTaggedVectorExtend J k rat ∧
      K' = fullTaggedGradedBaseIntersection J k K₀
        (fun i => majorPhaseDetectedRealBase J k (detectedfast i)))
    (hcertificate : RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m))
    (hslowEq : ∀ t ∈ K', eval₂ t (realChartSubstitute chart pS) =
      eval₂ t (realChartSubstitute chart qS))
    (hratEq : ∀ t ∈ K', eval₂ t pR = eval₂ t qR)
    (hnext : ∀ t ∈ K', ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
            (realChartSubstitute chart pS))⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
        fast.baseChange ℝ) :
    CertifiedFullChartGradeCorrectionData F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  refine ⟨qS, qR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid, ?_,
    horigin, hcertificate⟩
  intro t ht j hj
  have heq := F.restrictedMajorCorrection_residual_grades_congr_on b ω hF wt fast lift
    k Z left right K' hdilate (realChartSubstitute chart pS) pR
    (realChartSubstitute chart qS) qR hslowEq hratEq t ht j hj
  rw [← heq]
  exact hnext t ht j hj

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def CertifiedFullChartDetectedDecomposition : Prop :=
  ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    K' ⊆ K₀ ∧
    (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
    (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
    (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
    (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
    (∀ t ∈ K', ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
            (realChartSubstitute chart pS))⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
        fast.baseChange ℝ) ∧
    (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
      (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
      pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
      K' = fullTaggedGradedBaseIntersection J k K₀
        (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
    ∀ t ∈ K', fast.mkQ.baseChange ℝ
      (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute chart pS) + eval₂ t pR

omit [Fintype η] in

set_option maxHeartbeats 400000 in
theorem fullChart_grade_quotient_of_low_value
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (K : η → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
    (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal)
    (hvalue : ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ),
      (∀ i, z ∈ K i) →
      eval₂ (Sum.elim u z) (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord)) =
        eval₂ (Sum.elim u z) (realChartSubstitute
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (majorTranslationTopCoordinates (lowTaggedWeight J k)
              (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))) slow) +
          eval₂ (Sum.elim u z) rat) :
    ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
  let P := F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord
  let lowchart := normalizedRealPolynomialChart (fun i => (N i : ℝ))
    (majorTranslationTopCoordinates (lowTaggedWeight J k)
      (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))
  have hP : DegreeLE wt k P := by
    rw [degreeLE_iff]
    intro α hα
    by_contra hle
    have hz := F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF wt fast k
      (left⁻¹ * Z * right⁻¹).coord α (ne_of_gt (Nat.lt_of_not_ge hle))
    exact Finsupp.mem_support_iff.mp hα hz
  have hquotLow : ∀ t ∈ fullTaggedGradedBaseIntersection J k K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (lowTaggedVectorExtend J k (realChartSubstitute lowchart slow)) +
          eval₂ t (lowTaggedVectorExtend J k rat) := by
    intro t ht
    have h := hvalue (fun i => t (Sum.inl i))
      (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) ht.2
    have hsplit : Sum.elim (fun i => t (Sum.inl i))
        (fun b => t (lowTaggedVariableEmbedding J k (Sum.inr b))) =
        t ∘ lowTaggedVariableEmbedding J k := by
      funext i
      cases i <;> rfl
    rw [hsplit] at h
    rw [← F.realSymbolGradeQuotientPolynomial_eval,
      lowTaggedVectorRestrict_eval₂ J k _ hP, lowTaggedVectorExtend_eval₂,
      lowTaggedVectorExtend_eval₂]
    with_reducible exact h
  intro t ht
  have h := hquotLow t ht
  dsimp only [lowchart] at h
  simp only [lowTaggedVectorExtend_majorChart J k poly c (fun i => (N i : ℝ)) slow] at h
  with_reducible exact h

theorem certifiedFullChartDetectedDecomposition_of_vector_detection
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (hsection : ∀ y, fast.mkQ (lift y) = y)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
    (hdetected : MajorPhaseVectorDetectedConclusion (L := M) J k Utag poly c N budget basis
      (lowTaggedVectorRestrict J k
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord))) :
    CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, _, hcoeff,
    hq, hqB, hgrid, _, _, hvalue⟩ := hdetected
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  have hquot := fullChart_grade_quotient_of_low_value F b ω hF J k fast
    Z left right K₀ poly N c K slow rat (by with_reducible exact hvalue)
  have hstep := F.restricted_symbol_major_grade_step b ω hF wt fast hfast lift hsection
    k Z left right K₀ (fullTaggedGradedBaseIntersection J k K₀ K)
    (fullTaggedGradedBaseIntersection_subset J k K₀ K)
    (fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀)
    (realChartSubstitute chart (lowTaggedVectorExtend J k slow))
    (lowTaggedVectorExtend J k rat) hlower (by with_reducible exact hquot)
  have hcap := lowTaggedVectorExtend_coordinate_coefficient_bound J k
    (fun i => (basis.coord i).toAddMonoidHom) slow (Real.exp budget)
    (Real.exp_pos budget).le hcoeff
  have hden := lowTaggedVectorExtend_coefficients_grid J k
    (fun i => (basis.coord i).toAddMonoidHom) rat q hgrid
  obtain ⟨A, D, hA, hD, _, _, _, _, hnext⟩ := hstep
  have hAc : A = F.restrictedMajorCorrection b ω hF wt fast lift k
      (realChartSubstitute chart (lowTaggedVectorExtend J k slow)) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hA
  have hDc : D = F.restrictedMajorCorrection b ω hF wt fast lift k
      (lowTaggedVectorExtend J k rat) := by
    apply NilpotentLieBCHGroup.ext
    dsimp only [restrictedMajorCorrection]
    with_reducible exact hD
  rw [hAc, hDc] at hnext
  have hcertificate := majorPhase_rationalTaggedConstraintCertificate J k
    detectedfast gen K₀ budget hgen
  unfold CertifiedFullChartDetectedDecomposition
  refine ⟨lowTaggedVectorExtend J k slow, lowTaggedVectorExtend J k rat, q,
    fullTaggedGradedBaseIntersection J k K₀ K, hq, hqB,
    fullTaggedGradedBaseIntersection_subset J k K₀ K,
    fullTaggedGradedBaseIntersection_rat_dilation J k K₀ K hgrade hK₀,
    ?_, hcap, hden, ?_, ?_, hcertificate, ?_⟩
  · intro t ht hU
    refine ⟨ht, ?_⟩
    intro i
    change lowTaggedCoordinates J k (fun j a => t (Sum.inr ⟨j, a⟩)) ∈ K i
    apply (lowTaggedCoordinates_mem_iff J k (K i) (hgrade i) _).mpr
    intro j
    exact le_lowTaggedSubspaceFamily J k Utag (K i) (hretain i) j (hU j)
  · with_reducible exact hnext
  · exact ⟨detectedfast, slow, rat, rfl, rfl, rfl⟩
  · with_reducible exact hquot

theorem CertifiedFullChartDetectedDecomposition.to_correctionData
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    CertifiedFullChartGradeCorrectionData F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget := by
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    hnext, horigin, hcertificate, _⟩ := h
  refine ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    ?_, horigin, hcertificate⟩
  with_reducible exact hnext

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

theorem weightedHomogeneousComponent_totalDegree_le_of_positive
    {σ R : Type*} [CommRing R] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (k : ℕ) (p : MvPolynomial σ R) :
    (MvPolynomial.weightedHomogeneousComponent w k p).totalDegree ≤ k := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro α hα
  rw [MvPolynomial.support_weightedHomogeneousComponent] at hα
  exact (exponentSum_le_positive_weight w hw α).trans (Finset.mem_filter.mp hα).2.le

namespace VectorPolynomial

variable {σ R V η : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem weightedHomogeneousPart_idempotent (w : σ → ℕ) (k : ℕ)
    (p : VectorPolynomial σ R V) :
    weightedHomogeneousPart w k (weightedHomogeneousPart w k p) =
      weightedHomogeneousPart w k p :=
  weightedHomogeneousPart_eq_self (weightedHomogeneousPart_homogeneous w k p)

theorem weightedHomogeneousPart_coordinate_bound (w : σ → ℕ) (k : ℕ)
    (f : η → V →+ ℝ) (p : VectorPolynomial σ R V) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ α i, |f i (coefficients p α)| ≤ C) :
    ∀ α i, |f i (coefficients (weightedHomogeneousPart w k p) α)| ≤ C := by
  intro α i
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α i
  · simpa only [map_zero, abs_zero] using hC

theorem weightedHomogeneousPart_coefficients_grid (w : σ → ℕ) (k : ℕ)
    (f : η → V →+ ℝ) (p : VectorPolynomial σ R V) (q : ℕ)
    (hp : ∀ α, (fun i => f i (coefficients p α)) ∈ realDenominatorGrid q) :
    ∀ α, (fun i => f i (coefficients (weightedHomogeneousPart w k p) α)) ∈
      realDenominatorGrid q := by
  intro α
  simp only [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α
  · refine ⟨fun _ => 0, ?_⟩
    ext i
    simp

theorem weightedHomogeneousPart_coordinate_totalDegree_le
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (k : ℕ) (f : V →+ ℝ)
    (p : VectorPolynomial σ R V) :
    (coordinate f (weightedHomogeneousPart w k p)).totalDegree ≤ k := by
  rw [coordinate_weightedHomogeneousPart]
  exact weightedHomogeneousComponent_totalDegree_le_of_positive w hw k _

end VectorPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (fast : Submodule ℚ F.AssociatedGraded)
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorCorrection_weightedHomogeneousPart (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) :
    F.restrictedMajorCorrection b ω hF w fast lift k (weightedHomogeneousPart w k p) =
      F.restrictedMajorCorrection b ω hF w fast lift k p := by
  simp only [restrictedMajorCorrection, weightedHomogeneousPart_idempotent]

variable {m : ℕ} {X : Type} (J : Fin m → Type)

theorem restrictedMajorCorrection_fullChart_homogeneous (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (p : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) :
    F.restrictedMajorCorrection b ω hF (fullTaggedVariableWeight J) fast lift k
      (realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
        (weightedHomogeneousPart (fullTaggedVariableWeight J) k p)) =
    F.restrictedMajorCorrection b ω hF (fullTaggedVariableWeight J) fast lift k
      (realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) p) := by
  rw [realChartSubstitute_weightedHomogeneousPart _ _ _
    (fullTaggedMajorChart_homogeneous J poly H),
    restrictedMajorCorrection_weightedHomogeneousPart]

theorem fullChart_quotient_identity_homogeneous (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight J))
    (K : Set (X ⊕ (Σ j, J j) → ℝ))
    (hK : ∀ t ∈ K, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K)
    (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (hquot : ∀ t ∈ K, fast.mkQ.baseChange ℝ
      (F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) k t
        (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute
        (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) pS) + eval₂ t pR) :
    ∀ t ∈ K, eval₂ t
      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) fast k
        (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute
        (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
          (weightedHomogeneousPart (fullTaggedVariableWeight J) k pS)) +
      eval₂ t (weightedHomogeneousPart (fullTaggedVariableWeight J) k pR) := by
  intro t ht
  rw [realChartSubstitute_weightedHomogeneousPart _ _ _
    (fullTaggedMajorChart_homogeneous J poly H)]
  apply eval₂_weightedHomogeneousPart_decomposition_on _ _ _ _ K hK k
    (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF _ fast k _) _ t ht
  intro x hx
  rw [realSymbolGradeQuotientPolynomial_eval]
  exact hquot x hx

section Certified

variable {η : Type*} [Fintype η] [∀ j, Fintype (J j)] (k : ℕ)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

theorem CertifiedFullChartDetectedDecomposition.exists_homogeneous
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
      (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pS α = 0) ∧
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pR α = 0) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pS).totalDegree ≤ k) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pR).totalDegree ≤ k) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
      K' ⊆ K₀ ∧
      (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
      (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
      (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
      (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
      (∀ t ∈ K', ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF wt j t
          ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
              (realChartSubstitute chart pS))⁻¹ * Z *
            (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
          fast.baseChange ℝ) ∧
      (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
        pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
        K' = fullTaggedGradedBaseIntersection J k K₀
          (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
      RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
      ∀ t ∈ K', eval₂ t
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart pS) + eval₂ t pR := by
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    hnext, horigin, hcertificate, hquot⟩ := h
  refine ⟨weightedHomogeneousPart wt k pS, weightedHomogeneousPart wt k pR, q, K',
    weightedHomogeneousPart_homogeneous wt k pS,
    weightedHomogeneousPart_homogeneous wt k pR,
    (fun i => weightedHomogeneousPart_coordinate_totalDegree_le wt
      (fullTaggedVariableWeight_pos J) k (basis.coord i).toAddMonoidHom pS),
    (fun i => weightedHomogeneousPart_coordinate_totalDegree_le wt
      (fullTaggedVariableWeight_pos J) k (basis.coord i).toAddMonoidHom pR),
    hq, hqB, hsub, hdilate, hretain,
    weightedHomogeneousPart_coordinate_bound wt k (fun i => (basis.coord i).toAddMonoidHom)
      pS (Real.exp_nonneg budget) hcap,
    weightedHomogeneousPart_coefficients_grid wt k (fun i => (basis.coord i).toAddMonoidHom)
      pR q hgrid, ?_, ?_, hcertificate, ?_⟩
  · intro t ht j hj
    rw [restrictedMajorCorrection_fullChart_homogeneous,
      restrictedMajorCorrection_weightedHomogeneousPart]
    with_reducible exact hnext t ht j hj
  · obtain ⟨detectedfast, slow, rat, hs, hr, hK⟩ := horigin
    refine ⟨detectedfast, weightedHomogeneousPart (lowTaggedVariableWeight J k) k slow,
      weightedHomogeneousPart (lowTaggedVariableWeight J k) k rat, ?_, ?_, hK⟩
    · rw [hs, lowTaggedVectorExtend_weightedHomogeneousPart]
    · rw [hr, lowTaggedVectorExtend_weightedHomogeneousPart]
  · with_reducible
      exact fullChart_quotient_identity_homogeneous F b ω hF fast J k poly
        (fun i => (N i : ℝ)) Z left right K' hdilate pS pR (by with_reducible exact hquot)

end Certified

end NilpotentLieFiltration
end Erdos3

end

end OAI

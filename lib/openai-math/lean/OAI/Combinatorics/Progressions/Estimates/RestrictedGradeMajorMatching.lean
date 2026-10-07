import OAI.Combinatorics.Progressions.Geometry.RestrictedGradeScalarCoordinates
import OAI.Combinatorics.Progressions.Polynomial.MajorPhaseDetectedDecomposition

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

def RestrictedMajorGradeCorrectionConclusion
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (wt : σ → ℕ) (fast : Submodule ℚ F.AssociatedGraded)
    (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
    (k : ℕ) (Z left right : F.RealPolynomialSymbolGroup wt)
    (K : Set (σ → ℝ))
    (slow rat : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) : Prop :=
  ∃ Astep Dstep : F.RealPolynomialSymbolGroup wt,
    Astep.coord = F.homogeneousQuotientSymbolLift b ω hF wt k (lift.baseChange ℝ)
      (weightedHomogeneousPart wt k slow) ∧
    Dstep.coord = F.homogeneousQuotientSymbolLift b ω hF wt k (lift.baseChange ℝ)
      (weightedHomogeneousPart wt k rat) ∧
    Astep.coord ∈ (F.polynomialSymbolFiltration wt).realification.layer k ∧
    Dstep.coord ∈ (F.polynomialSymbolFiltration wt).realification.layer k ∧
    (left * Astep) * ((left * Astep)⁻¹ * Z * (Dstep * right)⁻¹) * (Dstep * right) = Z ∧
    (∀ t, ∀ j < k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * Astep)⁻¹ * Z * (Dstep * right)⁻¹).coord =
      F.realSymbolGradeEvaluation b ω hF wt j t (left⁻¹ * Z * right⁻¹).coord) ∧
    ∀ t ∈ K, ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * Astep)⁻¹ * Z * (Dstep * right)⁻¹).coord ∈ fast.baseChange ℝ

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

local notation "base" => Fin (Fintype.card (LowTaggedIndex J k))
local notation "w" => lowTaggedWeight J k
local notation "wt" => Sum.elim (fun _ : X => 1) w
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)

variable (Z left right : F.RealPolynomialSymbolGroup
  (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)))
variable (K₀ : Set (X ⊕ Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ) (N : X → ℕ) (budget : ℝ)

local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (majorTranslationTopCoordinates w
    (fun i => lowTaggedPolynomial J k poly i - MvPolynomial.C (c i)))

def RestrictedDetectedMajorGradeConclusion : Prop :=
  ∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra w k))
    (gen : η → Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w k) M)) → weightedSubalgebra w k)
    (slow rat : VectorPolynomial (X ⊕ base) ℚ quotientReal) (q : ℕ),
    (∀ i, (finrank ℚ (PairAlgebra (weightedSubalgebra w k) M) : ℝ) ≤ budget ∧
      Submodule.span ℚ (Set.range (gen i)) = (detectedfast i).toSubmodule ∧
      BasisGradedSubmodule (weightedBasis w k (lowTaggedWeight_pos J k))
        (weightedBasisGrade w k) (detectedfast i).toSubmodule ∧
      ∀ j a, rationalLogHeight
        ((weightedBasis w k (lowTaggedWeight_pos J k)).repr (gen i j) a) ≤ budget) ∧
    (∀ i, BasisGradedSubmodule (Pi.basisFun ℝ base) w
      (majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    (∀ i h, lowTaggedRetained J k Utag h ≤ majorPhaseDetectedRealBase J k (detectedfast i)) ∧
    (∀ i α, |basis.coord i (coefficients slow α)| ≤ Real.exp budget) ∧
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    (∀ i, realPolynomialCoefficientGrid q (coordinate (basis.coord i).toAddMonoidHom rat)) ∧
    RestrictedMajorGradeCorrectionConclusion (σ := X ⊕ base) F b ω hF wt fast lift k Z left right
      (gradedBaseIntersection K₀ (fun i => majorPhaseDetectedRealBase J k (detectedfast i)))
      (realChartSubstitute chart slow) rat

theorem restrictedDetectedMajorGradeConclusion_of_vector_detection
    (hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
    (hsection : ∀ y, fast.mkQ (lift y) = y)
    (hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ wt i * t i) ∈ K₀)
    (hlower : ∀ t ∈ K₀, ∀ j < k,
      F.realSymbolGradeEvaluation (σ := X ⊕ base) b ω hF wt j t
        (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
    (hdetected : MajorPhaseVectorDetectedConclusion (L := M) J k Utag poly c N budget basis
      (F.realSymbolGradeQuotientPolynomial (σ := X ⊕ base) b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord)) :
    RestrictedDetectedMajorGradeConclusion (M := M)
      F b ω hF J k fast basis lift Z left right K₀ Utag poly c N budget := by
  obtain ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain, _, hcoeff,
    hq, hqB, hgrid, _, _, hvalue⟩ := hdetected
  let K := fun i => majorPhaseDetectedRealBase J k (detectedfast i)
  have hquot : ∀ t ∈ gradedBaseIntersection K₀ K,
      fast.mkQ.baseChange ℝ
        (F.realSymbolGradeEvaluation (σ := X ⊕ base) b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart slow) + eval₂ t rat := by
    intro t ht
    have h := hvalue (fun i => t (Sum.inl i)) (fun i => t (Sum.inr i)) ht.2
    have hsplit : Sum.elim (fun i => t (Sum.inl i)) (fun i => t (Sum.inr i)) = t := by
      funext i
      cases i <;> rfl
    rw [hsplit, F.realSymbolGradeQuotientPolynomial_eval] at h
    with_reducible exact h
  have hstep := F.restricted_symbol_major_grade_step (σ := X ⊕ base) b ω hF wt fast hfast lift hsection
    k Z left right K₀ (gradedBaseIntersection K₀ K) (gradedBaseIntersection_subset K₀ K)
    (gradedBaseIntersection_rat_dilation w K₀ K hgrade hK₀)
    (realChartSubstitute chart slow) rat hlower hquot
  unfold RestrictedDetectedMajorGradeConclusion
  refine ⟨detectedfast, gen, slow, rat, q, hgen, hgrade, hretain,
    hcoeff, hq, hqB, hgrid, ?_⟩
  unfold RestrictedMajorGradeCorrectionConclusion
  with_reducible exact hstep

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_restricted_grade_scalar_major_detections (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (residual : F.RealPolynomialSymbol (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)))
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (F.realSymbolGradeQuotientPolynomial b ω hF
              (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual)) β (R j).eval u‖) →
      ∀ j, MajorPhaseDetectedConclusion (L := M) J k U poly c
        (coordinate (basis.coord j).toAddMonoidHom
          (F.realSymbolGradeQuotientPolynomial b ω hF
            (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual))
        N ((p + C) ^ C) := by
  obtain ⟨C, hC, hdetect⟩ := exists_majorPhase_detected_decomposition m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis residual
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr j
  exact hdetect J (W j) D htk (R j) N poly hpoly U hcoeff Ψ c
    (coordinate (basis.coord j).toAddMonoidHom
      (F.realSymbolGradeQuotientPolynomial b ω hF
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual))
    (F.realSymbolGradeQuotientPolynomial_coordinate_weightedSupportLE b ω hF
      (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast basis k residual j)
    β hβ p Rrank hp (hR j) (hRcap j) hdim (hmod j) (hcover j) hLip hΨ hN hRrank hrank (hcorr j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_restricted_grade_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (residual : F.RealPolynomialSymbol (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)))
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (F.realSymbolGradeQuotientPolynomial b ω hF
              (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual)) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis
        (F.realSymbolGradeQuotientPolynomial b ω hF
          (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual) := by
  obtain ⟨C, hC, hdetect⟩ := exists_restricted_grade_scalar_major_detections m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis residual
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hscalar := hdetect F b ω hF J fast basis residual W D htk R N poly hpoly U hcoeff
    Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  exact majorPhaseVectorDetectedConclusion_of_coordinates J k U poly c N ((p + C) ^ C) basis
    (F.realSymbolGradeQuotientPolynomial b ω hF
      (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual)
    (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF
      (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k residual) hscalar

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_restricted_grade_major_matching (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)))
      (K₀ : Set (X ⊕ Fin (Fintype.card (LowTaggedIndex J k)) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ Sum.elim (fun _ : X => 1) (lowTaggedWeight J k) i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (F.realSymbolGradeQuotientPolynomial b ω hF
              (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) fast k (left⁻¹ * Z * right⁻¹).coord)) β (R j).eval u‖) →
      RestrictedDetectedMajorGradeConclusion (M := M) F b ω hF J k fast basis lift
        Z left right K₀ U poly c N ((p + C) ^ C) := by
  obtain ⟨C, hC, hdetect⟩ := exists_restricted_grade_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower periodCap coverCap Lip W D htk R N poly hpoly U hcoeff
    Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hdetected := hdetect F b ω hF J fast basis (left⁻¹ * Z * right⁻¹).coord
    W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim hmod hcover
    hLip hΨ hN hRrank hrank hcorr
  exact restrictedDetectedMajorGradeConclusion_of_vector_detection F b ω hF J k fast basis lift
    Z left right K₀ U poly c N ((p + C) ^ C) hfast hsection hK₀ hlower hdetected

end Erdos3.NilpotentLieFiltration

end

end OAI

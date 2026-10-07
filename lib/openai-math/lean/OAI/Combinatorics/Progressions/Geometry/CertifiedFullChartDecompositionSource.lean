import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateCommonFastGeometry
import OAI.Combinatorics.Progressions.Estimates.FullRestrictedGradeMajorMatching
import OAI.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

def FullChartMajorCorrelation
    {m : ℕ} {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (D : RationalFilteredNilmanifold M t e)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ) (C : ℕ) : Prop :=
  ∃ (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (R : η → D.Niltest (fun _ : X => 1))
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ),
    (∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j)) ∧
    (∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j) ∧
    (∀ u ∈ integerBox N, ∀ i,
      |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
        c i - (β u i : ℝ)| ≤ 1 / 2) ∧
    0 ≤ p ∧ (∀ j, (R j).ComplexityLE p) ∧
    (∀ j, ((R j).normBound : ℝ) ≤ 1) ∧
    ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p ∧
    (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) ∧
    (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) ∧
    (Lip : ℝ) ≤ Real.exp p ∧ (Ψ.lip : ℝ) ≤ Real.exp p ∧
    (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) ∧
    Real.exp ((p + C) ^ C) ≤ Rrank ∧
    (∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) ∧
    (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
      (W j).eval N poly u * majorPhaseSample J k poly Ψ c
        (coordinate (basis.coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))) β (R j).eval u‖)

theorem exists_full_chart_grade_correction_of_major_correlation
    (m k : ℕ) (hk : 0 < k) :
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
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      FullChartMajorCorrelation F b ω hF J k fast basis Z left right D N poly U p Rrank C →
      FullChartGradeCorrectionData F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hmatching⟩ := exists_full_restricted_grade_major_matching m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower D htk N poly U p Rrank hcorrelation
  obtain ⟨periodCap, coverCap, Lip, W, R, Ψ, c, β, hpoly, hcoeff, hβ,
    hp, hR, hRcap, hdim, hmod, hcover, hLip, hΨ, hN, hRrank, hrank, hcorr⟩ := hcorrelation
  have hdetected := hmatching F b ω hF J fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower W D htk R N poly hpoly U hcoeff Ψ c β hβ
    p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hchart := fullChartDetectedMajorGradeConclusion_of_fullTagged F b ω hF J k fast
    basis lift Z left right K₀ U poly c N ((p + C) ^ C) hdetected
  exact fullChartGradeCorrectionData_of_detected F b ω hF J k fast basis lift
    Z left right K₀ U poly N ((p + C) ^ C) c hK₀ hchart

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

def FullChartControlledFactors
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (budget : ℝ) : Prop :=
  ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
    ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
        F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
      F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
        realPolynomialChartSubstitution
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (fullTaggedMajorTopCoordinates J poly)) Echart ∧
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
        (Real.exp budget) Echart.coord ∧
      CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
        (F.realGradedSymbolPolynomialHom b ω hF
          (fullTaggedVariableWeight (X := X) J) right).coord

theorem FullChartControlledFactors.mono
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget budget' : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (hle : budget ≤ budget') :
    FullChartControlledFactors F b ω hF J poly N left right budget' := by
  obtain ⟨q, hq, hqB, Echart, hchart, hslow, hgrid⟩ := h
  refine ⟨q, hq, hqB.trans (Real.exp_le_exp.mpr hle), Echart, hchart, ?_, hgrid⟩
  exact CoefficientBound.mono _ _ (fun _ => zero_lt_one) hslow (Real.exp_le_exp.mpr hle)

def FullChartControlledCorrelationSource
    {m : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {M : ℕ → Type} [∀ n, LieRing (M n)] [∀ n, LieAlgebra ℚ (M n)] {edim : ℕ → ℕ}
    [∀ n, TopologicalSpace (ℝ ⊗[ℚ] M n)]
    [∀ n, IsTopologicalAddGroup (ℝ ⊗[ℚ] M n)]
    [∀ n, ContinuousSMul ℝ (ℝ ⊗[ℚ] M n)] [∀ n, T2Space (ℝ ⊗[ℚ] M n)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (D : ∀ n, RationalFilteredNilmanifold (M n) n (edim n))
    (pPhase Rrank : ℝ) (Cphase : ℕ → ℕ) (controlBudget : ℝ) : Prop :=
  ∀ n < s,
    ∀ (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K : Set (X ⊕ (Σ j, J j) → ℝ)),
      K ⊆ Kinitial →
      (∀ t ∈ K, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K) →
      (∀ t ∈ Kinitial, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      (∀ t ∈ K, ∀ j < n + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ) →
      FullChartControlledFactors F b ω hF J poly N left right controlBudget →
      FullChartMajorCorrelation F b ω hF J (n + 1) fast basis Z left right
        (D n) N poly Utag pPhase Rrank (Cphase n)

def FullChartControlledCorrelationSourceStages
    {m : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    {M : ℕ → Type} [∀ n, LieRing (M n)] [∀ n, LieAlgebra ℚ (M n)] {edim : ℕ → ℕ}
    [∀ n, TopologicalSpace (ℝ ⊗[ℚ] M n)]
    [∀ n, IsTopologicalAddGroup (ℝ ⊗[ℚ] M n)]
    [∀ n, ContinuousSMul ℝ (ℝ ⊗[ℚ] M n)] [∀ n, T2Space (ℝ ⊗[ℚ] M n)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (D : ∀ n, RationalFilteredNilmanifold (M n) n (edim n))
    (pPhase : ℕ → ℝ) (Rrank : ℝ) (Cphase : ℕ → ℕ) (controlBudget : ℕ → ℝ) : Prop :=
  ∀ n < s,
    ∀ (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K : Set (X ⊕ (Σ j, J j) → ℝ)),
      K ⊆ Kinitial →
      (∀ t ∈ K, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K) →
      (∀ t ∈ Kinitial, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      (∀ t ∈ K, ∀ j < n + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ) →
      FullChartControlledFactors F b ω hF J poly N left right (controlBudget n) →
      FullChartMajorCorrelation F b ω hF J (n + 1) fast basis Z left right
        (D n) N poly Utag (pPhase n) Rrank (Cphase n)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_bounded_full_chart_major_iteration (m s a : ℕ) :
    ∃ (Cphase : ℕ → ℕ) (Ccontrol : ℕ), (∀ n, 2 ≤ Cphase n) ∧ 2 ≤ Ccontrol ∧
    ∀ {X L ι Γ : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded) (v : Γ → F.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = fast)
      (H : ℕ) (_hHpos : 1 ≤ H)
      (_hv : ∀ i j, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H)
      (p₀ : ℝ) (_hp₀ : 0 ≤ p₀)
      (_hrows : (Fintype.card ι : ℝ) ≤ p₀) (_hcols : (Fintype.card Γ : ℝ) ≤ p₀)
      (_hH : (H : ℝ) ≤ Real.exp p₀)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast),
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
        ∃ (eQ : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ fast))
          (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded) (qS : ℕ),
          Function.RightInverse lift fast.mkQ ∧
          Function.RightInverse (lift.baseChange ℝ) (fast.mkQ.baseChange ℝ) ∧
          0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p₀ + 2) ^ 47) ∧
          (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p₀ + 2) ^ 45)) ∧
          (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
          (∀ j i, RationalHeightLE (((eQ.coord j).comp fast.mkQ)
            (F.associatedGradedBasis b ω hF i)) ⌈Real.exp ((p₀ + 2) ^ 7)⌉₊) ∧
      ∀ {M : ℕ → Type} [∀ n, LieRing (M n)] [∀ n, LieAlgebra ℚ (M n)]
        [∀ n, TopologicalSpace (ℝ ⊗[ℚ] M n)] [∀ n, IsTopologicalAddGroup (ℝ ⊗[ℚ] M n)]
        [∀ n, ContinuousSMul ℝ (ℝ ⊗[ℚ] M n)] [∀ n, T2Space (ℝ ⊗[ℚ] M n)]
        (edim : ℕ → ℕ) (D : ∀ n, RationalFilteredNilmanifold (M n) n (edim n))
        (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
        (_hKinitial : ∀ t ∈ Kinitial, ∀ r : ℚ,
          (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ Kinitial)
        (Utag : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (pPhase Bpast : ℕ → ℝ) (Rrank : ℝ) (_hBpast : ∀ n ≤ s, 0 ≤ Bpast n)
        (_hBmono : Monotone Bpast)
        (_hphaseBudget : ∀ n < s, (pPhase n + Cphase n) ^ Cphase n ≤ Bpast (n + 1))
        (Hcontrol : ℕ) (pControl : ℕ → ℝ),
        1 ≤ Hcontrol → (∀ n ≤ s, 0 ≤ pControl n) →
        (∀ n ≤ s, (Fintype.card ι : ℝ) ≤ pControl n) →
        (∀ n ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl n) →
        (∀ n ≤ s, (Hcontrol : ℝ) ≤ Real.exp (pControl n)) →
        (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
          ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) Hcontrol) →
        (∀ n ≤ s, Real.exp ((p₀ + 2) ^ 47) * Real.exp ((s : ℝ) * d * Bpast n) ≤
          Real.exp (pControl n)) →
        (∀ n ≤ s, (d : ℝ) * Real.exp ((p₀ + 2) ^ 45) * Real.exp (Bpast n) ≤
          Real.exp ((pControl n + 2) ^ a)) →
        FullChartControlledCorrelationSourceStages F b ω hF J fast (eQ.baseChange ℝ) Z
          Kinitial Utag poly N D pPhase Rrank Cphase (fun n => (pControl n + Ccontrol) ^ Ccontrol) →
        ∃ history : FullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
          Z Kinitial Utag poly N (Bpast s) s,
          FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
            ((pControl s + Ccontrol) ^ Ccontrol) ∧
          ∀ t ∈ history.K,
            eval₂ t (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
              (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ := by
  classical
  choose Cphase hCphase hstep using
    (fun n : ℕ => exists_full_chart_grade_correction_of_major_correlation
      m (n + 1) (Nat.zero_lt_succ n))
  obtain ⟨Ccontrol, hCcontrol, hprefix⟩ := exists_restricted_chart_prefix_control s a
  refine ⟨Cphase, Ccontrol, hCphase, hCcontrol, ?_⟩
  intro X L ι Γ _ _ _ _ _ _ F b ω hF J _ fast v hspan H hHpos hv
    p₀ hp₀ hrows hcols hH hfast
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates (F.associatedGradedBasis b ω hF)
      fast v hspan hHpos hv hp₀ hrows hcols hH
  refine ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord, ?_⟩
  intro M _ _ _ _ _ _ edim D Z Kinitial hKinitial Utag poly N pPhase Bpast Rrank
    hBpast hBmono hphaseBudget Hcontrol pControl hHcontrol hpControl hι hσ hHexp hstructure
    hdenbudget hcost hsource
  have hcontrol : ∀ n ≤ s,
      ∀ history : FullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast n) n,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl n + Ccontrol) ^ Ccontrol) := by
    intro n hn history
    have hdenbudget' : (qS : ℝ) *
        Real.exp ((s : ℝ) * (Fintype.card (Fin d) : ℝ) * Bpast n) ≤ Real.exp (pControl n) := by
      simpa only [Fintype.card_fin] using
        (mul_le_mul_of_nonneg_right hqSB (Real.exp_nonneg _)).trans (hdenbudget n hn)
    have hcost' : (Fintype.card (Fin d) : ℝ) * Real.exp ((p₀ + 2) ^ 45) *
        Real.exp (Bpast n) ≤ Real.exp ((pControl n + 2) ^ a) := by
      simpa only [Fintype.card_fin] using hcost n hn
    obtain ⟨q, hq, hqB, _hdiv, Echart, hE, hEbound, hRgrid⟩ :=
      hprefix F b ω hF (fullTaggedVariableWeight J) (fullTaggedVariableWeight_pos J)
        Hcontrol (pControl n) hHcontrol (hpControl n hn) (hι n hn) (hσ n hn) (hHexp n hn) hstructure
        fast lift (eQ.baseChange ℝ) (Real.exp ((p₀ + 2) ^ 45)) (Bpast n) qS (hBpast n hn) hqS
        hdenbudget' hcost' hentry hgrid
        (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
        (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ)))
        history.slow history.rat history.q n hn history.q_pos history.q_bound
        history.slow_bound history.rat_grid
    unfold FullChartControlledFactors FullChartFiniteHistory.outer
    with_reducible exact ⟨q, hq, hqB, Echart, hE, hEbound, hRgrid⟩
  have hexists : ∀ n ≤ s,
      Nonempty (FullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast n) n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨FullChartFiniteHistory.initial F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast 0) hKinitial⟩
    | succ n ih =>
      intro hn
      obtain ⟨history⟩ := ih (by omega)
      have hlower : ∀ t ∈ history.K, ∀ j < n + 1,
          F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
            (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
        intro t ht j hj
        with_reducible exact history.invariant_outer t ht j (by omega)
      have hcorr := hsource n (by omega) history.outer.1 history.outer.2 history.K
        history.subset history.dilation history.retained hlower (hcontrol n (by omega) history)
      have hdata := hstep n F b ω hF J fast (eQ.baseChange ℝ) lift hfast hsection
        Z history.outer.1 history.outer.2 history.K history.dilation hlower
        (D n) (Nat.lt_succ_self n) N poly Utag (pPhase n) Rrank hcorr
      let larger := history.mono_bound (hBmono (Nat.le_succ n))
      have hdata' : FullChartGradeCorrectionData F b ω hF J (n + 1) fast
          (eQ.baseChange ℝ) lift Z larger.outer.1 larger.outer.2 larger.K Utag poly N
          ((pPhase n + Cphase n) ^ Cphase n) := by
        simpa only [larger, FullChartFiniteHistory.outer_mono_bound,
          FullChartFiniteHistory.mono_bound_K] using hdata
      obtain ⟨next, _⟩ := larger.exists_step ((pPhase n + Cphase n) ^ Cphase n)
        (hphaseBudget n (by omega)) hdata'
      exact ⟨next⟩
  obtain ⟨history⟩ := hexists s le_rfl
  refine ⟨history, hcontrol s le_rfl history, ?_⟩
  intro t ht
  apply (F.restricted_symbol_grade_terminal b ω hF (fullTaggedVariableWeight J)
    fast hfast _ t).mpr
  with_reducible exact history.invariant_outer t ht

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

structure FullChartMajorCorrelationWitness
    {m : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ) (C : ℕ) where
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  step : ℕ
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L step dim
  lower : step < k
  correlation : FullChartMajorCorrelation F b ω hF J k fast basis
    Z left right model N poly U p Rrank C

attribute [local instance] FullChartMajorCorrelationWitness.lie
  FullChartMajorCorrelationWitness.algebra FullChartMajorCorrelationWitness.topology
  FullChartMajorCorrelationWitness.topologicalAdd FullChartMajorCorrelationWitness.continuousSMul
  FullChartMajorCorrelationWitness.hausdorff

theorem exists_full_chart_grade_correction_of_major_correlation_witness
    (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
        Z left right N poly U p Rrank C) →
      FullChartGradeCorrectionData F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_full_chart_grade_correction_of_major_correlation m k hk
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower N poly U p Rrank hwitness
  obtain ⟨witness⟩ := hwitness
  exact hstep F b ω hF J fast basis lift hfast hsection Z left right K₀ hK₀ hlower
    witness.model witness.lower N poly U p Rrank witness.correlation

def BundledFullChartControlledCorrelationSourceStages
    {m : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
    (Utag : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (pPhase : ℕ → ℝ) (Rrank : ℝ) (Cphase : ℕ → ℕ) (controlBudget : ℕ → ℝ) : Prop :=
  ∀ n < s,
    ∀ (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K : Set (X ⊕ (Σ j, J j) → ℝ)),
      K ⊆ Kinitial →
      (∀ t ∈ K, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K) →
      (∀ t ∈ Kinitial, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      (∀ t ∈ K, ∀ j < n + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ) →
      FullChartControlledFactors F b ω hF J poly N left right (controlBudget n) →
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
        Z left right N poly Utag (pPhase n) Rrank (Cphase n))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_bounded_bundled_full_chart_major_iteration (m s a : ℕ) :
    ∃ (Cphase : ℕ → ℕ) (Ccontrol : ℕ), (∀ n, 2 ≤ Cphase n) ∧ 2 ≤ Ccontrol ∧
    ∀ {X L ι Γ : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype Γ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded) (v : Γ → F.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = fast)
      (H : ℕ) (_hHpos : 1 ≤ H)
      (_hv : ∀ i j, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr (v j) i) H)
      (p₀ : ℝ) (_hp₀ : 0 ≤ p₀)
      (_hrows : (Fintype.card ι : ℝ) ≤ p₀) (_hcols : (Fintype.card Γ : ℝ) ≤ p₀)
      (_hH : (H : ℝ) ≤ Real.exp p₀)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast),
      ∃ d : ℕ, d ≤ Fintype.card ι ∧
        ∃ (eQ : Basis (Fin d) ℚ (F.AssociatedGraded ⧸ fast))
          (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded) (qS : ℕ),
          Function.RightInverse lift fast.mkQ ∧
          Function.RightInverse (lift.baseChange ℝ) (fast.mkQ.baseChange ℝ) ∧
          0 < qS ∧ (qS : ℝ) ≤ Real.exp ((p₀ + 2) ^ 47) ∧
          (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Real.exp ((p₀ + 2) ^ 45)) ∧
          (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
            (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS) ∧
          (∀ j i, RationalHeightLE (((eQ.coord j).comp fast.mkQ)
            (F.associatedGradedBasis b ω hF i)) ⌈Real.exp ((p₀ + 2) ^ 7)⌉₊) ∧
      ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
        (_hKinitial : ∀ t ∈ Kinitial, ∀ r : ℚ,
          (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ Kinitial)
        (Utag : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (pPhase Bpast : ℕ → ℝ) (Rrank : ℝ) (_hBpast : ∀ n ≤ s, 0 ≤ Bpast n)
        (_hBmono : Monotone Bpast)
        (_hphaseBudget : ∀ n < s, (pPhase n + Cphase n) ^ Cphase n ≤ Bpast (n + 1))
        (Hcontrol : ℕ) (pControl : ℕ → ℝ),
        1 ≤ Hcontrol → (∀ n ≤ s, 0 ≤ pControl n) →
        (∀ n ≤ s, (Fintype.card ι : ℝ) ≤ pControl n) →
        (∀ n ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl n) →
        (∀ n ≤ s, (Hcontrol : ℝ) ≤ Real.exp (pControl n)) →
        (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
          ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) Hcontrol) →
        (∀ n ≤ s, Real.exp ((p₀ + 2) ^ 47) * Real.exp ((s : ℝ) * d * Bpast n) ≤
          Real.exp (pControl n)) →
        (∀ n ≤ s, (d : ℝ) * Real.exp ((p₀ + 2) ^ 45) * Real.exp (Bpast n) ≤
          Real.exp ((pControl n + 2) ^ a)) →
        BundledFullChartControlledCorrelationSourceStages F b ω hF J fast (eQ.baseChange ℝ) Z
          Kinitial Utag poly N pPhase Rrank Cphase (fun n => (pControl n + Ccontrol) ^ Ccontrol) →
        ∃ history : FullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
          Z Kinitial Utag poly N (Bpast s) s,
          FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
            ((pControl s + Ccontrol) ^ Ccontrol) ∧
          ∀ t ∈ history.K,
            eval₂ t (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
              (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ := by
  classical
  choose Cphase hCphase hstep using
    (fun n : ℕ => exists_full_chart_grade_correction_of_major_correlation_witness
      m (n + 1) (Nat.zero_lt_succ n))
  obtain ⟨Ccontrol, hCcontrol, hprefix⟩ := exists_restricted_chart_prefix_control s a
  refine ⟨Cphase, Ccontrol, hCphase, hCcontrol, ?_⟩
  intro X L ι Γ _ _ _ _ _ _ F b ω hF J _ fast v hspan H hHpos hv
    p₀ hp₀ hrows hcols hH hfast
  obtain ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord⟩ :=
    exists_bounded_submodule_quotient_section_with_coordinates (F.associatedGradedBasis b ω hF)
      fast v hspan hHpos hv hp₀ hrows hcols hH
  refine ⟨d, hd, eQ, lift, qS, hsection, hsectionR, hqS, hqSB, hentry, hgrid, hcoord, ?_⟩
  intro Z Kinitial hKinitial Utag poly N pPhase Bpast Rrank
    hBpast hBmono hphaseBudget Hcontrol pControl hHcontrol hpControl hι hσ hHexp hstructure
    hdenbudget hcost hsource
  have hcontrol : ∀ n ≤ s,
      ∀ history : FullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast n) n,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl n + Ccontrol) ^ Ccontrol) := by
    intro n hn history
    have hdenbudget' : (qS : ℝ) *
        Real.exp ((s : ℝ) * (Fintype.card (Fin d) : ℝ) * Bpast n) ≤ Real.exp (pControl n) := by
      simpa only [Fintype.card_fin] using
        (mul_le_mul_of_nonneg_right hqSB (Real.exp_nonneg _)).trans (hdenbudget n hn)
    have hcost' : (Fintype.card (Fin d) : ℝ) * Real.exp ((p₀ + 2) ^ 45) *
        Real.exp (Bpast n) ≤ Real.exp ((pControl n + 2) ^ a) := by
      simpa only [Fintype.card_fin] using hcost n hn
    obtain ⟨q, hq, hqB, _hdiv, Echart, hE, hEbound, hRgrid⟩ :=
      hprefix F b ω hF (fullTaggedVariableWeight J) (fullTaggedVariableWeight_pos J)
        Hcontrol (pControl n) hHcontrol (hpControl n hn) (hι n hn) (hσ n hn) (hHexp n hn) hstructure
        fast lift (eQ.baseChange ℝ) (Real.exp ((p₀ + 2) ^ 45)) (Bpast n) qS (hBpast n hn) hqS
        hdenbudget' hcost' hentry hgrid
        (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
        (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ)))
        history.slow history.rat history.q n hn history.q_pos history.q_bound
        history.slow_bound history.rat_grid
    unfold FullChartControlledFactors FullChartFiniteHistory.outer
    with_reducible exact ⟨q, hq, hqB, Echart, hE, hEbound, hRgrid⟩
  have hexists : ∀ n ≤ s,
      Nonempty (FullChartFiniteHistory F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast n) n) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨FullChartFiniteHistory.initial F b ω hF J fast (eQ.baseChange ℝ) lift
        Z Kinitial Utag poly N (Bpast 0) hKinitial⟩
    | succ n ih =>
      intro hn
      obtain ⟨history⟩ := ih (by omega)
      have hlower : ∀ t ∈ history.K, ∀ j < n + 1,
          F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
            (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
        intro t ht j hj
        with_reducible exact history.invariant_outer t ht j (by omega)
      have hcorr := hsource n (by omega) history.outer.1 history.outer.2 history.K
        history.subset history.dilation history.retained hlower (hcontrol n (by omega) history)
      have hdata := hstep n F b ω hF J fast (eQ.baseChange ℝ) lift hfast hsection
        Z history.outer.1 history.outer.2 history.K history.dilation hlower
        N poly Utag (pPhase n) Rrank hcorr
      let larger := history.mono_bound (hBmono (Nat.le_succ n))
      have hdata' : FullChartGradeCorrectionData F b ω hF J (n + 1) fast
          (eQ.baseChange ℝ) lift Z larger.outer.1 larger.outer.2 larger.K Utag poly N
          ((pPhase n + Cphase n) ^ Cphase n) := by
        simpa only [larger, FullChartFiniteHistory.outer_mono_bound,
          FullChartFiniteHistory.mono_bound_K] using hdata
      obtain ⟨next, _⟩ := larger.exists_step ((pPhase n + Cphase n) ^ Cphase n)
        (hphaseBudget n (by omega)) hdata'
      exact ⟨next⟩
  obtain ⟨history⟩ := hexists s le_rfl
  refine ⟨history, hcontrol s le_rfl history, ?_⟩
  intro t ht
  apply (F.restricted_symbol_grade_terminal b ω hF (fullTaggedVariableWeight J)
    fast hfast _ t).mpr
  with_reducible exact history.invariant_outer t ht

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_certified_full_chart_decomposition_of_major_correlation
    (m k : ℕ) (hk : 0 < k) :
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
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      FullChartMajorCorrelation F b ω hF J k fast basis Z left right D N poly U p Rrank C →
      CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hdetect⟩ := exists_full_restricted_grade_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower D htk N poly U p Rrank hcorrelation
  obtain ⟨periodCap, coverCap, Lip, W, R, Ψ, c, β, hpoly, hcoeff, hβ,
    hp, hR, hRcap, hdim, hmod, hcover, hLip, hΨ, hN, hRrank, hrank, hcorr⟩ := hcorrelation
  have hdetected := hdetect F b ω hF J fast basis (left⁻¹ * Z * right⁻¹).coord
    W D htk R N poly hpoly U hcoeff Ψ c β hβ
    p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  exact certifiedFullChartDetectedDecomposition_of_vector_detection F b ω hF J k fast
    basis lift Z left right K₀ U poly N ((p + C) ^ C) c hfast hsection hK₀ hlower hdetected.1

attribute [local instance] FullChartMajorCorrelationWitness.lie
  FullChartMajorCorrelationWitness.algebra FullChartMajorCorrelationWitness.topology
  FullChartMajorCorrelationWitness.topologicalAdd FullChartMajorCorrelationWitness.continuousSMul
  FullChartMajorCorrelationWitness.hausdorff

theorem exists_certified_full_chart_decomposition_of_major_correlation_witness
    (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
        Z left right N poly U p Rrank C) →
      CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_certified_full_chart_decomposition_of_major_correlation m k hk
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower N poly U p Rrank hwitness
  obtain ⟨witness⟩ := hwitness
  exact hstep F b ω hF J fast basis lift hfast hsection Z left right K₀ hK₀ hlower
    witness.model witness.lower N poly U p Rrank witness.correlation

end Erdos3.NilpotentLieFiltration

end

end OAI

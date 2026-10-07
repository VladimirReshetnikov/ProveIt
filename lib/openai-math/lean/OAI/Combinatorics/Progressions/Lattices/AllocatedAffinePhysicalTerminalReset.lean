import OAI.Combinatorics.Progressions.Estimates.GlobalMarkedPhysicalValueBounds
import OAI.Combinatorics.Progressions.Lattices.CertifiedAffineNormalizedBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realChartSubstitute PolynomialRationalGrid PolynomialSlowBound
  CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedCertifiedAffineControlledGlobalTerminal (t a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
      {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {τ ξ : ℝ} {stride : X → ℕ}
      {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
      {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
      {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
      {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark φ marked observable weight
        cost massThreshold scoreThreshold)
      {ι η : Type} [Fintype ι] [Fintype η]
      (bF : Basis ι ℚ M) (ω : ι → ℕ)
      (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ Fmark.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ W.toSubmodule)))
      (lift : (Fmark.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
      (Z : Fmark.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Bphase budget pAffine : ℝ)
      (history : CertifiedFullChartFiniteHistory Fmark bF ω hF J W.toSubmodule basis lift
        Z Set.univ U poly N Bphase t)
      (affine : P.CertifiedAffineRefinement history.K pAffine),
      BasisGradedSubmodule (Fmark.associatedGradedBasis bF ω hF) ω W.toSubmodule →
      FullChartControlledFactors Fmark bF ω hF J poly N history.outer.1 history.outer.2 budget →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      Fmark.realPolynomialSymbolHom bF ω hF (fullTaggedVariableWeight (X := X) J)
        (Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked) = Z →
      τ ≤ 1 → ξ ≤ 1 → (∀ j, σ j ≤ 1) →
    ∀ (Cgeo : Fin m → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1) →
    ∀ (H : ℕ) (pFull : ℝ), 1 ≤ H → 0 ≤ pFull →
      (Fintype.card ι : ℝ) ≤ pFull →
      (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull →
      (H : ℝ) ≤ Real.exp pFull →
      Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ t ≤
        Real.exp pFull →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pFull →
      (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t * Real.exp budget *
        (actualCandidateSlowProjectionMassBudget m
          (Fintype.card (LayerSamplerVariables G I n B)) pFull
          (((pAffine + ((pAffine+2)^2+2)^63)+2)^8)) ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
      let wt := fullTaggedVariableWeight (X := X) J
      let β := affine.globalChart
      let δ := affine.slowChart
      let pull := Fmark.realSymbolHomogeneousPullbackHom bF ω hF wt wt
        (fun i => weightedHomogeneousComponent wt (wt i) (β i))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      0 < affine.commonDenominator ∧
      (affine.commonDenominator : ℝ) ≤ Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine) ∧
      ∃ q nFinal : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
        0 < nFinal ∧ (nFinal : ℝ) ≤ Real.exp ((pFull + Cr) ^ Cr) ∧
        q * affine.commonDenominator ^ t ∣ nFinal ∧
        ∃ factors : GlobalMarkedNativeFactors Fmark bF ω hF wt W
          (Fmark.weightedAdaptedRealChartHom wt wt β affine.globalChart_support
            (Fmark.realification.polynomialOrbitCoordinates wt marked))
          (pull history.outer.1) (pull history.outer.2),
          Fmark.PolynomialRationalGrid bF wt nFinal factors.right ∧
          (∀ z : affine.refinement.problem.productive,
            let C := affine.refinement.problem.chart z
            Fmark.PolynomialSlowBound bF (fun _ : C.Variables => 1)
              (fun i => (sampler.sides i.val : ℝ)) (Real.exp ((pFull + Ce) ^ Ce))
              (Fmark.weightedAdaptedRealChartHom wt (fun _ : C.Variables => 1)
                (integerSampledRealChart C.integerChart) C.integerChart_support factors.left)) ∧
          ∀ {Υ : Type} [Fintype Υ] (v : Υ → ℕ), (∀ i, 0 < v i) →
            (Fintype.card Υ : ℝ) ≤ pFull →
            ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial Υ ℝ)
              (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
              (T : Υ → ℝ), (∀ i, 0 < T i) →
            ∀ mass : ℝ, 1 ≤ mass →
              (∀ i, realPolynomialMass
                (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ mass) →
              (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t *
                Real.exp budget * mass ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
              Fmark.PolynomialSlowBound bF v T (Real.exp ((pFull + Ce) ^ Ce))
                (Fmark.weightedAdaptedRealChartHom wt v γ hγ factors.left) := by
  classical
  obtain ⟨Ce, Cr, hCe, hCr, hterminal⟩ := exists_allocatedCertifiedAffineGlobalTerminal t a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ ξ stride cells center _ sampler L M _ _ _ _ s d D Fmark φ marked observable weight
    cost massThreshold scoreThreshold P ι η _ _ bF ω hF W basis lift Z Bphase budget pAffine
    history affine hW hcontrol hpoly hZ hτ1 hξ1 hσ1 Cgeo hCgeo hchart hsmall
    H pFull hH hpFull hι hvars hHp hden hbracket hsample hmass
  obtain ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors, hgrid, hslow⟩ :=
    hterminal P bF ω hF W basis lift Z Bphase budget pAffine history affine hW hcontrol
      hpoly hZ H pFull hH hpFull hι hvars hHp hden hbracket
  refine ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
    hgrid, ?_, hslow⟩
  intro z
  let C := affine.refinement.problem.chart z
  have hretained (x) (hx : ∀ j, (fun i => x (Sum.inr ⟨j,i⟩)) ∈ U j) : x ∈ history.K :=
    history.retained x (Set.mem_univ _) hx
  have hdim (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ pFull := by
    exact (Nat.cast_le.mpr (Fintype.card_le_of_injective
      (fun i : J j => (Sum.inr ⟨j,i⟩ : X ⊕ (Σ j,J j)))
      (by intro i k h; simpa using h))).trans hvars
  have hlocal : (Fintype.card C.Variables : ℝ) ≤ pFull :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le C.keep)).trans hsample
  have hside (i : C.Variables) : (0 : ℝ) < sampler.sides i.val :=
    Nat.cast_pos.mpr (sampler.sides_pos i.val)
  apply hslow (fun _ : C.Variables => 1) (fun _ => Nat.zero_lt_one) hlocal
    (integerSampledRealChart C.integerChart) C.integerChart_support
    (fun i => (sampler.sides i.val : ℝ)) hside
    (actualCandidateSlowProjectionMassBudget m
      (Fintype.card (LayerSamplerVariables G I n B)) pFull
      (((pAffine + ((pAffine+2)^2+2)^63)+2)^8))
    (actualCandidateSlowProjectionMassBudget_one_le _ _ hpFull) ?_ hmass
  intro i
  exact affine.slowChart_mass_sides hretained hpFull hdim hτ1 hξ1 hpoly hσ1
    Cgeo hCgeo hchart hsmall z i

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators Classical
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realChartSubstitute PolynomialRationalGrid PolynomialSlowBound
  CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedCertifiedAffineGlobalPhysicalTerminal (t a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
      {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {τ ξ : ℝ} {stride : X → ℕ}
      {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
      {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
      {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
      {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark φ marked observable weight
        cost massThreshold scoreThreshold)
      {ι η : Type} [Fintype ι] [Fintype η]
      (bF : Basis ι ℚ M) (ω : ι → ℕ)
      (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ Fmark.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ W.toSubmodule)))
      (lift : (Fmark.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
      (Z : Fmark.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Bphase budget pAffine : ℝ)
      (history : CertifiedFullChartFiniteHistory Fmark bF ω hF J W.toSubmodule basis lift
        Z Set.univ U poly N Bphase t)
      (affine : P.CertifiedAffineRefinement history.K pAffine),
      BasisGradedSubmodule (Fmark.associatedGradedBasis bF ω hF) ω W.toSubmodule →
      FullChartControlledFactors Fmark bF ω hF J poly N history.outer.1 history.outer.2 budget →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      Fmark.realPolynomialSymbolHom bF ω hF (fullTaggedVariableWeight (X := X) J)
        (Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked) = Z →
      τ ≤ 1 → ξ ≤ 1 → (∀ j, σ j ≤ 1) →
    ∀ (Cgeo : Fin m → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1) →
    ∀ (H : ℕ) (pFull : ℝ), 1 ≤ H → 0 ≤ pFull →
      (Fintype.card ι : ℝ) ≤ pFull →
      (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull →
      (H : ℝ) ≤ Real.exp pFull →
      Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ t ≤
        Real.exp pFull →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pFull →
      (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t * Real.exp budget *
        (actualCandidateSlowProjectionMassBudget m
          (Fintype.card (LayerSamplerVariables G I n B)) pFull
          (((pAffine + ((pAffine+2)^2+2)^63)+2)^8)) ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
      let wt := fullTaggedVariableWeight (X := X) J
      let β := affine.globalChart
      let δ := affine.slowChart
      let pull := Fmark.realSymbolHomogeneousPullbackHom bF ω hF wt wt
        (fun i => weightedHomogeneousComponent wt (wt i) (β i))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      0 < affine.commonDenominator ∧
      (affine.commonDenominator : ℝ) ≤ Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine) ∧
      ∃ q nFinal : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
        0 < nFinal ∧ (nFinal : ℝ) ≤ Real.exp ((pFull + Cr) ^ Cr) ∧
        q * affine.commonDenominator ^ t ∣ nFinal ∧
        ∃ factors : GlobalMarkedNativeFactors Fmark bF ω hF wt W
          (Fmark.weightedAdaptedRealChartHom wt wt β affine.globalChart_support
            (Fmark.realification.polynomialOrbitCoordinates wt marked))
          (pull history.outer.1) (pull history.outer.2),
          Fmark.PolynomialRationalGrid bF wt nFinal factors.right ∧
          (∀ z : affine.refinement.problem.productive,
            let C := affine.refinement.problem.chart z
            Fmark.PolynomialSlowBound bF (fun _ : C.Variables => 1)
              (fun i => (sampler.sides i.val : ℝ)) (Real.exp ((pFull + Ce) ^ Ce))
              (Fmark.weightedAdaptedRealChartHom wt (fun _ : C.Variables => 1)
                (integerSampledRealChart C.integerChart) C.integerChart_support factors.left)) ∧
          (∀ x ∈ integerBox N, ∀ i,
            |(bF.baseChange ℝ).repr
              (Fmark.realification.polynomialOrbitEval wt (P.physicalIntegerPoint x)
                ((Fmark.realification.polynomialOrbitCoordinates wt).symm factors.left)).coord i| ≤
              Real.exp ((pFull + Ce) ^ Ce)) ∧
          (∀ x : X → ℤ, (bF.baseChange ℝ).equivFun
            (Fmark.realification.polynomialOrbitEval wt (P.physicalIntegerPoint x)
              ((Fmark.realification.polynomialOrbitCoordinates wt).symm factors.right)).coord ∈
              realDenominatorGrid nFinal) ∧
          ∀ {Υ : Type} [Fintype Υ] (v : Υ → ℕ), (∀ i, 0 < v i) →
            (Fintype.card Υ : ℝ) ≤ pFull →
            ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial Υ ℝ)
              (hγ : ∀ i, γ i ∈ weightedSupportLE v (wt i))
              (T : Υ → ℝ), (∀ i, 0 < T i) →
            ∀ mass : ℝ, 1 ≤ mass →
              (∀ i, realPolynomialMass
                (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ mass) →
              (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ t *
                Real.exp budget * mass ^ t ≤ Real.exp ((pFull + 2) ^ a)) →
              Fmark.PolynomialSlowBound bF v T (Real.exp ((pFull + Ce) ^ Ce))
                (Fmark.weightedAdaptedRealChartHom wt v γ hγ factors.left) := by
  classical
  obtain ⟨Ce, Cr, hCe, hCr, hterminal⟩ :=
    exists_allocatedCertifiedAffineControlledGlobalTerminal t a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ ξ stride cells center _ sampler L M _ _ _ _ s d D Fmark φ marked observable weight
    cost massThreshold scoreThreshold P ι η _ _ bF ω hF W basis lift Z Bphase budget pAffine
    history affine hW hcontrol hpoly hZ hτ1 hξ1 hσ1 Cgeo hCgeo hchart hsmall
    H pFull hH hpFull hι hvars hHp hden hbracket hsample hmass
  obtain ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
      hgrid, hlocal, hcharts⟩ :=
    hterminal P bF ω hF W basis lift Z Bphase budget pAffine history affine hW hcontrol
      hpoly hZ hτ1 hξ1 hσ1 Cgeo hCgeo hchart hsmall H pFull hH hpFull hι hvars hHp
      hden hbracket hsample hmass
  refine ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
    hgrid, hlocal, ?_, ?_, hcharts⟩
  · intro x hx i
    have hretained (y) (hy : ∀ j, (fun i => y (Sum.inr ⟨j,i⟩)) ∈ U j) : y ∈ history.K :=
      history.retained y (Set.mem_univ _) hy
    have hdim (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ pFull := by
      exact (Nat.cast_le.mpr (Fintype.card_le_of_injective
        (fun i : J j => (Sum.inr ⟨j,i⟩ : X ⊕ (Σ j,J j)))
        (by intro i k h; simpa using h))).trans hvars
    rw [← Fmark.realification.polynomialOrbitRealEval_integer,
      Fmark.nativeFrozenMarkedOrbitCoordinates_symm_realEval]
    apply Fmark.value_bound_of_terminal_chart_control bF (fullTaggedVariableWeight J)
      affine.slowChart pFull budget a Ce hpFull factors.left hcharts _
      (actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) pFull
        (((pAffine + ((pAffine+2)^2+2)^63)+2)^8))
      (actualCandidateSlowProjectionMassBudget_one_le _ _ hpFull) ?_ hmass i
    intro z
    exact (affine.slowChart_physical_abs_le hretained hdim x hx z).trans
      (actualCandidateSlowProjectionMassBudget_max_le _ _ hpFull)
  · intro x
    rw [← Fmark.realification.polynomialOrbitRealEval_integer,
      Fmark.nativeFrozenMarkedOrbitCoordinates_symm_realEval]
    exact Fmark.polynomialRationalGrid_value bF (fullTaggedVariableWeight J)
      nFinal factors.right hgrid (P.physicalIntegerPoint x)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical TensorProduct BigOperators
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

noncomputable def allocatedEarlyAffineLeftExponent (s a : ℕ) : ℕ :=
  Classical.choose (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a)

noncomputable def allocatedEarlyAffineRightExponent (s a : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a))

theorem allocatedEarlyAffine_exponent_bounds (s a : ℕ) :
    2 ≤ allocatedEarlyAffineLeftExponent s a ∧ 2 ≤ allocatedEarlyAffineRightExponent s a := by
  have h := Classical.choose_spec
    (Classical.choose_spec (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a))
  exact ⟨h.1, h.2.1⟩

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark

structure AffinePhysicalTerminalData
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ (fast).toSubmodule)))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (Bphase budget pAffine pFull : ℝ) (a : ℕ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      basis lift Z Set.univ U poly N Bphase s)
    (separation : ℝ) where
  selected : P.CertifiedThresholdAffineRefinement history.K pAffine separation
  denominator_pos : 0 < selected.affine.commonDenominator
  denominator_bound : (selected.affine.commonDenominator : ℝ) ≤
    Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)
  q : ℕ
  nFinal : ℕ
  q_pos : 0 < q
  q_bound : (q : ℝ) ≤ Real.exp budget
  nFinal_pos : 0 < nFinal
  nFinal_bound : (nFinal : ℝ) ≤
    Real.exp ((pFull + allocatedEarlyAffineRightExponent s a) ^ allocatedEarlyAffineRightExponent s a)
  denominator_dvd : q * selected.affine.commonDenominator ^ s ∣ nFinal
  factors :
    let wt := fullTaggedVariableWeight (X := X) J
    let β := selected.affine.globalChart
    let pull := Fmark.realSymbolHomogeneousPullbackHom bF ν hF wt wt
      (fun i => weightedHomogeneousComponent wt (wt i) (β i))
      (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
    GlobalMarkedNativeFactors Fmark bF ν hF wt fast
      (Fmark.weightedAdaptedRealChartHom wt wt β selected.affine.globalChart_support
        (Fmark.realification.polynomialOrbitCoordinates wt marked))
      (pull history.outer.1) (pull history.outer.2)
  right_grid : Fmark.PolynomialRationalGrid bF (fullTaggedVariableWeight J) nFinal factors.right
  local_left : ∀ z : selected.affine.refinement.problem.productive,
    let C := selected.affine.refinement.problem.chart z
    Fmark.PolynomialSlowBound bF (fun _ : C.Variables => 1)
      (fun i => (A.sides i.val : ℝ))
      (Real.exp ((pFull + allocatedEarlyAffineLeftExponent s a) ^ allocatedEarlyAffineLeftExponent s a))
      (Fmark.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support factors.left)
  physical_left : ∀ x ∈ integerBox N, ∀ i,
    |(bF.baseChange ℝ).repr
      (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (P.physicalIntegerPoint x)
        ((Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.left)).coord i| ≤
      Real.exp ((pFull + allocatedEarlyAffineLeftExponent s a) ^ allocatedEarlyAffineLeftExponent s a)
  physical_right : ∀ x : X → ℤ, (bF.baseChange ℝ).equivFun
    (Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (P.physicalIntegerPoint x)
      ((Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.right)).coord ∈
      realDenominatorGrid nFinal

theorem exists_affinePhysicalTerminalData
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.AssociatedGraded ⧸ (fast).toSubmodule)))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (Bphase budget pAffine : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      basis lift Z Set.univ U poly N Bphase s)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N
      history.outer.1 history.outer.2 budget)
    {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K pAffine blocks)
    (hpAffine : 0 ≤ pAffine) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ pAffine)
    (hblocks : (blocks : ℝ) ≤ pAffine)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1)
    (hmass : 0 < massThreshold) (H : ℕ) (a : ℕ) (pFull : ℝ)
    (hH : 1 ≤ H) (hpFull : 0 ≤ pFull)
    (hκ : (Fintype.card κ : ℝ) ≤ pFull)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull)
    (hHExp : (H : ℝ) ≤ Real.exp pFull)
    (hden : Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ s ≤
      Real.exp pFull)
    (hbracket : ∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pFull)
    (hmassFull : (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
      (actualCandidateSlowProjectionMassBudget m (Fintype.card (LayerSamplerVariables G I n B)) pFull
        (((pAffine + ((pAffine+2)^2+2)^63)+2)^8)) ^ s ≤ Real.exp ((pFull + 2) ^ a)))
    (separation : ℝ) (hseparation : certifiedAffineLongSideBound pAffine ≤ separation) :
    Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W basis lift
      Bphase budget pAffine pFull a history separation) := by
  classical
  have hretained (point) (hpoint : ∀ j, (fun i => point (Sum.inr ⟨j,i⟩)) ∈ U j) :
      point ∈ history.K := history.retained point (Set.mem_univ _) hpoint
  have hcap (j : Fin m) :
      Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Real.exp pAffine :=
    (hsmall j).trans (Real.one_le_exp_iff.mpr hpAffine)
  obtain ⟨selected⟩ := P.exists_certifiedThresholdAffineRefinement hσone history.K
    (p := pAffine) (blocks := blocks) hcertificate hretained hpAffine hdim hblocks
    Cgeo hCgeo hchart hpoly hcap separation hseparation hmass
  obtain ⟨hDpos, hDbound, q, nFinal, hq, hqB, hn, hnB, hdiv, factors,
      hgrid, hlocal, hphysicalLeft, hphysicalRight, _⟩ :=
    ((Classical.choose_spec
      (Classical.choose_spec (exists_allocatedCertifiedAffineGlobalPhysicalTerminal s a))).2.2)
      selected.freezing.problem bF ν hF fast basis lift Z Bphase budget pAffine
      history selected.affine hfast hcontrol hpoly rfl hτ hξ hσone Cgeo hCgeo hchart hsmall
      H pFull hH hpFull hκ htags hHExp hden hbracket hsampler hmassFull
  exact ⟨{
    selected := selected
    denominator_pos := hDpos
    denominator_bound := hDbound
    q := q
    nFinal := nFinal
    q_pos := hq
    q_bound := hqB
    nFinal_pos := hn
    nFinal_bound := hnB
    denominator_dvd := hdiv
    factors := factors
    right_grid := hgrid
    local_left := hlocal
    physical_left := hphysicalLeft
    physical_right := hphysicalRight
  }⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {η : Type} [Fintype η]
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
    (lift : (Fmark.filtration.AssociatedGraded ⧸
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
        Fmark.filtration.AssociatedGraded)
    (Bphase budget pAffine pFull separation : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark.filtration c ν hF J
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
      basis lift
      (Fmark.filtration.realPolynomialSymbolHom c ν hF (fullTaggedVariableWeight J)
        (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
      Set.univ U poly N Bphase (s + 1))
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (hcost : Real.exp cost ≤ separation)

local notation "kept" => (fun i : LayerSamplerVariables G I n B =>
  candidateSideCutoff separation ≤ A.sides i)

theorem exists_affinePhysicalTerminal_nativeReset_of_zero_restriction
    {κK μ χ : Type} [Fintype κK] [Fintype μ] [Fintype χ]
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (bk : Basis κK ℚ (LinearMap.ker φ.toLinearMap))
    (v : μ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (vg : χ → Fmark.filtration.PolynomialSymbol (fun _ : {i // kept i} => 1))
    (hvgspan : span ℚ (Set.range vg) =
      (Fmark.filtration.symbolPointwiseSubalgebra c ν hF (fun _ : {i // kept i} => 1)
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).toSubmodule)
    [Fintype (SymbolBasisIndex (fun _ : {i // kept i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : {i // kept i} => 1) ν)]
    (H l : ℕ) (pMap pNative : ℝ)
    (hH : 1 ≤ H) (hl : 0 < l) (hpMap : 0 ≤ pMap) (hpNative : 0 ≤ pNative)
    (hsrc : (Fintype.card (SymbolBasisIndex (fun _ : {i // kept i} => 1) ω) : ℝ) ≤ pMap)
    (htgt : (Fintype.card (SymbolBasisIndex (fun _ : {i // kept i} => 1) ν) : ℝ) ≤ pMap)
    (hHmap : (H : ℝ) ≤ Real.exp pMap)
    (hlmap : ((l * data.nFinal : ℕ) : ℝ) ≤ Real.exp pMap)
    (hmabsorb : Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative)
    (hd : (d : ℝ) ≤ pNative) (hc : (nMarkedBasis : ℝ) ≤ pNative)
    (hk : (Fintype.card κK : ℝ) ≤ pNative)
    (hμ : (Fintype.card μ : ℝ) ≤ pNative)
    (hχ : (Fintype.card χ : ℝ) ≤ pNative)
    (hvars : (Fintype.card {i // kept i} : ℝ) ≤ pNative)
    (hHp : (H : ℝ) ≤ Real.exp pNative)
    (hbracketD : ∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H)
    (hbracketF : ∀ i j k, RationalHeightLE (c.repr ⁅c i, c j⁆ k) H)
    (hkernel : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H)
    (hentries : ∀ k i, RationalHeightLE (c.repr (φ (D.basis i)) k) H)
    (hv : ∀ j i, RationalHeightLE
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.filtration.polynomialSymbolBasis c ν hF (fun _ : {i // kept i} => 1)).repr (vg i) z) H)
    (hslow : Real.exp ((pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
      allocatedEarlyAffineLeftExponent (s + 1) 4) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hsideBound : Real.exp ((pNative + allocatedAffineResetCompareExponent s) ^
      allocatedAffineResetCompareExponent s) ≤ separation)
    (q : ℝ)
    (hq : Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hqmap : Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)))
    (hcutoff : Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, kept i → initialLong i)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))) :
    ∃ denominator : ℕ, 0 < denominator ∧
      (denominator : ℝ) ≤ Real.exp (allocatedAffineResetLogBudget s pNative) ∧
      data.nFinal ∣ denominator ∧
      Nonempty (AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
        data.selected.problem kept (data.selected.common_keep hcost) W data.factors
        (Real.exp (allocatedAffineResetLogBudget s pNative)) denominator) := by
  classical
  have hreset := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1)))
  obtain ⟨mMap, denominator, hmMap, hmMapBound, hdiv, hden, hdenBound, hmMapDen, hrun⟩ :=
    hreset.2.2.2 (sampler := A) (E := E) D Fmark φ hφ ω hD c ν hF hsurj kept
      bk W v hW hvspan vg hvgspan H l data.nFinal pMap pNative hH hl data.nFinal_pos
      hpMap hpNative hsrc htgt hHmap hlmap hmabsorb hd (by simpa using hc) hk hμ hχ
      (by convert hvars using 1; simp only [Fintype.card_eq_nat_card]) hHp
      hbracketD hbracketF hkernel hentries hv hvg
  refine ⟨denominator, hden, hdenBound, (dvd_mul_left data.nFinal l).trans (hdiv.trans hmMapDen), ?_⟩
  have hside (i : {i // kept i}) :
      Real.exp ((pNative + allocatedAffineResetCompareExponent s) ^
        allocatedAffineResetCompareExponent s) ≤ (A.sides i.val : ℝ) :=
    hsideBound.trans ((lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr i.property))
  have hlong (i : LayerSamplerVariables G I n B) (hi : kept i) :
      separation ≤ layerSamplerBox B U b S i := by
    rw [allocatedParameterBox_side_eq B U b S i]
    exact (lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr hi)
  apply hrun marked observable weight data.selected.freezing.problem data.selected.affine
    (data.selected.common_keep hcost) _ _ data.factors data.right_grid
  · intro z
    exact Fmark.filtration.polynomialSlowBound_mono c
      (fun _ : (data.selected.problem.chart z).Variables => 1)
      (fun i => (A.sides i.val : ℝ)) (fun i => Nat.cast_pos.mpr (A.sides_pos i.val))
      hslow _ (data.local_left z)
  · exact hside
  · exact hq
  · exact hqmap
  · exact data.selected.original_dense
  · exact hcutoff
  · exact hlong
  · exact data.selected.withKeep_nativeFactors_of_zero_restriction
      kept (data.selected.common_keep hcost) initialLong
      (fun z i hi => hsub i hi.2) D.basis ω hD q l W hzero

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

def affineResetNativeBudget (C : ℕ) (pFull pMap q : ℝ) : ℝ :=
  pFull + pMap + max q 0 + (pFull + C) ^ C + (pMap + 2) ^ 4

theorem affineResetNativeBudget_bounds (C : ℕ) {pFull pMap q : ℝ}
    (hFull : 0 ≤ pFull) (hMap : 0 ≤ pMap) :
    let pNative := affineResetNativeBudget C pFull pMap q
    0 ≤ pNative ∧ pFull ≤ pNative ∧ pMap ≤ pNative ∧ q ≤ pNative ∧
      (pFull + C) ^ C ≤ pNative ∧ (pMap + 2) ^ 4 ≤ pNative ∧
      (pMap + 2) ^ 3 + q ≤ pNative := by
  have hq0 : 0 ≤ max q 0 := le_max_right _ _
  have hq : q ≤ max q 0 := le_max_left _ _
  have hslow : 0 ≤ (pFull + C) ^ C := pow_nonneg (by positivity) _
  have hmap4 : 0 ≤ (pMap + 2) ^ 4 := pow_nonneg (by linarith) _
  have h34 : (pMap + 2) ^ 3 ≤ (pMap + 2) ^ 4 :=
    pow_le_pow_right₀ (by linarith) (by omega)
  dsimp only [affineResetNativeBudget]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem affineResetNativeBudget_exp_bounds (C : ℕ) {pFull pMap q : ℝ}
    (hFull : 0 ≤ pFull) (hMap : 0 ≤ pMap) :
    let pNative := affineResetNativeBudget C pFull pMap q
    0 ≤ pNative ∧ pFull ≤ pNative ∧ pMap ≤ pNative ∧
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative ∧
      Real.exp ((pFull + C) ^ C) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) := by
  obtain ⟨hp, hfull, hmap, hq, hslow, hmap4, hmapq⟩ :=
    affineResetNativeBudget_bounds C hFull hMap (q := q)
  refine ⟨hp, hfull, hmap, Real.exp_le_exp.mpr hmap4, ?_, ?_, ?_⟩ <;>
    apply Real.exp_le_exp.mpr <;> simp only [pow_one] <;> linarith

noncomputable def allocatedAffineResetNativeBudget (s : ℕ) (pFull pMap q : ℝ) : ℝ :=
  affineResetNativeBudget (allocatedEarlyAffineLeftExponent (s + 1) 4) pFull pMap q

theorem allocatedAffineResetNativeBudget_exp_bounds (s : ℕ) {pFull pMap q : ℝ}
    (hFull : 0 ≤ pFull) (hMap : 0 ≤ pMap) :
    let pNative := allocatedAffineResetNativeBudget s pFull pMap q
    let Ce := allocatedEarlyAffineLeftExponent (s + 1) 4
    0 ≤ pNative ∧ pFull ≤ pNative ∧ pMap ≤ pNative ∧
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative ∧
      Real.exp ((pFull + Ce) ^ Ce) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) ∧
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) :=
  affineResetNativeBudget_exp_bounds (allocatedEarlyAffineLeftExponent (s + 1) 4) hFull hMap

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedAffinePhysicalTerminalReset (s : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
      {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {τ narrow : ℝ} {stride : X → ℕ}
      {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ narrow stride cells center}
      {L M κ ξ μ χ : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [Fintype κ] [Fintype ξ] [Fintype μ] [Fintype χ]
      {d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (ω : Fin d → ℕ)
      (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
      (bF : Basis κ ℚ M) (ν : κ → ℕ)
      (hF : ∀ j, Fmark.filtration.layer j = span ℚ (bF '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (separation : ℝ),
      let keep : LayerSamplerVariables G I n B → Prop :=
        fun i => candidateSideCutoff separation ≤ sampler.sides i;
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : μ → D.filtration.AssociatedGraded),
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → Fmark.filtration.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (Fmark.filtration.symbolPointwiseSubalgebra bF ν hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ν)]
      (H l nFinal : ℕ) (pMap pNative : ℝ),
      1 ≤ H → 0 < l → 0 < nFinal → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → ((l * nFinal : ℕ) : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (d : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H) →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      (∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (bF.repr (φ (D.basis i)) k) H) →
      (∀ j i, RationalHeightLE ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((Fmark.filtration.polynomialSymbolBasis bF ν hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
    ∃ mMap mReset : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l * nFinal ∣ mMap ∧ 0 < mReset ∧
      (mReset : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput (s + 1) 1 Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ mReset ∧
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark.filtration φ marked
        observable weight cost massThreshold scoreThreshold)
      {η : Type} [Fintype η]
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (Fmark.filtration.AssociatedGraded ⧸
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule)))
      (lift : (Fmark.filtration.AssociatedGraded ⧸
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule) →ₗ[ℚ]
          Fmark.filtration.AssociatedGraded)
      (Bphase budget pAffine pFull : ℝ)
      (history : CertifiedFullChartFiniteHistory Fmark.filtration bF ν hF J
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)).toSubmodule
        basis lift
        (Fmark.filtration.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J)
          (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked))
        Set.univ U poly N Bphase (s + 1))
      (data : P.AffinePhysicalTerminalData bF ν hF hφ W basis lift
        Bphase budget pAffine pFull 4 history separation)
      (hcost : Real.exp cost ≤ separation),
      data.nFinal = nFinal →
      Real.exp ((pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
        allocatedEarlyAffineLeftExponent (s + 1) 4) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) →
      Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ separation →
    ∀ (q : ℝ),
      Real.exp q ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ (1 : ℕ)) →
      Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation →
      (∀ z : P.productive,
        D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
          (fun i : (P.chart z).Variables => (sampler.sides i.val : ℝ)) q l W
          (D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)) →
      Nonempty (AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
        data.selected.problem keep (data.selected.common_keep hcost) W data.factors
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput (s + 1) 1 Cf pNative)
          + Cnative) ^ Cnative)) mReset) := by
  classical
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_allocatedThresholdAffineFamilyReset s 1
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ narrow stride cells center _ sampler L M κ ξ μ χ _ _ _ _ _ _ _ _ d f
    D Fmark φ hφ ω hD bF ν hF hsurj separation keep bk W v hW hvspan vg hvgspan _ _
    H l nFinal pMap pNative hH hl hnFinal hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
    hd hκ hξ hμ hχ hvars hHp hbracketD hbracketF hkernel hentries hv hvg
  obtain ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, hrun⟩ :=
    hreset (sampler := sampler) (E := E) D Fmark φ hφ ω hD bF ν hF hsurj separation
      bk W v hW hvspan vg hvgspan H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
      hsrc htgt hHmap hlmap hmabsorb hd hκ hξ hμ hχ hvars hHp
      hbracketD hbracketF hkernel hentries hv hvg
  refine ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, ?_⟩
  intro marked observable weight cost massThreshold scoreThreshold P η _ basis lift
    Bphase budget pAffine pFull history data hcost hn hslow hside q hq hqmap hcutoff hOriginal
  apply hrun marked observable weight P data.selected hcost _ _ data.factors
  · simpa only [← hn] using data.right_grid
  · intro z
    exact Fmark.filtration.polynomialSlowBound_mono bF
      (fun _ : (data.selected.problem.chart z).Variables => 1)
      (fun i => (sampler.sides i.val : ℝ))
      (fun i => Nat.cast_pos.mpr (sampler.sides_pos i.val)) hslow _ (data.local_left z)
  · exact hside
  · exact hq
  · exact hqmap
  · exact hcutoff
  · exact hOriginal

end Erdos3.VectorPolynomial

end

end OAI

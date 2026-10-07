import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
    {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}

namespace AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem fixedCenter_excess
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm τ ξ stride cells center)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hσ1 : ∀ j, σ j ≤ 1) (C V : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P E : ℝ} (hP : 0 ≤ P) (hmSize : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hsP : ∀ x, (stride x : ℝ) ≤ Real.exp P)
    (hWP : allocatedExternalCandidateRootBudget B U basis S ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) (hτhalf : τ ≤ 1 / 2)
    (hτdim : (Fintype.card X : ℝ) * τ ≤ 1 / 2)
    (hξ1 : ξ ≤ 1) (hξP : ξ⁻¹ ≤ Real.exp P)
    (hsize : ∀ x, Real.exp ((max P E + allocatedExternalConditionalExcessExponent m) ^
      allocatedExternalConditionalExcessExponent m) ≤ (N x : ℝ))
    {rank : ℝ}
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun x => (N x : ℝ)) rank (U j) (poly j))
    (hRank : Real.exp ((max P E + allocatedExternalConditionalExcessExponent m) ^
      allocatedExternalConditionalExcessExponent m) ≤ rank)
    (hCells : cells.Nonempty)
    (hbox : (integerBox N).Nonempty)
    (hmargin : ∀ x, 2 * spatialTrimMargin τ N x ≤ N x) :
      letI : Nonempty A.Site := A.site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
        (A.law.siteLaw (A.physicalBox hξ1 hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)) ≤
          6 * positiveProjectionAccuracy E := by
  obtain ⟨_hN, _hbases, _hbox', _hmass, _hmargin', _hnormalizer, hsite⟩ :=
    (allocatedExternalConditionalExcessExponent_spec m).2 B U basis S hb o μ ν
      hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall hP hmSize hK hX hdim
      hRP hσP hcount hI hn hJ hAP hLP hCP hVP poly hp hm stride A.stride_pos hsP
      (allocatedExternalCandidateRootBudget_nonneg B U basis S) hWP
      A.trim_pos hτP hτhalf hτdim A.narrow_pos hξ1 hξP N hsize hrank hRank cells hCells
  let : Nonempty A.Site := A.site_nonempty
  exact hsite (fun t : A.Site => t.val)
    (fun t k => (allocatedParameterSite_bound B U basis S t k).trans hLP)
    (fun t => (allocatedParameterSite_sum_bound B U basis S t).trans_eq
      (allocatedExternalCandidateRootBudget_eq B U basis S).symm) center

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

end OAI

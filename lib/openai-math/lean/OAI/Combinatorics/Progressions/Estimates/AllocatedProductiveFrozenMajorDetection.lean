import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial Submodule BooleanCubeKernel RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag R σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U btag S hb o hR hσ N poly hm τ ξ stride cells center)

namespace VectorPolynomial.AllocatedExternalCandidateSampler

theorem NativeDetection.localMajorSliceDetection
    {degree dim : ℕ} {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {pSlice pTest pNative α cost budget : ℝ}
    (hdetect : A.NativeDetection degree pSlice pTest pNative α)
    (D : RationalFilteredNilmanifold L degree dim)
    {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    (chosen : ∀ z, Tests z → LocalMajorSliceTest D A.sides cost budget)
    (hcost : cost ≤ pSlice) (hbudget : budget ≤ pTest) :
    SampledSliceNativeDetection J N A.integerBox_nonempty poly A.law A.physical
      (fun z a => (chosen z a).slice.subtypeSites)
      (fun z a (x : A.Site) => (chosen z a).weight x.val) degree pNative α := by
  exact hdetect (fun _ _ => D) (fun z a => (chosen z a).test)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a i => ((chosen z a).slice.start i : ℤ))
    (fun z a => (chosen z a).stride) (fun z a => (chosen z a).slice.length)
    (fun z a => (chosen z a).stride_pos)
    (fun z a => (chosen z a).slice.subtypeSites_image_val.trans
      (chosen z a).slice.integerPoints_eq_commonStrideBox)
    (fun z a => ((chosen z a).slice.subtypeSites_dense (chosen z a).dense).mono hcost)
    (fun z a => (chosen z a).complexity.mono hbudget)
    (fun z a => (chosen z a).norm)

end VectorPolynomial.AllocatedExternalCandidateSampler

namespace NilpotentLieFiltration

theorem exists_allocated_full_chart_major_correlation_witness_of_frozen_local_tests
    {k t : ℕ} {L ι η : Type} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (good : η → Finset A.Path)
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (hξ : ξ ≤ 1)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * A.law.mass (good j))
    (hdirect : A.NativeDetection t pSlice pTest pNative α)
    (hslice : max cost (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget t ≤ pTest)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val) ∧
      ∃ T : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
        (fun i : {i // keep i} => A.sides i.val) cost (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ T.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint keep x fixed) (z.1.val, z.2.val)) * T.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_full_chart_major_correlation_witness_of_frozen_productive_local_tests
    F b ω hF J fast basis Z left right htk N A.integerBox_nonempty poly hpoly U
    (fun j e _ => hm j e) c pNative pMajor Rrank C hpNative hη hNativeMajor hproduct
    hdim hN hRrank hrank A.law good A.sides A.sides_pos keep cost Bshort hcost hBshort hshort
    (fun z x => jointIntegerPhysicalSite x (z.1.val, z.2.val))
    (fun _ z _ x hx => by
      simpa only [mem_integerBox, AllocatedExternalCandidateSampler.physical] using
        A.physical_mem_integerBox hξ z ⟨x, hx⟩) α hmass
  · intro chosen
    exact hdirect.localMajorSliceDetection A (OrdinaryPolynomialPhase.nilmanifold t)
      chosen hslice htest
  · have hdec :
        (fun a b : {i : LayerSamplerVariables G I n B // keep i} =>
          Classical.propDecidable (a = b)) =
        (fun a b => @Subtype.instDecidableEq _ keep
          (inferInstance : DecidableEq (LayerSamplerVariables G I n B)) a b) :=
      Subsingleton.elim _ _
    rw [hdec] at hlocal
    exact hlocal

end NilpotentLieFiltration
end Erdos3

end

end OAI

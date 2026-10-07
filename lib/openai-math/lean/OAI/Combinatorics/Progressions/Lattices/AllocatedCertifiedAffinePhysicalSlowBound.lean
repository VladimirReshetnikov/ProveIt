/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateResetSuccessor
import OAI.Combinatorics.Progressions.Dynamics.CommonRefilteredGlobalMarkedFamilyReset
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateKeptSymbolFactors
import OAI.Combinatorics.Progressions.Linear.ActualCandidateSlowProjectionMass
import OAI.Combinatorics.Progressions.Sampling.FullTaggedRationalChartGrid

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

local notation "wt" => fullTaggedVariableWeight (X := X) J

noncomputable def globalChart :
    (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ :=
  fullTaggedAffineMapChart J (fullTaggedRealMatrixProjection J C.projection) C.translate

noncomputable def slowChart :
    (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ :=
  fullTaggedSlowProjectionChart J (fullTaggedRealMatrixProjection J C.projection)
    (fun i => (N i : ℝ)) poly (fun j => (P.centerLift j).val)

noncomputable def commonDenominator : ℕ := ∏ j, C.denominator j

theorem globalChart_support (i : X ⊕ (Σ j, J j)) :
    C.globalChart i ∈ weightedSupportLE wt (wt i) :=
  fullTaggedAffineMapChart_support J _ _ i

theorem slowChart_support
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (i : X ⊕ (Σ j, J j)) :
    C.slowChart i ∈ weightedSupportLE wt (wt i) :=
  fullTaggedSlowProjectionChart_support J _ _ poly hpoly _ i

theorem globalChart_top (i : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent wt (wt i) (C.globalChart i) =
      fullTaggedLinearMapChart J (fullTaggedRealMatrixProjection J C.projection) i :=
  fullTaggedAffineMapChart_top J _ _ i

theorem slowChart_top (i : X ⊕ (Σ j, J j)) :
    weightedHomogeneousComponent wt (wt i) (C.slowChart i) =
      aeval (fun a => weightedHomogeneousComponent wt (wt a) (C.globalChart a))
        (normalizedRealPolynomialChart (fun x => (N x : ℝ))
          (fullTaggedMajorTopCoordinates J poly) i) := by
  simp only [C.globalChart_top]
  exact fullTaggedSlowProjectionChart_top J _ _ poly _ i

theorem globalChart_top_mem (x : X ⊕ (Σ j, J j) → ℝ) :
    (fun i => MvPolynomial.eval x
      (weightedHomogeneousComponent wt (wt i) (C.globalChart i))) ∈ K := by
  apply fullTaggedAffineMapChart_top_mem_set J _ _
    (fun j => realRationalCoordinateSpan (C.space j)) _ K _ x
  · intro j y
    rw [← C.range_eq j]
    exact LinearMap.mem_range_self _ y
  · intro y hy
    rw [C.constraint]
    exact hy

theorem commonDenominator_pos : 0 < C.commonDenominator :=
  Finset.prod_pos (fun j _ => C.denominator_pos j)

theorem commonDenominator_bound :
    (C.commonDenominator : ℝ) ≤
      Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine) := by
  rw [commonDenominator, Nat.cast_prod]
  calc
    _ ≤ ∏ _j : Fin m, Real.exp (certifiedAffineCenterBudget pAffine) :=
      Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => C.denominator_bound j)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]

theorem globalChart_top_grid (v : X ⊕ (Σ j, J j)) :
    realPolynomialCoefficientGrid C.commonDenominator
      (weightedHomogeneousComponent wt (wt v) (C.globalChart v)) := by
  rw [C.globalChart_top]
  apply fullTaggedLinearMapChart_coefficientGrid J
    (fullTaggedRealMatrixProjection J C.projection) C.commonDenominator
  intro j i a
  obtain ⟨z, hz⟩ := C.projection_grid j i a
  have hdiv : C.denominator j ∣ C.commonDenominator :=
    Finset.dvd_prod_of_mem C.denominator (Finset.mem_univ j)
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨(k : ℤ) * z, ?_⟩
  have hentry : fullTaggedRealMatrixProjection J C.projection j (Pi.single a 1) i =
      (C.projection j i a : ℝ) := by
    change (Matrix.mulVecLin (fun (i a : J j) => (C.projection j i a : ℝ)))
      (Pi.single a (1 : ℝ)) i = (C.projection j i a : ℝ)
    exact congrFun (Matrix.mulVec_single_one
      (fun (i a : J j) => (C.projection j i a : ℝ)) a) i
  rw [hentry, hk, Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← hz]
  ring

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound

theorem exists_allocatedCertifiedAffineFamilyReset (s a : ℕ) :
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
    ∀ (keep : LayerSamplerVariables G I n B → Prop),
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
        (fullMarkedNativeInput (s + 1) a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ mReset ∧
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark.filtration φ marked
        observable weight cost massThreshold scoreThreshold)
      {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
      (affine : P.CertifiedAffineRefinement K pAffine)
      (hkeep : ∀ z : affine.refinement.problem.productive,
        (affine.refinement.problem.chart z).keep = keep)
      (EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (factors : GlobalMarkedNativeFactors Fmark.filtration bF ν hF
        (fullTaggedVariableWeight J)
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
        (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fullTaggedVariableWeight J) affine.globalChart affine.globalChart_support
          (Fmark.filtration.realification.polynomialOrbitCoordinates _ marked)) EF RF),
      Fmark.filtration.PolynomialRationalGrid bF (fullTaggedVariableWeight J) nFinal factors.right →
      (∀ z : affine.refinement.problem.productive,
        let C := affine.refinement.problem.chart z
        Fmark.filtration.PolynomialSlowBound bF (fun _ : C.Variables => 1)
          (fun i => (sampler.sides i.val : ℝ)) (Real.exp ((pNative + 2) ^ a))
          (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
            C.integerChart_support factors.left)) →
      (∀ i : {i : LayerSamplerVariables G I n B // keep i},
        Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ (sampler.sides i.val : ℝ)) →
    ∀ (q densityCost cutoff : ℝ),
      Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
      (∀ z : affine.refinement.problem.productive,
        let C := affine.refinement.problem.chart z
        IsDenseCommonStrideBox (fun i : C.Variables => sampler.sides i.val)
          densityCost C.slice.integerPoints) →
      Real.exp densityCost * ((s + 1 + 1 : ℕ) : ℝ) ≤ cutoff →
      (∀ i, keep i → cutoff ≤ layerSamplerBox B U btag S i) →
      (∀ z : (affine.refinement.problem.withKeep keep hkeep).productive,
        D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
          (fun i : {i : LayerSamplerVariables G I n B // keep i} => (sampler.sides i.val : ℝ))
          q l W (D.filtration.realification.polynomialOrbitCoordinates _
            ((affine.refinement.problem.withKeep keep hkeep).candidate z).orbit)) →
      Nonempty (AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
        affine.refinement.problem keep hkeep W factors
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput (s + 1) a Cf pNative)
          + Cnative) ^ Cnative)) mReset) := by
  classical
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_common_refiltered_globalMarked_family_reset (s + 1) a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ narrow stride cells center _ sampler L M κ ξ μ χ _ _ _ _ _ _ _ _ d f
    D Fmark φ hφ ω hD bF ν hF hsurj keep bk W v hW hvspan vg hvgspan _ _
    H l nFinal pMap pNative hH hl hnFinal hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
    hd hκ hξ hμ hχ hvars hHp hbracketD hbracketF hkernel hentries hv hvg
  obtain ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, hrun⟩ :=
    hreset D.filtration Fmark.filtration φ hφ D.basis ω hD bF ν hF hsurj
      bk W v hW hvspan vg hvgspan H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
      hsrc htgt hHmap hlmap hmabsorb (by simpa using hd) hκ hξ hμ hχ hvars hHp
      hbracketD hbracketF hkernel hentries hv hvg
  refine ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, ?_⟩
  intro marked observable weight cost massThreshold scoreThreshold P K pAffine affine hkeep
    EF RF factors hgrid hslow hside q densityCost cutoff hq hqmap hdensity hcutoff hlong hcommon
  let Q := affine.refinement.problem.withKeep keep hkeep
  have hfixed (z : Q.productive) :=
    (affine.refinement.problem.chart z).withKeep_chart_fixed keep (hkeep z)
      affine.globalChart (affine.chart_fixed z)
  have hslow' (z : Q.productive) :=
    (affine.refinement.problem.chart z).withKeep_polynomialSlowBound keep (hkeep z)
      Fmark.filtration bF factors.left (Real.exp ((pNative + 2) ^ a)) (hslow z)
  have hmarked (z : Q.productive) := (Q.candidate z).formal_mark_group hφ (by
    simp only [max_self]
    apply (Q.chart z).slice_length_gt_of_dense_cutoff
      ((affine.refinement.problem.chart z).withKeep_dense keep (hkeep z) densityCost (hdensity z))
      (s + 1) hcutoff
    exact hlong)
  obtain ⟨left, middle, right, native, hfactors⟩ := hrun
    (fullTaggedVariableWeight J) affine.globalChart affine.globalChart_support
    (Fmark.filtration.realification.polynomialOrbitCoordinates _ marked) EF RF factors hgrid
    (fun _ : Q.productive => fun i : {i : LayerSamplerVariables G I n B // keep i} => (sampler.sides i.val : ℝ))
    (fun _ => q) (fun z => (Q.chart z).integerChart) (fun z => (Q.chart z).integerChart_support)
    (fun _ => hside) (fun _ => hq) (fun _ => hqmap) hfixed hslow'
    (fun z => D.filtration.realification.polynomialOrbitCoordinates _ (Q.candidate z).orbit)
    hmarked hcommon
  exact ⟨{
    localLeft := left
    localMiddle := middle
    localRight := right
    native := native
    source_factor := fun z => (hfactors z).1
    projection_left := fun z => (hfactors z).2.1
    projection_right := fun z => (hfactors z).2.2.1
    projection_middle := fun z => (hfactors z).2.2.2.1
    slow_left := fun z => (hfactors z).2.2.2.2.1
    grid_right := fun z => (hfactors z).2.2.2.2.2.1
    native_log := fun z => (hfactors z).2.2.2.2.2.2.1 }⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realChartSubstitute PolynomialRationalGrid PolynomialSlowBound
  CertifiedFullChartFiniteHistory.outer

theorem exists_allocatedCertifiedAffineGlobalTerminal (t a : ℕ) :
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
    ∀ (H : ℕ) (pFull : ℝ), 1 ≤ H → 0 ≤ pFull →
      (Fintype.card ι : ℝ) ≤ pFull →
      (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pFull →
      (H : ℝ) ≤ Real.exp pFull →
      Real.exp budget * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget pAffine)) ^ t ≤
        Real.exp pFull →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
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
          ∀ {Υ : Type*} [Fintype Υ] (v : Υ → ℕ), (∀ i, 0 < v i) →
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
  obtain ⟨Ce, Cr, hCe, hCr, hterminal⟩ :=
    exists_controlled_terminal_globalMarkedNativeFactors t a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ ξ stride cells center _ sampler L M _ _ _ _ s d D Fmark φ marked observable weight
    cost massThreshold scoreThreshold P ι η _ _ bF ω hF W basis lift Z Bphase budget pAffine
    history affine hW hcontrol hpoly hZ H pFull hH hpFull hι hvars hHp hden hbracket
  let wt := fullTaggedVariableWeight (X := X) J
  let β := affine.globalChart
  let δ := affine.slowChart
  have hden' : Real.exp budget * (affine.commonDenominator : ℝ) ^ t ≤ Real.exp pFull :=
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Nat.cast_nonneg _) affine.commonDenominator_bound t)
      (Real.exp_nonneg _)).trans hden
  obtain ⟨q, nFinal, hq, hqB, hn, hnB, hdiv, hproduce⟩ := hterminal
    Fmark bF ω hF J W basis lift Z Set.univ U poly N Bphase budget history hW hcontrol
    β δ affine.globalChart_support (affine.slowChart_support hpoly)
    affine.slowChart_top affine.globalChart_top_mem
    affine.commonDenominator H pFull affine.commonDenominator_pos hH hpFull hι hvars hHp
    hden' hbracket affine.globalChart_top_grid
  refine ⟨affine.commonDenominator_pos, affine.commonDenominator_bound,
    q, nFinal, hq, hqB, hn, hnB, hdiv, ?_⟩
  exact hproduce (Fmark.realification.polynomialOrbitCoordinates wt marked) hZ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

theorem projection_fixes_original
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    (j : Fin m) (x : J j → ℝ) (hx : x ∈ U j) :
    fullTaggedRealMatrixProjection J C.projection j x = x := by
  apply C.fixes_space j x
  exact retained_tag_le_of_product_constraint K
    (fun j => realRationalCoordinateSpan (C.space j)) C.constraint hretained j hx

theorem slowChart_mass
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    {dTag : ℝ} (hdTag : 0 ≤ dTag)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ dTag)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : C.refinement.problem.productive) (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes
      (fun a : (C.refinement.problem.chart z).Variables => layerSamplerBox B U b S a.val)
      (aeval (integerSampledRealChart (C.refinement.problem.chart z).integerChart)
        (C.slowChart i))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) dTag
        (((pAffine + ((pAffine + 2) ^ 2 + 2) ^ 63) + 2) ^ 8) := by
  have h := (C.refinement.problem.chart z).slowProjection_mass C.projection
    (C.projection_fixes_original hretained) hdTag C.projection_height hdim
    hτ1 hξ1 hp hσ1 Cgeo hCgeo hchart hsmall i
  rw [C.refinement.problem.chart_centerLift z] at h
  exact h

theorem slowChart_mass_sides
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    {dTag : ℝ} (hdTag : 0 ≤ dTag)
    (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ dTag)
    (hτ1 : τ ≤ 1) (hξ1 : ξ ≤ 1)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)
    (z : C.refinement.problem.productive) (i : X ⊕ (Σ j, J j)) :
    realPolynomialMass (scaleMvPolynomialAxes
      (fun a : (C.refinement.problem.chart z).Variables => (A.sides a.val : ℝ))
      (aeval (integerSampledRealChart (C.refinement.problem.chart z).integerChart)
        (C.slowChart i))) ≤
      actualCandidateSlowProjectionMassBudget m
        (Fintype.card (LayerSamplerVariables G I n B)) dTag
        (((pAffine + ((pAffine + 2) ^ 2 + 2) ^ 63) + 2) ^ 8) := by
  have h := (C.refinement.problem.chart z).slowProjection_mass_sides C.projection
    (C.projection_fixes_original hretained) hdTag C.projection_height hdim
    hτ1 hξ1 hp hσ1 Cgeo hCgeo hchart hsmall i
  rw [C.refinement.problem.chart_centerLift z] at h
  exact h

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem

noncomputable def allocatedAffineResetCompareExponent (s : ℕ) : ℕ :=
  Classical.choose (exists_allocatedCertifiedAffineFamilyReset s 1)

noncomputable def allocatedAffineResetFactorExponent (s : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1))

noncomputable def allocatedAffineResetLiftExponent (s : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec
    (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1)))

theorem allocatedAffineReset_exponents_ge_two (s : ℕ) :
    2 ≤ allocatedAffineResetCompareExponent s ∧
    2 ≤ allocatedAffineResetFactorExponent s ∧
    2 ≤ allocatedAffineResetLiftExponent s := by
  have h := Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec (exists_allocatedCertifiedAffineFamilyReset s 1)))
  exact ⟨h.1, h.2.1, h.2.2.1⟩

noncomputable def allocatedAffineResetLogBudget (s : ℕ) (pNative : ℝ) : ℝ :=
  (markedNativeLiftInput
    (fullMarkedNativeInput (s + 1) 1 (allocatedAffineResetFactorExponent s) pNative) +
    allocatedAffineResetLiftExponent s) ^ allocatedAffineResetLiftExponent s

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
    (C : P.CertifiedAffineRefinement K pAffine)

theorem slowChart_physical_abs_le
    (hretained : ∀ x, (∀ j, (fun i => x (Sum.inr ⟨j, i⟩)) ∈ U j) → x ∈ K)
    {dTag : ℝ} (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ dTag)
    (x : X → ℤ) (hx : x ∈ integerBox N) (z : X ⊕ (Σ j, J j)) :
    |MvPolynomial.eval (fun v => (P.physicalIntegerPoint x v : ℝ)) (C.slowChart z)| ≤
      max 1 (dTag * Real.exp (((pAffine + ((pAffine + 2) ^ 2 + 2) ^ 63) + 2) ^ 8)) := by
  exact fullTaggedSlowProjectionChart_physical_abs_le_rational J U C.projection
    (C.projection_fixes_original hretained) N poly hm P.centerLift x hx
    C.projection_height hdim z

end AllocatedExternalCandidateProblem.CertifiedAffineRefinement
end Erdos3.VectorPolynomial

end

end OAI

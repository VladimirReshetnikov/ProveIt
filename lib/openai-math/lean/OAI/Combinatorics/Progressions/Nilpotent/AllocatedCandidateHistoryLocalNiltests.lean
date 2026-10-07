import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateKeptSymbolFactors
import OAI.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateSamplerFacts

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

theorem exists_history_current_grade_local_niltests
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (r a : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bhistory Bstage budget : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      (eQ.baseChange ℝ) lift Z Set.univ U poly N Bhistory r)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2 budget)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bstage
      (r * (Fintype.card η * m)))
    (HMap l : ℕ) (pMap : ℝ) (hHMap : 1 ≤ HMap) (hl : 0 < l) (hpMap : 0 ≤ pMap)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp pMap) (hlExp : (l : ℝ) ≤ Real.exp pMap)
    (H : ℕ) (p qNative : ℝ) (hH : 1 ≤ H) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hVars : (Fintype.card Vars : ℝ) ≤ p)
    (hχ : (Fintype.card χ : ℝ) ≤ p) (hHExp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p)
    (hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a))
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ))
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pK Mbound LongSide : ℝ) (hpK : 0 ≤ pK) (hBstage : Bstage ≤ pK)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK) (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound)
    (hLong : 1 ≤ LongSide) (hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i)
    (hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide)
    (hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (Hθ : ℕ) (pLocal : ℝ)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hpLocal : 1 ≤ pLocal) (hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal)
    (hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ)) :
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧
      ∀ (j : η) (z : P.productive) (score : (Vars → ℤ) → ℝ),
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card κ * reset ∧
      ∃ slice : ResidueBoxSlice (fun i : Vars => A.sides i.val) q,
        IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
          ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) slice.integerPoints ∧
        (𝔼 x : (∀ i : Vars, Fin (A.sides i.val)), score (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ slice.integerPoints, score x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest (fun _ : Vars => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ slice.integerPoints,
          majorPhasePlateauSignal J (r + 1) poly
            (fun i => (P.centerLift (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
            (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J (r + 1) (Fmark.realSymbolGradeQuotientPolynomial bF ν hF
                (fullTaggedVariableWeight J) (fast).toSubmodule (r + 1)
                (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint keep x ((Q).chart z).fixed)
              (z.val.1.val, z.val.2.val)) *
              star (T.eval (commonStrideIndex (fun i => (slice.start i : ℤ)) q x))‖ := by
  obtain ⟨lLocal, hlLocal, hlLocalBound, _, hmarkedFactors⟩ :=
    P.exists_withKeep_marked_frozen_symbol_factors keep hkeep bD ω hD bF ν hF hφ
      hHMap hl hentries hpMap hsource htarget hHMapExp hlExp
  have hcommon' : Real.exp budget * (lLocal : ℝ) ≤ Real.exp p :=
    (mul_le_mul_of_nonneg_left hlLocalBound (Real.exp_nonneg _)).trans hcommon
  obtain ⟨qCurrent, _, _, reset, hreset, hresetBound, _, hlocal⟩ :=
    exists_allocated_controlled_frozen_current_grade_local_niltest (Deck := Deck) B U btag hb o S hRad hσ poly hm
      s a keep Fmark bF ν hF H lLocal p hH hlLocal hp hκ hVars hχ hHExp hbracket
      history.outer.1 history.outer.2 N A.size_pos hcontrol hcommon' hallowance hNreset
  refine ⟨reset, hreset, hresetBound, ?_⟩
  intro j z score
  obtain ⟨El, Pl, Rl, hprod, hPl, hEl, hRl⟩ :=
    hmarkedFactors z qNative W (hlength z) (hfactor z)
  have hsidePos : ∀ i : Vars, (0 : ℝ) < A.sides i.val :=
    fun i => (Real.exp_pos _).trans_le (hNreset i)
  have hEl' := Fmark.symbolSlowBound_mono bF ν hF (fun _ : Vars => 1)
    (fun i => (A.sides i.val : ℝ)) hsidePos hmapSlow El hEl
  have hden : ((Hθ ^ Fintype.card κ * reset : ℕ) : ℝ) ≤ Real.exp pLocal := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_left hresetBound (Nat.cast_nonneg _)).trans hLocalDen
  have hrecover := P.withKeep_chart_recovered z
  have hspatial := P.currentGrade_spatial_support z
  have hfixed := ((Q).chart z).fixed_in_box
  exact hlocal hr fast vg hspan hvg eQ j P.centerLift z.val.1.val z.val.2.val
    (P.chart z).sample (P.chart z).read hrecover A.trim_pos hτ hξ hspatial
    ((Q).chart z).fixed hfixed hσone Cgeo hCgeo hchart hsmall hpoly
    history.K Bstage pK Mbound LongSide (r * (Fintype.card η * m)) hcertificate
    (fun point hpoint => history.retained point (Set.mem_univ _) hpoint)
    hpK hBstage hJ hM hcap hLong hlong hthreshold gmark
    (fun point hpoint d hd => history.invariant_outer point hpoint d (by omega))
    El Pl Rl hprod hPl hEl' hRl Hθ pLocal (hθ j) hpLocal hLocalDim hLocalSize hden score hNLocal

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

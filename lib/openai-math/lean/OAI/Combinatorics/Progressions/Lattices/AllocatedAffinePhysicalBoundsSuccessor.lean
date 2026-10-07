import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateRoundedThresholdSuccessor
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget
import OAI.Combinatorics.Progressions.Nilpotent.NativeResetBracketGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
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

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

variable (selected : P.CertifiedThresholdAffineRefinement K p separation)

@[simp] theorem problem_physicalIntegerPoint (x : X → ℤ) :
    selected.problem.physicalIntegerPoint x = P.physicalIntegerPoint x := rfl

@[simp] theorem withKeep_physicalIntegerPoint
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    (x : X → ℤ) :
    (selected.problem.withKeep keep hkeep).physicalIntegerPoint x =
      P.physicalIntegerPoint x := rfl

theorem withKeep_original_dense
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    (z : (selected.problem.withKeep keep hkeep).productive) :
    IsDenseCommonStrideBox
      (fun i : ((selected.problem.withKeep keep hkeep).chart z).Variables => A.sides i.val)
      cost ((selected.problem.withKeep keep hkeep).chart z).slice.integerPoints := by
  suffices h : ∀ (keep' : LayerSamplerVariables G I n B → Prop)
      (heq : (selected.problem.chart z).keep = keep'),
      IsDenseCommonStrideBox
        (fun i : ((selected.problem.chart z).withKeep keep' heq).Variables => A.sides i.val)
        cost ((selected.problem.chart z).withKeep keep' heq).slice.integerPoints by
    exact h keep (hkeep z)
  intro keep' heq
  cases heq
  exact selected.original_dense z

noncomputable def conclusion_normalized {outputCost : ℝ}
    (hcutoff : candidateSideCutoffCost separation ≤ outputCost)
    (out : selected.problem.Conclusion outputCost
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) :
    P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)) := by
  simpa only [max_eq_left hcutoff] using selected.conclusion out

noncomputable def conclusion_of_withKeep_normalized
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    {outputCost : ℝ} (hcutoff : candidateSideCutoffCost separation ≤ outputCost)
    (out : (selected.problem.withKeep keep hkeep).Conclusion outputCost
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) :
    P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)) :=
  selected.conclusion_normalized hcutoff
    (selected.problem.conclusion_of_withKeep keep hkeep out)

theorem canonical_cutoff_le_recursive (degree slowExponent : ℕ) {input : ℝ}
    (hinput : 0 ≤ input) :
    candidateSideCutoffCost (Real.exp
      (candidatePrimitiveFreezingCutoff degree slowExponent input)) ≤
      finiteFreezingRecursiveParameter
        (candidatePrimitivePhysicalBudgetExponent degree slowExponent) input := by
  apply (candidatePrimitiveFreezingCutoff_integer_cost degree slowExponent hinput).trans
  apply (candidatePrimitiveFreezingCutoff_add_two_le_budget degree slowExponent hinput).trans
  unfold finiteFreezingRecursiveParameter
  have hbudget : 0 ≤ (input + candidatePrimitivePhysicalBudgetExponent degree slowExponent) ^
      candidatePrimitivePhysicalBudgetExponent degree slowExponent := by positivity
  linarith

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

theorem conclusion_of_affinePhysicalTerminal_nativeReset_degreeRule
    {p logSlow massLog : ℝ} {denominator e : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
      data.selected.problem (fun i => candidateSideCutoff separation ≤ A.sides i)
      (data.selected.common_keep hcost) W data.factors (Real.exp logSlow) denominator)
    (hp0 : 0 ≤ p)
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1 p))
    (hDNative : D.GeometryComplexityLE p)
    (hRetainedCount : (Fintype.card { i : LayerSamplerVariables G I n B //
      candidateSideCutoff separation ≤ A.sides i } : ℝ) ≤ p)
    (hMarkedDimension : (nMarkedBasis : ℝ) ≤ p)
    (hSectionMapHeight : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hdenominatorDvd : data.nFinal ∣ denominator)
    (hlogSlow : logSlow ≤ p)
    (hphysical : (pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
      allocatedEarlyAffineLeftExponent (s + 1) 4 ≤ p)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p)
    (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ p)
    (hmassLog : massLog ≤ p)
    (hmassInput : Real.exp (-massLog) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE p)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ p)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ p)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1) p) outputCost) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let keep : LayerSamplerVariables G I n B → Prop :=
    fun i => candidateSideCutoff separation ≤ A.sides i
  let hkeep := data.selected.common_keep hcost
  let reset' : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
      data.selected.problem keep hkeep W data.factors (Real.exp p) denominator :=
    { reset with
      slow_left := fun z => D.filtration.polynomialSlowBound_mono D.basis
        (fun _ : {i // keep i} => 1) (fun i => (A.sides i.val : ℝ))
        (fun i => Nat.cast_pos.mpr (A.sides_pos i.val))
        (Real.exp_le_exp.mpr hlogSlow) _ (reset.slow_left z) }
  have hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c
      (fun _ : {i // keep i} => 1) (fun i => (A.sides i.val : ℝ)) (Real.exp p)
      (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1)
        (integerSampledRealChart ((data.selected.problem.withKeep keep hkeep).chart z).integerChart)
        ((data.selected.problem.withKeep keep hkeep).chart z).integerChart_support data.factors.left) := by
    intro z
    suffices h : ∀ (keep' : LayerSamplerVariables G I n B → Prop)
        (heq : (data.selected.problem.chart z).keep = keep'),
        Fmark.filtration.PolynomialSlowBound c
          (fun _ : ((data.selected.problem.chart z).withKeep keep' heq).Variables => 1)
          (fun i => (A.sides i.val : ℝ)) (Real.exp p)
          (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : ((data.selected.problem.chart z).withKeep keep' heq).Variables => 1)
            (integerSampledRealChart ((data.selected.problem.chart z).withKeep keep' heq).integerChart)
            ((data.selected.problem.chart z).withKeep keep' heq).integerChart_support data.factors.left) by
      exact h keep (hkeep z)
    intro keep' heq
    cases heq
    exact Fmark.filtration.polynomialSlowBound_mono c
      (fun _ : (data.selected.problem.chart z).Variables => 1)
      (fun i => (A.sides i.val : ℝ))
      (fun i => Nat.cast_pos.mpr (A.sides_pos i.val))
      (Real.exp_le_exp.mpr hphysical) _ (data.local_left z)
  have hgrid := Fmark.filtration.polynomialRationalGrid_of_dvd c
    (fullTaggedVariableWeight J) data.nFinal_pos hdenominatorDvd data.factors.right data.right_grid
  have hside (i : {i // keep i}) :
      Real.exp (candidatePrimitiveFreezingCutoff s 1 p) ≤ (A.sides i.val : ℝ) := by
    rw [← hseparation]
    exact (lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr i.property)
  have hcostRounded : max cost (candidateSideCutoffCost separation) ≤
      candidatePrimitiveFreezingCutoff s 1 p + 2 := by
    apply max_le
    · have h := candidatePrimitiveFreezingCutoff_ge_input s 1 hp0
      linarith
    · rw [hseparation]
      exact candidatePrimitiveFreezingCutoff_integer_cost s 1 hp0
  have hmarkedPhysicalLeft : ∀ x ∈ integerBox N, ∀ i,
      |(c.baseChange ℝ).repr
        (Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
          ((data.selected.problem.withKeep keep hkeep).physicalIntegerPoint x) reset'.leftMark).coord i| ≤
        Real.exp p := by
    intro x hx i
    rw [data.selected.withKeep_physicalIntegerPoint keep hkeep x]
    exact (data.physical_left x hx i).trans (Real.exp_le_exp.mpr hphysical)
  obtain ⟨out⟩ := data.selected.problem.conclusion_of_roundedThreshold_nativeReset_degreeRule
    Fmark φ hφ keep hkeep W c ν hF data.factors reset' hσ1 H hH hchart hsmall hp
    1 hp0 hDNative (by simpa only [Fintype.card_eq_nat_card] using hRetainedCount)
    hMarkedDimension hSectionMapHeight
    hdenominatorPos hdenominatorBound (Real.exp_le_exp.mpr (by simp)) hslowMark hgrid
    (data.selected.withKeep_original_dense keep hkeep) hside hweight hscoreInput
    hcostRounded hcostInput hmassLog hmassInput dw hdb hW hsurj hξ1 ℓ hℓ
    hmarkedPhysicalLeft hOriginalLip hpositive hFGeo generators hspan hgeneratorCount
    hmarkedBasis hmarkHeight hgeneratorHeight htopKernel hOriginalNet outputCost lowerIH
  exact ⟨data.selected.conclusion out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

variable {Fmark φ hφ P W c ν hF basis lift Bphase budget pAffine pFull separation history data hcost}

structure AffinePhysicalTerminalData.SuccessorInputs
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (p : ℝ) (e : ℕ) (outputCost : ℝ) where
  nonnegative : 0 ≤ p
  separation_eq : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1 p)
  source_geometry : D.GeometryComplexityLE p
  retained_count : (Fintype.card { i : LayerSamplerVariables G I n B //
    candidateSideCutoff separation ≤ A.sides i } : ℝ) ≤ p
  marked_dimension : (nMarkedBasis : ℝ) ≤ p
  section_height : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p
  physical_budget : (pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
    allocatedEarlyAffineLeftExponent (s + 1) 4 ≤ p
  scale_le_one : ∀ j, σ j ≤ 1
  chart_bound : Fin m → ℝ
  chart_nonnegative : ∀ j, 0 ≤ chart_bound j
  chart_norm : ∀ j v,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ chart_bound j * ‖v‖
  chart_small : ∀ j, chart_bound j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  polynomial_degree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  weight_bound : ∀ x, ‖weight x‖ ≤ Real.exp p
  score_bound : Real.exp (-p) ≤ scoreThreshold
  cost_bound : cost ≤ p
  mass_log : ℝ
  mass_log_bound : mass_log ≤ p
  mass_bound : Real.exp (-mass_log) ≤
    Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold
  weights : Fin d → ℕ
  adapted : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ weights i})
  graded : BasisGradedSubmodule
    (D.filtration.associatedGradedBasis D.basis weights adapted) weights W.toSubmodule
  surjective : ∀ j, ∀ y ∈ Fmark.filtration.layer j,
    ∃ x ∈ D.filtration.layer j, φ x = y
  width_le_one : ξ ≤ 1
  lipschitz_constant : ℝ≥0
  lipschitz_bound : (lipschitz_constant : ℝ) ≤ Real.exp p
  lipschitz : ∀ x, letI := D.metricSpace; LipschitzWith lipschitz_constant (observable x)
  positive : ∀ x y, (observable x y).im = 0 ∧
    0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1
  marked_geometry : Fmark.GeometryComplexityLE p
  Generator : Type
  generator_fintype : Fintype Generator
  generators : Generator → D.filtration.AssociatedGraded
  generator_span : span ℚ (Set.range generators) = W.toSubmodule
  generator_count : (@Fintype.card Generator generator_fintype : ℝ) ≤ p
  marked_basis_height : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p
  mark_height : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p
  generator_height : ∀ i j,
    rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis weights adapted).repr (generators i) j) ≤ p
  top_kernel : ∀ x : L,
    x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0
  net : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
    (count : ℝ) ≤ Real.exp ((p + Real.log (1 / accuracy) + e) ^ e) ∧
    ∃ centers : Fin count → {x : X → ℤ // x ∈ integerBox N},
      ∀ x ∈ integerBox N, ∃ i, ∀ y,
        ‖observable x y - observable (centers i).val y‖ ≤ accuracy
  lower_degree : A.DegreeGlobalizationAt (E := E) weight s
    (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
    (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1) p) outputCost

theorem AffinePhysicalTerminalData.SuccessorInputs.conclusion_of_reset
    {p logSlow outputCost : ℝ} {denominator e : ℕ}
    (input : data.SuccessorInputs p e outputCost)
    (reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
      data.selected.problem (fun i => candidateSideCutoff separation ≤ A.sides i)
      (data.selected.common_keep hcost) W data.factors (Real.exp logSlow) denominator)
    (hlogSlow : logSlow ≤ p)
    (hdenominatorPos : 0 < denominator)
    (hdenominatorBound : (denominator : ℝ) ≤ Real.exp p)
    (hdenominatorDvd : data.nFinal ∣ denominator) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  let _ := input.generator_fintype
  exact P.conclusion_of_affinePhysicalTerminal_nativeReset_degreeRule Fmark φ hφ W c ν hF
    basis lift Bphase budget pAffine pFull separation history data hcost reset
    input.nonnegative input.separation_eq input.source_geometry input.retained_count
    input.marked_dimension input.section_height hdenominatorPos hdenominatorBound hdenominatorDvd
    hlogSlow input.physical_budget input.scale_le_one input.chart_bound input.chart_nonnegative
    input.chart_norm input.chart_small input.polynomial_degree input.weight_bound input.score_bound
    input.cost_bound input.mass_log_bound input.mass_bound input.weights input.adapted input.graded
    input.surjective input.width_le_one input.lipschitz_constant input.lipschitz_bound input.lipschitz
    input.positive input.marked_geometry input.generators input.generator_span input.generator_count
    input.marked_basis_height input.mark_height input.generator_height input.top_kernel input.net
    outputCost input.lower_degree

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

variable {Fmark φ hφ P W c ν hF basis lift Bphase budget pAffine pFull separation history data hcost}

noncomputable def AffinePhysicalTerminalData.successorInputsOfBounds
    (data : P.AffinePhysicalTerminalData c ν hF hφ W basis lift
      Bphase budget pAffine pFull 4 history separation)
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hpFull : 0 ≤ pFull)
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s p0 pFull)))
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (hmarkedDim : (nMarkedBasis : ℝ) ≤ p0)
    (hsection : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hcost0 : cost ≤ p0)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    {Generator : Type} [Fintype Generator]
    (v : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range v) = W.toSubmodule)
    (hcount : (Fintype.card Generator : ℝ) ≤ p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p0)
    (hv : ∀ i j, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v i) j) ≤ p0)
    (htop : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull)) outputCost) :
    data.SuccessorInputs (allocatedAffineCanonicalBudget s p0 pFull) e outputCost := by
  have bounds := allocatedAffineCanonicalBudget_bounds s hp0 hpFull
  refine {
    nonnegative := bounds.nonnegative
    separation_eq := hseparation
    source_geometry := hDgeo.mono D bounds.input
    retained_count := ?_
    marked_dimension := hmarkedDim.trans bounds.input
    section_height := fun i j => (hsection i j).trans bounds.input
    physical_budget := bounds.physical
    scale_le_one := hσ1
    chart_bound := Hchart
    chart_nonnegative := hHchart
    chart_norm := hchart
    chart_small := hsmall
    polynomial_degree := hpoly
    weight_bound := fun x => (hweight x).trans (Real.exp_le_exp.mpr bounds.input)
    score_bound := (Real.exp_le_exp.mpr (neg_le_neg bounds.input)).trans hscore
    cost_bound := hcost0.trans bounds.input
    mass_log := p0
    mass_log_bound := bounds.input
    mass_bound := hmass
    weights := ω
    adapted := hD
    graded := hW
    surjective := hsurj
    width_le_one := hξ1
    lipschitz_constant := ℓ
    lipschitz_bound := hℓ.trans (Real.exp_le_exp.mpr bounds.input)
    lipschitz := hLip
    positive := hpositive
    marked_geometry := hFgeo.mono Fmark bounds.input
    Generator := Generator
    generator_fintype := inferInstance
    generators := v
    generator_span := hspan
    generator_count := hcount.trans bounds.input
    marked_basis_height := fun i j => (hcForward i j).trans bounds.input
    mark_height := fun i j => (hmark i j).trans bounds.input
    generator_height := fun i j => (hv i j).trans bounds.input
    top_kernel := htop
    net := ?_
    lower_degree := lowerIH }
  · exact (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans
      (hvariables.trans bounds.input)
  · intro accuracy hacc hacc1
    obtain ⟨count, hcount, centers, hcenters⟩ := hnet accuracy hacc hacc1
    refine ⟨count, hcount.trans (Real.exp_le_exp.mpr ?_), centers, hcenters⟩
    have hlog : 0 ≤ Real.log (1 / accuracy) :=
      Real.log_nonneg ((one_le_div hacc).mpr hacc1)
    exact pow_le_pow_left₀ (by positivity) (by linarith [bounds.input]) e

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

theorem conclusion_of_affinePhysicalTerminal_zeroRestricted_degreeRule
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
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    {p outputCost : ℝ} {e : ℕ}
    (input : data.SuccessorInputs p e outputCost)
    (hresetBudget : allocatedAffineResetLogBudget s pNative ≤ p) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  have hcost : Real.exp cost ≤ separation := by
    rw [input.separation_eq]
    exact Real.exp_le_exp.mpr
      (input.cost_bound.trans (candidatePrimitiveFreezingCutoff_ge_input s 1 input.nonnegative))
  obtain ⟨denominator, hden, hdenBound, hdenDvd, ⟨reset⟩⟩ :=
    P.exists_affinePhysicalTerminal_nativeReset_of_zero_restriction Fmark φ hφ W c ν hF
      basis lift Bphase budget pAffine pFull separation history data hcost
      ω hD hsurj bk v hW hvspan vg hvgspan H l pMap pNative hH hl hpMap hpNative
      hsrc htgt hHmap hlmap hmabsorb hd hc hk hμ hχ hvars hHp
      hbracketD hbracketF hkernel hentries hv hvg hslow hsideBound q hq hqmap hcutoff
      initialLong hsub hzero
  exact input.conclusion_of_reset (hcost := hcost) reset hresetBudget hden
    (hdenBound.trans (Real.exp_le_exp.mpr hresetBudget)) hdenDvd

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

theorem conclusion_of_normalized_affinePhysicalTerminal_zeroRestricted_degreeRule
    {γ : Type} [Fintype γ]
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hpFull : 0 ≤ pFull)
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hMap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (v : γ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (hγ : (Fintype.card γ : ℝ) ≤ p0)
    (hvHeight : ∀ j i, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (q : ℝ) (l : ℕ) (hq0 : q ≤ p0) (hl : 0 < l) (hlBound : (l : ℝ) ≤ Real.exp p0)
    (hcost0 : cost ≤ p0)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    {outputCost : ℝ} {e : ℕ}
    (input : data.SuccessorInputs (allocatedAffineCanonicalBudget s p0 pFull) e outputCost) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  classical
  let Vars := {i : LayerSamplerVariables G I n B // kept i}
  have hvars : (Fintype.card Vars : ℝ) ≤ p0 :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le kept)).trans hvariables
  obtain ⟨hHeight0, hHeightInput, hHeightBracket, hHeightKernel, hHeightPoint⟩ :=
    allocatedAffineResetHeightLog_bounds hp0
  let H := ⌈Real.exp (allocatedAffineResetHeightLog p0)⌉₊
  obtain ⟨hH, hHBound, hd, hc, hbracketD, hbracketF⟩ :=
    D.nativeResetBracketGeometry_of_logBudget Fmark c hp0 hDgeo hFgeo hcForward hHeightBracket
  obtain ⟨r, hr, hrp, bk, hbk⟩ := exists_marked_kernel_basis_commonHeight_of_dim
    D.basis c φ hp0 (by simpa using hd) hc hMap
  let : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω) :=
    D.filtration.ordinarySymbolBasisFintype D.basis ω hD
  let : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν) :=
    Fmark.filtration.ordinarySymbolBasisFintype c ν hF
  let vg := D.filtration.gradedImagePointwiseSpanningFamily Fmark.filtration φ hφ
    c ν hF (fun _ : Vars => 1) v
  obtain ⟨hvgspan, _, hvgHeight, hsrcCount, htgtCount, hvgCount, _, _⟩ :=
    D.filtration.ordinaryGradedImagePointwiseSpanning_controlled Fmark.filtration φ hφ
      D.basis ω hD c ν hF W v hW hvspan hp0 (by simpa using hd) hc hγ hvars hvHeight
      (fun i j => hMap j i)
  have mapBounds := allocatedAffineResetMapBudget_bounds s hp0 hpFull
  have bounds := allocatedAffineCanonicalBudget_bounds s hp0 hpFull
  have expBounds := allocatedAffineCanonicalBudget_exp_bounds s hp0 hpFull
  have hsrc : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤
      allocatedAffineResetMapBudget s p0 pFull := by
    simpa only [Nat.card_eq_fintype_card] using hsrcCount.trans mapBounds.pointwise
  have htgt : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤
      allocatedAffineResetMapBudget s p0 pFull := by
    simpa only [Nat.card_eq_fintype_card] using htgtCount.trans mapBounds.pointwise
  have hχ : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν × γ) : ℝ) ≤
      allocatedAffineCanonicalNativeBudget s p0 pFull := by
    simpa only [Nat.card_eq_fintype_card] using
      (hvgCount.trans mapBounds.pointwise).trans bounds.native_map
  have hHmap : (H : ℝ) ≤ Real.exp (allocatedAffineResetMapBudget s p0 pFull) :=
    hHBound.trans (Real.exp_le_exp.mpr mapBounds.height)
  have hlmap : ((l * data.nFinal : ℕ) : ℝ) ≤
      Real.exp (allocatedAffineResetMapBudget s p0 pFull) :=
    allocatedAffineResetMapBudget_denominator s hp0 hpFull hlBound data.nFinal_bound
  have hkernel : ∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H := by
    intro i j
    exact (hbk j i).mono (Nat.ceil_mono (Real.exp_le_exp.mpr hHeightKernel))
  have hentries : ∀ i j, RationalHeightLE (c.repr (φ (D.basis j)) i) H :=
    fun i j => rationalHeightLE_ceil_exp ((hMap i j).trans hHeightInput)
  have hv : ∀ j i, RationalHeightLE
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H :=
    fun j i => rationalHeightLE_ceil_exp ((hvHeight j i).trans hHeightInput)
  have hvg : ∀ i z, RationalHeightLE
      ((Fmark.filtration.polynomialSymbolBasis c ν hF (fun _ : Vars => 1)).repr (vg i) z) H := by
    intro i z
    exact (hvgHeight i z).mono (Nat.ceil_mono (Real.exp_le_exp.mpr hHeightPoint))
  have hside : Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull +
      allocatedAffineResetCompareExponent s) ^ allocatedAffineResetCompareExponent s) ≤ separation := by
    rw [input.separation_eq]
    exact expBounds.compare_cutoff
  have hcutoff : Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation := by
    rw [input.separation_eq]
    simpa only [Nat.add_assoc] using expBounds.interpolation cost hcost0
  have hsub : ∀ i, kept i → initialLong i := by
    intro i hi
    by_contra hn
    have hside0 : Real.exp p0 ≤ separation := by
      rw [input.separation_eq]
      exact expBounds.cost_cutoff p0 le_rfl
    have hlong : separation < (A.sides i : ℝ) :=
      (lt_candidateSideCutoff separation).trans_le (Nat.cast_le.mpr hi)
    exact (not_lt_of_ge ((hshort i hn).trans hside0)) hlong
  exact P.conclusion_of_affinePhysicalTerminal_zeroRestricted_degreeRule Fmark φ hφ W c ν hF
    basis lift Bphase budget pAffine pFull separation history data
    ω hD input.surjective bk v hW hvspan vg hvgspan H l
    (allocatedAffineResetMapBudget s p0 pFull) (allocatedAffineCanonicalNativeBudget s p0 pFull)
    hH hl bounds.map_nonnegative bounds.native_nonnegative hsrc htgt hHmap hlmap
    expBounds.map_absorption (hd.trans bounds.native_input)
    (by simpa only [Fintype.card_fin] using hc.trans bounds.native_input)
    (by simpa only [Fintype.card_fin] using hrp.trans bounds.native_input)
    (hγ.trans bounds.native_input) hχ (hvars.trans bounds.native_input)
    (hHmap.trans (Real.exp_le_exp.mpr bounds.native_map)) hbracketD hbracketF
    hkernel hentries hv hvg expBounds.physical_absorption hside q
    ((Real.exp_le_exp.mpr hq0).trans expBounds.original_absorption)
    ((Real.exp_le_exp.mpr (add_le_add le_rfl hq0)).trans expBounds.mapped_absorption)
    hcutoff initialLong hsub hzero input bounds.reset

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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

include data in
theorem conclusion_of_affinePhysicalTerminal_bounds_degreeRule
    {γ : Type} [Fintype γ]
    (p0 : ℝ) (hp0 : 0 ≤ p0) (hpFull : 0 ≤ pFull)
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hMap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (v : γ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (hγ : (Fintype.card γ : ℝ) ≤ p0)
    (hvHeight : ∀ j i, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (q : ℝ) (l : ℕ) (hq0 : q ≤ p0) (hl : 0 < l) (hlBound : (l : ℝ) ≤ Real.exp p0)
    (hcost0 : cost ≤ p0)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s p0 pFull)))
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * massThreshold)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p0)
    (htop : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull)) outputCost) :
    Nonempty (P.Conclusion (max outputCost (candidateSideCutoffCost separation))
      (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  have hc := (D.nativeResetBracketGeometry Fmark c hp0 hDgeo hFgeo hcForward).2.1
  let input := data.successorInputsOfBounds p0 hp0 hpFull hseparation hDgeo hFgeo
    hvariables (by simpa only [Fintype.card_fin] using hc) hMap hσ1 Hchart hHchart hchart
    hsmall hpoly hweight hscore hcost0 hmass ω hD hW hsurj hξ1 ℓ hℓ hLip hpositive
    v hvspan hγ hcForward hmark hvHeight htop hnet outputCost lowerIH
  exact P.conclusion_of_normalized_affinePhysicalTerminal_zeroRestricted_degreeRule
    Fmark φ hφ W c ν hF basis lift Bphase budget pAffine pFull separation history data
    p0 hp0 hpFull hDgeo hFgeo hcForward hMap ω hD v hW hvspan hγ hvHeight hvariables
    q l hq0 hl hlBound hcost0 initialLong hshort hzero input

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

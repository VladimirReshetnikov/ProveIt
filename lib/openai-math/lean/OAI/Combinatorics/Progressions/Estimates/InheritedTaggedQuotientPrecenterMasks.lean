/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
import OAI.Combinatorics.Progressions.Linear.ExternalKernelPrecenterNativePointPartners
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidatePhysicalScore

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e dQ dQF : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s dQ)
    (hQ : Q.filtration = D.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold (M ⧸ Fmark.filtration.layerIdeal (s + 1)) s dQF)
    (hQF : QF.filtration = Fmark.filtration.quotientTop)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark.filtration φ marked)

noncomputable def topQuotient :
    AllocatedExternalLocalCandidate C Q QF.filtration
      (D.topQuotientMarkedMap Fmark φ hφ) (Fmark.topQuotientOrbit QF hQF marked) where
  orbit := D.topQuotientOrbit Q hQ candidate.orbit
  mark_on_slice u hu := by
    rw [D.topQuotientOrbit_eval Q hQ, Fmark.topQuotientOrbit_eval QF hQF]
    have hsquare :
        realificationMap (hnil := Q.filtration.lowerCentralSeries_eq_bot)
          (hM := QF.filtration.lowerCentralSeries_eq_bot)
          (D.topQuotientMarkedMap Fmark φ hφ)
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) =
        realificationMap (hnil := Fmark.filtration.lowerCentralSeries_eq_bot)
          (hM := QF.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (Fmark.filtration.layerIdeal (s + 1)))
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) := by
      apply NilpotentLieBCHGroup.ext
      exact D.topQuotientMarkedMap_real_mk Fmark φ hφ _
    rw [hsquare, candidate.mark_on_slice u hu]

@[simp] theorem topQuotient_orbit :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).orbit =
      D.topQuotientOrbit Q hQ candidate.orbit := rfl

theorem topQuotient_value (u : C.Variables → ℤ) :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).value u =
      (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
          (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) : Q.Space) := by
  unfold value
  rw [topQuotient_orbit, D.topQuotientOrbit_eval Q hQ]

theorem topQuotient_score (observable : (X → ℤ) → Q.Space → ℂ)
    (weight : (X → ℤ) → ℂ) :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).score observable weight =
      (𝔼 u ∈ C.slice.integerPoints, weight (C.physical u) *
        observable (C.physical u)
          (QuotientGroup.mk
            (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
              (hM := Q.filtration.lowerCentralSeries_eq_bot)
              (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
              (D.filtration.realification.polynomialOrbitEval _ u candidate.orbit)) : Q.Space)).re := by
  unfold score
  simp only [topQuotient_value]

theorem topQuotient_score_eq
    (observable : (X → ℤ) → D.Space → ℂ) (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
        observable x (QuotientGroup.mk g))
    (weight : (X → ℤ) → ℂ) :
    (candidate.topQuotient Fmark φ hφ Q hQ QF hQF).score descended weight =
      candidate.score observable weight := by
  rw [topQuotient_score]
  simp only [hrecovery, score, value]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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

namespace AllocatedExternalCandidateProblem

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e dQ dQF : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s dQ)
    (hQ : Q.filtration = D.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold (M ⧸ Fmark.filtration.layerIdeal (s + 1)) s dQF)
    (hQF : QF.filtration = Fmark.filtration.quotientTop)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.layerIdeal (s + 1))) g)) =
        observable x (QuotientGroup.mk g))

noncomputable def topQuotientProblem :
    AllocatedExternalCandidateProblem (E := E) A Q QF.filtration
      (D.topQuotientMarkedMap Fmark φ hφ) (Fmark.topQuotientOrbit QF hQF marked)
      descended weight cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).topQuotient Fmark φ hφ Q hQ QF hQF
  score z := by
    rw [(P.candidate z).topQuotient_score_eq Fmark φ hφ Q hQ QF hQF
      observable descended hrecovery weight]
    exact P.score z

theorem topQuotientProblem_ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.topQuotientProblem Fmark φ hφ Q hQ QF hQF descended hrecovery).ambientScore
      (D.topQuotientOrbit Q hQ ambient) z points = P.ambientScore ambient z points := by
  unfold ambientScore
  simp only [topQuotientProblem, D.topQuotientOrbit_eval, hrecovery]

theorem conclusion_of_topQuotient
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j,
      ∃ x ∈ D.filtration.layer j, φ x = y)
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.topQuotientProblem Fmark φ hφ Q hQ QF hQF descended hrecovery).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  have hmarked : D.topQuotientMarkedOrbit Fmark φ hφ Q hQ QF hQF lower.ambient =
      Fmark.topQuotientOrbit QF hQF marked := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact lower.marked
  obtain ⟨ambient, hquotient, hmark, _, _⟩ :=
    D.exists_marked_topQuotientOrbit_lift_of_quotient_eq Fmark φ hφ Q hQ QF hQF
      hsurj lower.ambient marked hmarked
  refine ⟨{
    ambient := ambient
    marked := hmark
    retained := lower.retained
    subset := lower.subset
    mass := lower.mass
    step := lower.step
    step_pos := lower.step_pos
    slice := lower.slice
    dense := lower.dense
    inside := lower.inside
    score := ?_
  }⟩
  intro z
  have he := P.topQuotientProblem_ambientScore Fmark φ hφ Q hQ QF hQF descended hrecovery
    ambient ⟨z.val, lower.subset z.property⟩ (lower.slice z).integerPoints
  rw [hquotient] at he
  exact (lower.score z).trans_eq he

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    (QF : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hQF : QF.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

noncomputable def refilteredFrozenObservable (x : X → ℤ) (source : Dref.RealGroup) : ℂ :=
  observable x (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) left *
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source *
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) right))

noncomputable def refilteredQuotientObservable (x : X → ℤ) : Q.Space → ℂ :=
  positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
    (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) markedMiddle))

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (hrecovery : ∀ x source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)
    (hfactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      D.filtration.realification.polynomialOrbitEval (fun _ => 1) u (P.candidate z).orbit =
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) left *
          realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
          D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) right)

include hσ1 H hH hchart hsmall hp hrecovery hfactor in

theorem refilteredQuotientCandidate_score (z : P.productive) :
    ((middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF).score
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight = (P.candidate z).score observable weight := by
  unfold AllocatedExternalLocalCandidate.score
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  congr 1
  rw [AllocatedExternalLocalCandidate.topQuotient_value]
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  have hmark := (middle z).mark_on_slice u hu
  rw [htags] at hmark
  have hr := hrecovery ((P.chart z).physical u)
    (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)
  simp only [RationalFilteredNilmanifold.markedTopQuotientDiagram, hmark] at hr
  rw [refilteredQuotientObservable, hr]
  unfold refilteredFrozenObservable AllocatedExternalLocalCandidate.value
  rw [hfactor z u hu, htags]

noncomputable def refilteredQuotientProblem :
    AllocatedExternalCandidateProblem (E := E) A Q QF.filtration
      (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit QF hQF markedMiddle)
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF
  score z := by
    rw [P.refilteredQuotientCandidate_score A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle hrecovery hfactor z]
    exact P.score z

omit [PseudoMetricSpace Fref.Space] in
include hfactor in

theorem refilteredAssembly_mark_on_slice
    (ambientMiddle : Dref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (hmarkedMiddle : map (realLieHomToRat (realificationLieHom (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W))).toLinearMap
      ambientMiddle.log = markedMiddle.log)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
        (D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked := by
  have hglobal := Dref.filtration.formal_mark_realEval Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (fullTaggedVariableWeight (X := X) J)
    ambientMiddle markedMiddle hmarkedMiddle (fun i => ((P.chart z).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hglobal
  have heval := D.externalCandidateOrbit_realEval W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
    (fun i => ((P.chart z).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at heval
  rw [heval]
  rw [← (P.candidate z).mark_on_slice u hu, hfactor z u hu]
  simp only [map_mul]
  rw [D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    hglobal, (middle z).mark_on_slice u hu]

theorem conclusion_of_refilteredQuotient
    (db : Basis ι ℚ L) (dw : ι → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (db '' {i | j ≤ dw i}))
    (fb : Basis κ ℚ M) (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (fb '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis db dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.refilteredQuotientProblem A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle hrecovery hfactor).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  have hcompat : Dref.topQuotientMarkedOrbit Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF lower.ambient =
      Fref.topQuotientOrbit QF hQF markedMiddle := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact lower.marked
  obtain ⟨ambientMiddle, _, hmarkedMiddle, hevalMiddle⟩ :=
    Dref.exists_marked_topQuotientOrbit_lift_externalFamily Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right) hrecovery
      (D.refilteredMarkedMap_layer_surjective Fmark φ hφ W Dref hDref Fref hFref
        db dw hdb fb fw hfb hW hsurj)
      lower.ambient markedMiddle hcompat
  let candidate := D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
  obtain ⟨restored, hmark, _, hkeep⟩ :=
    D.filtration.exists_formal_marked_orbit_restoration Fmark.filtration φ hφ
      fb fw hfb hsurj (fullTaggedVariableWeight (X := X) J) candidate marked
  have hretained (z : P.productive) (u : (P.chart z).Variables → ℤ)
      (hu : u ∈ (P.chart z).slice.integerPoints) :
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) restored =
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) candidate := by
    have hk := hkeep (fun i => ((P.chart z).chartValues u i : ℝ)) (by
      simpa only [polynomialOrbitRealEval_integer] using
        P.refilteredAssembly_mark_on_slice A Fmark φ hφ W Dref hDref Fref left right
          markedMiddle middle hfactor ambientMiddle hmarkedMiddle z u hu)
    simpa only [polynomialOrbitRealEval_integer] using hk
  refine ⟨{
    ambient := restored
    marked := hmark
    retained := lower.retained
    subset := lower.subset
    mass := lower.mass
    step := lower.step
    step_pos := lower.step_pos
    slice := lower.slice
    dense := lower.dense
    inside := lower.inside
    score := ?_
  }⟩
  intro z
  apply (lower.score z).trans_eq
  unfold ambientScore
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  let zp : P.productive := ⟨z.val, lower.subset z.property⟩
  have huOriginal : u ∈ (P.chart zp).slice.integerPoints := lower.inside z hu
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp zp u huOriginal
  change weight ((P.chart zp).physical u) *
      P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K
        ((P.chart zp).physical u)
        (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P.chart zp).chartValues u) lower.ambient)) =
    weight ((P.chart zp).physical u) * observable ((P.chart zp).physical u)
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((P.chart zp).chartValues u) restored))
  congr 1
  rw [hretained zp u huOriginal]
  have ha := D.externalCandidateOrbit_realEval W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at ha
  change _ = observable ((P.chart zp).physical u)
    (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      ((P.chart zp).chartValues u) (D.externalCandidateOrbit W Dref hDref (fullTaggedVariableWeight (X := X) J) left right ambientMiddle)))
  rw [ha]
  have hr := hevalMiddle ((P.chart zp).physical u)
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hr
  simpa only [refilteredQuotientObservable, refilteredFrozenObservable, ← htags] using hr

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

universe u

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
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

theorem refilteredFrozenObservable_recovery_of_coveredDiagram
    {inputDenominator k : ℕ} {p coverCost dictBound : ℝ}
    (rightDictionary : D.NativeGridRightDictionary inputDenominator dictBound)
    (covered : RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram
      D Fmark φ hφ W k rightDictionary.denominator p coverCost)
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ Real.exp ((p + 2) ^ k))
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid inputDenominator) :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 covered.Fref.basis
    letI := moduleTopology ℝ (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1)))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 covered.Q.basis
    letI := covered.Q.metricSpace
    letI := covered.Fref.metricSpace
    let diagram := covered.Dref.markedTopQuotientDiagram covered.Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) covered.Q
    let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    ∀ x ∈ integerBox N, ∀ source,
      positiveImageSlice diagram K
        (P.refilteredFrozenObservable A Fmark φ W covered.Dref left right x)
        (diagram source).2 (diagram source).1 =
          P.refilteredFrozenObservable A Fmark φ W covered.Dref left right x source := by
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 covered.Fref.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ covered.Dref.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 covered.Q.basis
  let := covered.Q.metricSpace
  let := covered.Fref.metricSpace
  dsimp only
  intro x hx
  apply rightDictionary.markedTopQuotient_recovery D Fmark φ hφ W
    covered.Dref covered.Fref covered.Q ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    (observable x)
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) left)
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) right) (hright x hx)
  dsimp only
  intro j
  exact covered.recovery
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x) left)
    (rightDictionary.representative j) (hleft x hx)
    (rightDictionary.representative_bounds j).2 (observable x) ℓ hℓ
    (hLip x hx) (hpositive x hx)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

section Operator

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

noncomputable def taggedRefilteredQuotientOperator
    (left right : D.RealGroup) (mark : Fref.Space) (f : D.Space → ℂ) : Q.Space → ℂ :=
  positiveImageSlice
    (Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    (fun source => f (QuotientGroup.mk
      (left * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source * right))) mark

theorem taggedRefilteredQuotientOperator_nonexpansive
    (left right : D.RealGroup) (mark : Fref.Space) (f g : D.Space → ℂ)
    (hf : ∀ z, 0 ≤ (f z).re) (hg : ∀ z, 0 ≤ (g z).re)
    {δ : ℝ} (hfg : ∀ z, ‖f z - g z‖ ≤ δ) (y : Q.Space) :
    ‖taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K left right mark f y -
      taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K left right mark g y‖ ≤ δ := by
  exact positiveImageExtension_nonexpansive
    (Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
    _ _ (fun source => hf _) (fun source => hg _) (fun source => hfg _) (y, mark)

theorem taggedRefilteredQuotientOperator_approx_on
    {Physical : Type*} (allowed : Physical → Prop)
    (left right : Physical → D.RealGroup) (mark : Physical → Fref.Space)
    (f : Physical → D.Space → ℂ) (g : D.Space → ℂ)
    (hf : ∀ x, allowed x → ∀ z, 0 ≤ (f x z).re) (hg : ∀ z, 0 ≤ (g z).re)
    {δ : ℝ} (hfg : ∀ x, allowed x → ∀ z, ‖f x z - g z‖ ≤ δ) :
    ∀ x, allowed x → ∀ y,
      ‖taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
          (left x) (right x) (mark x) (f x) y -
        taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
          (left x) (right x) (mark x) g y‖ ≤ δ := by
  intro x hx y
  exact taggedRefilteredQuotientOperator_nonexpansive D Fmark φ hφ W Dref Fref Q K
    (left x) (right x) (mark x) (f x) g (hf x hx) hg (hfg x hx) y

end Operator

section ActualProblem

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

namespace AllocatedExternalCandidateProblem

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

theorem refilteredQuotientObservable_eq_taggedOperator (x : X → ℤ) :
    P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
      left right markedMiddle K x =
    taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        (P.physicalIntegerPoint x) left)
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        (P.physicalIntegerPoint x) right)
      (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval
        (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) markedMiddle))
      (observable x) := rfl

theorem refilteredQuotientObservable_approx_on
    (allowed : (X → ℤ) → Prop) (representative : D.Space → ℂ)
    (hobs : ∀ x, allowed x → ∀ z, 0 ≤ (observable x z).re)
    (hrep : ∀ z, 0 ≤ (representative z).re)
    {δ : ℝ} (happrox : ∀ x, allowed x → ∀ z, ‖observable x z - representative z‖ ≤ δ)
    (x : X → ℤ) (hx : allowed x) (y : Q.Space) :
    ‖P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
        left right markedMiddle K x y -
      taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left)
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right)
        (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval
          (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) markedMiddle))
        representative y‖ ≤ δ := by
  rw [P.refilteredQuotientObservable_eq_taggedOperator Fmark φ hφ W Dref Fref Q
    left right markedMiddle K x]
  exact taggedRefilteredQuotientOperator_nonexpansive D Fmark φ hφ W Dref Fref Q K
    _ _ _ (observable x) representative (hobs x hx) hrep (happrox x hx) y

end AllocatedExternalCandidateProblem
end ActualProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

variable {Physical Bin : Type*}
    (left right : Physical → D.RealGroup) (mark : Physical → Fref.Space)
    (F : Physical → D.Space → ℂ) (centers : Bin → D.Space → ℂ)
    {ε : ℝ} (hnet : ∀ x, ∃ i, ∀ z, ‖F x z - centers i z‖ ≤ ε)

noncomputable def inheritedTaggedQuotientFamily : Physical → (Physical × Q.Space) → ℂ :=
  fun x y => taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
    (left y.1) (right y.1) (mark y.1) (F x) y.2

noncomputable def inheritedTaggedQuotientCenters : Bin → (Physical × Q.Space) → ℂ :=
  fun i y => taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
    (left y.1) (right y.1) (mark y.1) (centers i) y.2

theorem inheritedTaggedQuotient_original_index_approx
    (hF : ∀ x z, 0 ≤ (F x z).re) (hcenters : ∀ i z, 0 ≤ (centers i z).re)
    (x : Physical) (y : Physical × Q.Space) :
    ‖inheritedTaggedQuotientFamily D Fmark φ hφ W Dref Fref Q K left right mark F x y -
      inheritedTaggedQuotientCenters D Fmark φ hφ W Dref Fref Q K left right mark centers
        (externalNetIndex F centers hnet x) y‖ ≤ ε := by
  exact taggedRefilteredQuotientOperator_nonexpansive D Fmark φ hφ W Dref Fref Q K
    (left y.1) (right y.1) (mark y.1) (F x)
    (centers (externalNetIndex F centers hnet x))
    (hF x) (hcenters _) (externalNetIndex_approx F centers hnet x) y.2

theorem inheritedTaggedQuotient_approx_on_original_bin
    (hF : ∀ x z, 0 ≤ (F x z).re) (hcenters : ∀ i z, 0 ≤ (centers i z).re)
    (i : Bin) (x : Physical) (hbin : externalNetIndex F centers hnet x = i)
    (y : Q.Space) :
    ‖taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
        (left x) (right x) (mark x) (F x) y -
      taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
        (left x) (right x) (mark x) (centers i) y‖ ≤ ε := by
  have h := inheritedTaggedQuotient_original_index_approx D Fmark φ hφ W Dref Fref Q K
    left right mark F centers hnet hF hcenters x (x, y)
  simpa only [inheritedTaggedQuotientFamily, inheritedTaggedQuotientCenters, hbin] using h

theorem inheritedTaggedQuotient_selected_score_lower
    {Site : Type*} [Fintype Site] (law : FiniteProbabilityWeights Site)
    (physical : Site → Physical) (point : Site → Q.Space) (weight : Site → ℝ)
    (hF : ∀ x z, 0 ≤ (F x z).re) (hcenters : ∀ i z, 0 ≤ (centers i z).re)
    {B δ : ℝ} (hB : 0 ≤ B) (hweight : ∀ t, |weight t| ≤ B)
    (hscore : δ ≤ law.mean (fun t => weight t *
      (taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
        (left (physical t)) (right (physical t)) (mark (physical t))
        (F (physical t)) (point t)).re)) :
    δ - B * ε ≤ law.mean (fun t => weight t *
      (taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
        (left (physical t)) (right (physical t)) (mark (physical t))
        (centers (externalNetIndex F centers hnet (physical t))) (point t)).re) := by
  exact externalNet_selected_score_lower law
    (inheritedTaggedQuotientFamily D Fmark φ hφ W Dref Fref Q K left right mark F)
    (inheritedTaggedQuotientCenters D Fmark φ hφ W Dref Fref Q K left right mark centers)
    (externalNetIndex F centers hnet) physical (fun t => (physical t, point t)) weight
    hB hweight
    (inheritedTaggedQuotient_original_index_approx D Fmark φ hφ W Dref Fref Q K
      left right mark F centers hnet hF hcenters) hscore

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks

namespace OAI

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

noncomputable def refilteredFrozenScore (z : P.productive) : ℝ :=
  (𝔼 u ∈ (P.chart z).slice.integerPoints, weight ((P.chart z).physical u) *
    P.refilteredFrozenObservable A Fmark φ W Dref left right ((P.chart z).physical u)
      (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)).re

include hσ1 H hH hchart hsmall hp hrecovery in

theorem refilteredQuotientCandidate_score_eq_frozen (z : P.productive) :
    ((middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF).score
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight = P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z := by
  unfold AllocatedExternalLocalCandidate.score refilteredFrozenScore
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
  exact hr

omit [PseudoMetricSpace Fref.Space] in

theorem refilteredFrozenScore_ge_of_error {Bweight ε : ℝ}
    (hBweight : 0 ≤ Bweight) (hε : 0 ≤ ε)
    (hweight : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      ‖weight ((P.chart z).physical u)‖ ≤ Bweight)
    (herror : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      ‖observable ((P.chart z).physical u) ((P.candidate z).value u) -
        P.refilteredFrozenObservable A Fmark φ W Dref left right ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)‖ ≤ ε)
    (z : P.productive) :
    scoreThreshold - Bweight * ε ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z := by
  have herr := complex_expect_error_le (P.chart z).slice.integerPoints
    (fun u => weight ((P.chart z).physical u) *
      observable ((P.chart z).physical u) ((P.candidate z).value u))
    (fun u => weight ((P.chart z).physical u) *
      P.refilteredFrozenObservable A Fmark φ W Dref left right ((P.chart z).physical u)
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit))
    (mul_nonneg hBweight hε) (by
      intro u hu
      rw [← mul_sub, norm_mul]
      exact mul_le_mul (hweight z u hu) (herror z u hu) (norm_nonneg _) hBweight)
  have hre := (Complex.re_le_norm _).trans herr
  rw [Complex.sub_re] at hre
  have hs := P.score z
  unfold AllocatedExternalLocalCandidate.score at hs
  unfold refilteredFrozenScore
  linarith

variable {frozenScoreThreshold : ℝ}
    (hscore : ∀ z : P.productive, frozenScoreThreshold ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z)

noncomputable def refilteredQuotientScoredProblem :
    AllocatedExternalCandidateProblem (E := E) A Q QF.filtration
      (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit QF hQF markedMiddle)
      (P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K)
      weight cost massThreshold frozenScoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (middle z).topQuotient Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF
  score z := by
    rw [P.refilteredQuotientCandidate_score_eq_frozen A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle hrecovery z]
    exact hscore z

variable (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked)

omit [PseudoMetricSpace Fref.Space] in
include hmarkFactor in

theorem refilteredScoredAssembly_mark_on_slice
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
  rw [heval, ← hmarkFactor z u hu]
  simp only [map_mul]
  rw [D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    D.refiltered_mark_realification_commutes Fmark φ hφ W Dref Fref,
    hglobal, (middle z).mark_on_slice u hu]

include hmarkFactor in

theorem conclusion_of_refilteredQuotientScored
    (db : Basis ι ℚ L) (dw : ι → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (db '' {i | j ≤ dw i}))
    (fb : Basis κ ℚ M) (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (fb '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis db dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.refilteredQuotientScoredProblem A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle hrecovery hscore).Conclusion
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
        P.refilteredScoredAssembly_mark_on_slice A Fmark φ hφ W Dref hDref Fref left right
          markedMiddle middle hmarkFactor ambientMiddle hmarkedMiddle z u hu)
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

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

noncomputable def refilteredLocalCoordinates (z : P.productive) :
    (D.filtration.realification.adaptedPolynomialFiltration
      (fun _ : (P.chart z).Variables => 1)).Group :=
  D.filtration.realification.polynomialOrbitCoordinates _
    (D.includedRefilteredOrbit W Dref hDref _ (middle z).orbit)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in

theorem refilteredLocalCoordinates_value (z : P.productive)
    (u : (P.chart z).Variables → ℤ) :
    D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
      (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z) =
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
  simpa only [refilteredLocalCoordinates,
    NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    polynomialOrbitRealEval_integer] using
      D.includedRefilteredOrbit_realEval W Dref hDref (fun _ => 1) (middle z).orbit
        (fun i => (u i : ℝ))

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hfactor : ∀ z : P.productive,
      localLeft z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle z * localRight z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)
    (hcoset : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1)
        (fun i => (u i : ℝ))
        ((D.filtration.filteredRealPolynomialSection Fmark.filtration (fun _ => 1)
          sectionMap hSectionFilt (localRightMark z))⁻¹ * localRight z)) : D.Space) =
        QuotientGroup.mk kR)
    (tests : (X → ℤ) → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hsection hkE hkR hfactor hleft hright hcoset htests hσ1 H hH hchart hsmall hp in

theorem refilteredFrozenObservable_error_of_native_freezing
    {Lip ε : ℝ} (hε : 0 ≤ ε)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hslow :
      letI := rightMetricSpace
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
        dist (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
          (localLeft z * (D.filtration.filteredRealPolynomialSection Fmark.filtration
            (fun _ => 1) sectionMap hSectionFilt (localLeftMark z))⁻¹)) kE ≤ ε)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    ‖observable ((P.chart z).physical u) ((P.candidate z).value u) -
      P.refilteredFrozenObservable A Fmark φ W Dref
        (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE)
        (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)
        ((P.chart z).physical u)
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)‖ ≤
      Lip * ε := by
  let test := (tests ((P.chart z).physical u)).withOrbit (P.candidate z).orbit
  have he := test.observable_frozenMarked_outerOrbits Fmark.filtration φ sectionMap hSectionFilt
    hsection (D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (localLeft z)
    (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
    (localRight z) (hfactor z) (localLeftMark z) (localRightMark z)
    (fullTaggedVariableWeight (X := X) J) leftMark rightMark kE kR hkE hkR (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hleft z u hu) (hright z u hu) (hcoset z u hu)
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  have hbound := he.trans ((mul_le_mul_of_nonneg_left (hslow z u hu)
    (NNReal.coe_nonneg test.lipBound)).trans
      (mul_le_mul_of_nonneg_right (hlip ((P.chart z).physical u)) hε))
  simpa only [test, RationalFilteredNilmanifold.Niltest.withOrbit, htests,
    NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle,
    polynomialOrbitRealEval_integer, AllocatedExternalLocalCandidate.value,
    refilteredFrozenObservable, htags] using hbound

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
include hsection hkE hkR hfactor hleft hright in

theorem refilteredFrozen_mark_on_slice
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localRight z) = localRightMark z)
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE) *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J) ((P.chart z).chartValues u) marked := by
  have he := D.filtration.frozenMarkedOuter_product_mark_eq Fmark.filtration φ hφ
    sectionMap hSectionFilt hsection (fun _ : (P.chart z).Variables => 1)
    (D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (localLeft z)
    (P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
    (localRight z) (hfactor z) (localLeftMark z) (localRightMark z)
    (hprojLeft z) (hprojRight z) (fullTaggedVariableWeight (X := X) J) leftMark rightMark kE kR hkE hkR
    (fun i => (u i : ℝ)) (fun i => ((P.chart z).chartValues u i : ℝ))
    (hleft z u hu) (hright z u hu)
  simp only [NilpotentLieFiltration.nativeFrozenMarkedOrbitCoordinates_realValue,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle,
    polynomialOrbitRealEval_integer] at he
  exact he.trans ((P.candidate z).mark_on_slice u hu)

include hsection hkE hkR hfactor hleft hright hcoset htests hσ1 H hH hchart hsmall hp in

theorem refilteredFrozenScore_ge_of_native_freezing
    {Bweight Lip ε : ℝ} (hBweight : 0 ≤ Bweight) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      ‖weight ((P.chart z).physical u)‖ ≤ Bweight)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hslow :
      letI := rightMetricSpace
        (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ)
      ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
        dist (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
          (localLeft z * (D.filtration.filteredRealPolynomialSection Fmark.filtration
            (fun _ => 1) sectionMap hSectionFilt (localLeftMark z))⁻¹)) kE ≤ ε)
    (z : P.productive) :
    scoreThreshold - Bweight * (Lip * ε) ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref
        (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE)
        (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)
        markedMiddle middle z := by
  apply P.refilteredFrozenScore_ge_of_error A Fmark φ hφ W Dref Fref
    (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE)
    (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)
    markedMiddle middle hBweight (mul_nonneg hLip hε) hweight ?_ z
  intro z u hu
  exact P.refilteredFrozenObservable_error_of_native_freezing A Fmark φ hφ W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt hsection leftMark rightMark kE kR hkE hkR
    localLeft localRight localLeftMark localRightMark hfactor hleft hright hcoset
    tests htests hσ1 H hH hchart hsmall hp hε hlip hslow z u hu

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

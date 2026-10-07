import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateNativeFrozenScore

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

theorem exists_marked_topQuotientOrbit_lift_externalFamily_on
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace E.Space]
    {A : Type*} (K : ℝ≥0) (observable : A → D.RealGroup → ℂ) (allowed : A → Prop)
    (hrecovery : ∀ a, allowed a → ∀ source,
      positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K
        (observable a) (D.markedTopQuotientDiagram E φ Q source).2
          (D.markedTopQuotientDiagram E φ Q source).1 = observable a source)
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ a, allowed a → ∀ z : σ → ℝ,
        positiveImageSlice (D.markedTopQuotientDiagram E φ Q) K (observable a)
          (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked))
          (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q)) =
        observable a (D.filtration.realification.polynomialOrbitRealEval w z g) := by
  obtain ⟨g, hg, hm, hdiagram⟩ :=
    D.exists_marked_topQuotientOrbit_lift_diagram E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro a ha z
  have h := hrecovery a ha (D.filtration.realification.polynomialOrbitRealEval w z g)
  rw [hdiagram z] at h
  exact h

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem sides_pos (k : LayerSamplerVariables G I n B) : 0 < A.sides k := by
  cases k with
  | inl g => exact S.positive
  | inr j => exact allocatedPrincipalSides_pos B U b S j

include A in

theorem trimMargin_proper (x : X) : 2 * spatialTrimMargin τ N x < N x := by
  obtain ⟨base, hbase⟩ := A.bases_nonempty
  obtain ⟨a, ha, _⟩ := Finset.mem_image.mp hbase
  have hx := (mem_integerBox _ _).mp ha x
  omega

theorem physical_mem_integerBox (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) :
    A.physical z site ∈ integerBox N := by
  have hroot : (∑ k, |(site.val k : ℝ)|) ≤
      allocatedExternalCandidateRootBudget B U b S := by
    rw [allocatedExternalCandidateRootBudget_eq]
    exact allocatedParameterSite_sum_bound B U b S site
  exact jointIntegerPhysicalSite_mem_box site.val N (spatialTrimMargin τ N)
    (fun x => (A.trimMargin_proper x).le) A.widths
    (narrowTrimmedSpatialWidths_fit
      (allocatedExternalCandidateRootBudget_nonneg B U b S) A.trim_pos hξ1
      site.val hroot N A.size_pos) z

end AllocatedExternalCandidateSampler

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

namespace AllocatedExternalLocalChart

variable {A} {chartCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A chartCost)

theorem physical_mem_integerBox (hξ1 : ξ ≤ 1) (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) : C.physical u ∈ integerBox N := by
  rw [C.physical_eq_sampler u (C.slice.integerPoints_subset_integerBox hu)]
  exact A.physical_mem_integerBox hξ1 C.path _

end AllocatedExternalLocalChart

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
    (allowed : (X → ℤ) → Prop)
    (hphysical : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      allowed ((P.chart z).physical u))
    (hrecovery : ∀ x, allowed x → ∀ source, positiveImageSlice (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right x)
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
      (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        P.refilteredFrozenObservable A Fmark φ W Dref left right x source)

include hσ1 H hH hchart hsmall hp hphysical hrecovery in

theorem refilteredQuotientCandidate_score_eq_frozen_on (z : P.productive) :
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
  have hr := hrecovery ((P.chart z).physical u) (hphysical z u hu)
    (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)
  simp only [RationalFilteredNilmanifold.markedTopQuotientDiagram, hmark] at hr
  exact hr

variable {frozenScoreThreshold : ℝ}
    (hscore : ∀ z : P.productive, frozenScoreThreshold ≤
      P.refilteredFrozenScore A Fmark φ hφ W Dref Fref left right markedMiddle middle z)

noncomputable def refilteredQuotientScoredProblem_on :
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
    rw [P.refilteredQuotientCandidate_score_eq_frozen_on A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle allowed hphysical hrecovery z]
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

include hmarkFactor in

theorem conclusion_of_refilteredQuotientScored_on
    (db : Basis ι ℚ L) (dw : ι → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (db '' {i | j ≤ dw i}))
    (fb : Basis κ ℚ M) (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (fb '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis db dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    {outputCost outputMass outputScore : ℝ}
    (lower : (P.refilteredQuotientScoredProblem_on A Fmark φ hφ W Dref hDref Fref hFref
      Q hQ QF hQF left right markedMiddle K hσ1 H hH hchart hsmall hp middle allowed hphysical hrecovery hscore).Conclusion
      outputCost outputMass outputScore) :
    Nonempty (P.Conclusion outputCost outputMass outputScore) := by
  have hcompat : Dref.topQuotientMarkedOrbit Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF lower.ambient =
      Fref.topQuotientOrbit QF hQF markedMiddle := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact lower.marked
  obtain ⟨ambientMiddle, _, hmarkedMiddle, hevalMiddle⟩ :=
    Dref.exists_marked_topQuotientOrbit_lift_externalFamily_on Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref) Q hQ QF hQF K
      (P.refilteredFrozenObservable A Fmark φ W Dref left right) allowed hrecovery
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
  have hr := hevalMiddle ((P.chart zp).physical u) (hphysical zp u huOriginal)
    (fun i => ((P.chart zp).chartValues u i : ℝ))
  simp only [polynomialOrbitRealEval_integer] at hr
  simpa only [refilteredQuotientObservable, refilteredFrozenObservable, ← htags] using hr

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

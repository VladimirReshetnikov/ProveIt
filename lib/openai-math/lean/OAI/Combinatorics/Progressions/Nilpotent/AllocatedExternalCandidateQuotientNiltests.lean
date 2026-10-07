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
    [PseudoMetricSpace Fref.Space]
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

theorem exists_refilteredQuotient_niltests
    {σtest : Type*} (w : σtest → ℕ) {pGeo : ℝ}
    (hGeo : Q.GeometryComplexityLE pGeo) (hK : (K : ℝ) ≤ Real.exp pGeo)
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1) :
    letI := Q.metricSpace
    ∃ tests : (X → ℤ) → Q.Niltest w, ∀ x,
      (tests x).orbit = 1 ∧
      (tests x).observable =
        P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K x ∧
      (tests x).normBound = 1 ∧ (tests x).lipBound = K ∧
      (tests x).UnitIntervalValued ∧ (tests x).ComplexityLE (pGeo + 3) ∧
      ∀ (orbit : Q.filtration.realification.PolynomialOrbit w) u,
        ((tests x).withOrbit orbit).eval u =
          P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K x
            (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval w u orbit)) := by
  let := Q.metricSpace
  let f := P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q left right markedMiddle K
  have hLip (x : X → ℤ) : LipschitzWith K (f x) := by
    apply positiveImageSlice_lipschitz
    intro source
    exact (hpositive x _).2.1
  have hcap (x : X → ℤ) (y : Q.Space) : ‖f x y‖ ≤ 1 :=
    positiveImageExtension_norm_le_one _ _ _ _
  have hunit (x : X → ℤ) (y : Q.Space) :
      (f x y).im = 0 ∧ 0 ≤ (f x y).re ∧ (f x y).re ≤ 1 :=
    positiveImageExtension_unit_interval _ _ _ _
  let tests (x : X → ℤ) : Q.Niltest w :=
    Q.externalNetNiltest (f x) K (hcap x) (hLip x) 1
  refine ⟨tests, fun x => ⟨rfl, rfl, rfl, rfl, hunit x, ?_, fun _ _ => rfl⟩⟩
  exact Q.externalNetNiltest_complexity (f x) K (hcap x) (hLip x) 1
    ((Nat.cast_nonneg _).trans hGeo.1) hGeo hK

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

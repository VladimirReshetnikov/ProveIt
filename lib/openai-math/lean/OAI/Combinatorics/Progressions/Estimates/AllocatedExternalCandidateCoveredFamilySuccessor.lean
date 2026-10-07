/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateResetSuccessor
import OAI.Combinatorics.Progressions.Nilpotent.AllocatedExternalCandidateQuotientNiltests
import OAI.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion

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

namespace AllocatedExternalCandidateSampler

def FamilyGlobalizationAt
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {degree d f : ℕ} (D : RationalFilteredNilmanifold L degree d)
    (Fmark : RationalFilteredNilmanifold M degree f) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (ℓ : ℝ≥0) (netExponent : ℕ) (p outputCost : ℝ) : Prop :=
  (∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j) →
  (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
  D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
  (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
  (ℓ : ℝ) ≤ Real.exp p →
  (∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x)) →
  (∀ x y, (observable x y).im = 0 ∧ 0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1) →
  (∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
    (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + netExponent) ^ netExponent) ∧
    ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
      ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η) →
  (∀ x, ‖weight x‖ ≤ Real.exp p) →
  ∀ P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
    observable weight p (Real.exp (-p)) (Real.exp (-p)),
  Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost)))

theorem DegreeGlobalizationAt.family
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {degree d f netExponent : ℕ} {p outputCost : ℝ} {weight : (X → ℤ) → ℂ}
    (rule : A.DegreeGlobalizationAt (E := E) weight degree netExponent p outputCost)
    (D : RationalFilteredNilmanifold L degree d)
    (Fmark : RationalFilteredNilmanifold M degree f) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (ℓ : ℝ≥0) :
    A.FamilyGlobalizationAt (E := E) D Fmark φ marked observable weight ℓ netExponent p outputCost := by
  intro hφ hsurj hD hF hmap
  exact rule D Fmark φ hφ hsurj hD hF hmap marked observable ℓ

theorem familyGlobalizationAt_zero
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d f : ℕ} (D : RationalFilteredNilmanifold L 0 d)
    (Fmark : RationalFilteredNilmanifold M 0 f) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (ℓ : ℝ≥0) (netExponent : ℕ) (p : ℝ) :
    A.FamilyGlobalizationAt (E := E) D Fmark φ marked observable weight ℓ netExponent p p := by
  intro hφ hsurj hD hF hmap hℓ hLip hpositive hnet hweight P
  exact P.conclusion_stepZero A D Fmark.filtration φ marked observable weight

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

universe uL uM uX

namespace Erdos3.RationalFilteredNilmanifold

noncomputable def refilteredQuotientNetExponent (s r e : ℕ) : ℕ :=
  Classical.choose (exists_uniform_controlled_native_external_nets.{uL, uM, uX, 0, uL, uL} (s + 1) (s + 1) r e)

theorem refilteredQuotientNetExponent_ge_two (s r e : ℕ) :
    2 ≤ refilteredQuotientNetExponent.{uL, uM, uX} s r e :=
  (Classical.choose_spec (exists_uniform_controlled_native_external_nets.{uL, uM, uX, 0, uL, uL}
    (s + 1) (s + 1) r e)).1

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G : Type*} {X : Type uX} [Fintype G] [Fintype X]
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

variable {L : Type uL} {M : Type uM} {ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
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
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]

theorem exists_refilteredQuotient_uniform_nets
    (r e : ℕ) (cap ℓ : ℝ≥0) {p dictBound : ℝ} {rightDenominator : ℕ}
    (rightDictionary : D.NativeGridRightDictionary rightDenominator dictBound)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hF : Fref.GeometryComplexityLE p)
    (hcap : 1 ≤ cap) (hcapBound : (cap : ℝ) ≤ Real.exp ((p + 2) ^ r))
    (hK : (K : ℝ) ≤ Real.exp p) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hcount : (rightDictionary.count : ℝ) ≤ Real.exp p)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ cap)
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid rightDenominator)
    (hrecovery :
      letI := Q.metricSpace
      letI := Fref.metricSpace
      let diagram := Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
      ∀ x ∈ integerBox N, ∀ a r₀ : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ cap) →
        (D.basis.baseChange ℝ).equivFun r₀.coord ∈
          realDenominatorGrid rightDictionary.denominator →
        let frozen := fun source : Dref.RealGroup => observable x (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl source * r₀))
        ∀ source, positiveImageSlice diagram K frozen
          (diagram source).2 (diagram source).1 = frozen source) :
    letI := Q.metricSpace
    letI := Fref.metricSpace
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) +
        RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e) ^
        RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e) ∧
      ∃ centers : Fin n → Q.Space → ℂ,
        (∀ i, LipschitzWith K (centers i)) ∧
        (∀ i y, (centers i y).im = 0 ∧ 0 ≤ (centers i y).re ∧ (centers i y).re ≤ 1) ∧
        (∀ i y, ‖centers i y‖ ≤ 1) ∧
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
            left right markedMiddle K x y - centers i y‖ ≤ ε := by
  let := Q.metricSpace
  let := Fref.metricSpace
  let sites := {x : X → ℤ // x ∈ integerBox N}
  let family : sites → D.Space → ℂ := fun x => observable x.val
  let inclusion : Dref.RealGroup → D.RealGroup :=
    realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl
  let diagram := Dref.markedTopQuotientDiagram Fref
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
  let leftAt (x : sites) : coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) cap :=
    ⟨D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x.val) left, hleft x.val x.property⟩
  let rightAt (x : sites) : D.RealGroup :=
    D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
      (P.physicalIntegerPoint x.val) right
  obtain ⟨label, hlabel⟩ := rightDictionary.labeling rightAt
    (fun x => hright x.val x.property)
  have hmember η hη hη1 := hnet η hη hη1
  have hmember' : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → sites, ∀ x, ∃ i, ∀ y, ‖family x y - family (oc i) y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨n, hn, oc, hoc⟩ := hmember η hη hη1
    exact ⟨n, hn, oc, fun x => hoc x.val x.property⟩
  have hrec (x : sites) (a : coordinateBox
      (hnil := D.filtration.realification.lowerCentralSeries_eq_bot) (D.basis.baseChange ℝ) cap)
      (j : Fin rightDictionary.count) :=
    exists_lipschitz_reconstruction_of_positiveImageSlice_eq diagram K
      (fun source => family x (QuotientGroup.mk (a.val * inclusion source * rightDictionary.representative j)))
      (fun _ => (hpositive x.val x.property _).2.1)
      (hrecovery x.val x.property a.val (rightDictionary.representative j) a.property
        (rightDictionary.representative_bounds j).2)
  have hfixed := (Classical.choose_spec
    (RationalFilteredNilmanifold.exists_uniform_controlled_native_external_nets.{uL, uM, uX, 0, uL, uL}
      (s + 1) (s + 1) r e)).2 D Fref cap K ℓ hp hD hF hcap hcapBound hK hℓ
    (by simpa only [Fintype.card_fin] using hcount)
    family inclusion rightDictionary.representative diagram
    (fun x => hLip x.val x.property) (fun x y => hpositive x.val x.property y) hmember' hrec
  dsimp only at hfixed ⊢
  intro ε hε hε1
  obtain ⟨n, hn, centers, hcentersLip, hunit, hnorm, _, hcover⟩ := hfixed ε hε hε1
  refine ⟨n, hn, centers, hcentersLip, hunit, hnorm, ?_⟩
  intro x hx
  let site : sites := ⟨x, hx⟩
  have hfrozen : P.refilteredFrozenObservable A Fmark φ W Dref left right x =
      fun source => family site (QuotientGroup.mk
        ((leftAt site).val * inclusion source * rightDictionary.representative (label site))) := by
    funext source
    exact congrArg (observable x) ((hlabel site).2 ((leftAt site).val * inclusion source))
  obtain ⟨i, hi⟩ := hcover site (leftAt site) (label site)
    (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval
      (fullTaggedVariableWeight (X := X) J) (P.physicalIntegerPoint x) markedMiddle))
  refine ⟨i, ?_⟩
  simpa only [refilteredQuotientObservable, hfrozen] using hi

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

universe uL uM uX

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G : Type*} {X : Type uX} [Fintype G] [Fintype X]
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

variable {L : Type uL} {M : Type uM} {ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
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
    [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))]

variable (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (K : ℝ≥0)

variable
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
    [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]

theorem exists_refilteredQuotient_uniform_member_nets
    (r e : ℕ) (cap ℓ : ℝ≥0) {p dictBound : ℝ} {rightDenominator : ℕ}
    (rightDictionary : D.NativeGridRightDictionary rightDenominator dictBound)
    (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hF : Fref.GeometryComplexityLE p)
    (hcap : 1 ≤ cap) (hcapBound : (cap : ℝ) ≤ Real.exp ((p + 2) ^ r))
    (hK : (K : ℝ) ≤ Real.exp p) (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hcount : (rightDictionary.count : ℝ) ≤ Real.exp p)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ cap)
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid rightDenominator)
    (hrecovery :
      letI := Q.metricSpace
      letI := Fref.metricSpace
      let diagram := Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
      ∀ x ∈ integerBox N, ∀ a r₀ : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ cap) →
        (D.basis.baseChange ℝ).equivFun r₀.coord ∈
          realDenominatorGrid rightDictionary.denominator →
        let frozen := fun source : Dref.RealGroup => observable x (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl source * r₀))
        ∀ source, positiveImageSlice diagram K frozen
          (diagram source).2 (diagram source).1 = frozen source) :
    letI := Q.metricSpace
    letI := Fref.metricSpace
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / ε) +
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e + 2 : ℕ)) ^
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e + 2)) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
            left right markedMiddle K x y -
            P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
              left right markedMiddle K (oc i).val y‖ ≤ ε := by
  let := Q.metricSpace
  let := Fref.metricSpace
  let sites := {x : X → ℤ // x ∈ integerBox N}
  have hzero : (fun _ : X => (0 : ℤ)) ∈ integerBox N := by
    apply (mem_integerBox N _).mpr
    intro x
    exact ⟨le_rfl, by exact_mod_cast A.size_pos x⟩
  let : Nonempty sites := ⟨⟨fun _ => 0, hzero⟩⟩
  let family : sites → Q.Space → ℂ := fun x =>
    P.refilteredQuotientObservable A Fmark φ hφ W Dref Fref Q
      left right markedMiddle K x.val
  have hfixed := P.exists_refilteredQuotient_uniform_nets A Fmark φ hφ W Dref Fref Q
    left right markedMiddle K r e cap ℓ rightDictionary hp hD hF hcap hcapBound
    hK hℓ hcount hLip hpositive hnet hleft hright hrecovery
  have hfunctions : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) +
        RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e) ^
        RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e) ∧
      ∃ centers : Fin n → Q.Space → ℂ, ∀ x, ∃ i, ∀ y,
        ‖family x y - centers i y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨n, hn, centers, _, _, _, hcover⟩ := hfixed η hη hη1
    exact ⟨n, hn, centers, fun x => hcover x.val x.property⟩
  intro ε hε hε1
  obtain ⟨n, hn, oc, hoc⟩ := exists_uniform_family_member_net_of_polynomial_log
    family hp (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{uL, uM, uX} s r e)
    hfunctions ε hε hε1
  exact ⟨n, hn, oc, fun x hx => hoc ⟨x, hx⟩⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

universe u uX

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G : Type*} {X : Type uX} [Fintype G] [Fintype X]
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
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_covered_refilteredQuotient_uniform_member_nets
    (k e : ℕ) {p coverCost pNext dictBound : ℝ} {rightDenominator : ℕ}
    (rightDictionary : D.NativeGridRightDictionary rightDenominator dictBound)
    (covered : RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram
      D Fmark φ hφ W k rightDictionary.denominator p coverCost)
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (markedMiddle : covered.Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (ℓ : ℝ≥0) (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p)
    (hpNext : p ≤ pNext) (hcoverNext : coverCost ≤ pNext)
    (hℓ : (ℓ : ℝ) ≤ Real.exp p)
    (hcount : (rightDictionary.count : ℝ) ≤ Real.exp pNext)
    (hLip : ∀ x ∈ integerBox N, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x ∈ integerBox N, ∀ y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hnet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((p + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hleft : ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) left).coord i| ≤ Real.exp ((p + 2) ^ k))
    (hright : ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          (P.physicalIntegerPoint x) right).coord ∈ realDenominatorGrid rightDenominator) :
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
    let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pNext + Real.log (1 / ε) +
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{u, u, uX} s k e + 2 : ℕ)) ^
        (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{u, u, uX} s k e + 2)) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖P.refilteredQuotientObservable A Fmark φ hφ W covered.Dref covered.Fref covered.Q
            left right markedMiddle K x y -
            P.refilteredQuotientObservable A Fmark φ hφ W covered.Dref covered.Fref covered.Q
              left right markedMiddle K (oc i).val y‖ ≤ ε := by
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
  let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
  let cap : ℝ≥0 := ⟨Real.exp ((p + 2) ^ k), (Real.exp_pos _).le⟩
  have hnetNext : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pNext + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η := by
    intro η hη hη1
    obtain ⟨n, hn, oc, hoc⟩ := hnet η hη hη1
    refine ⟨n, hn.trans (Real.exp_le_exp.mpr ?_), oc, hoc⟩
    have hlog : 0 ≤ Real.log (1 / η) :=
      Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa using hη1))
    exact pow_le_pow_left₀ (by positivity) (by linarith) e
  refine P.exists_refilteredQuotient_uniform_member_nets A Fmark φ hφ W
    covered.Dref covered.Fref covered.Q left right markedMiddle K k e cap ℓ
    rightDictionary (hp.trans hpNext) (hD.mono D hpNext)
    (covered.Fref_geometry.mono covered.Fref hcoverNext) ?_ ?_ ?_
    (hℓ.trans (Real.exp_le_exp.mpr hpNext)) hcount hLip hpositive hnetNext hleft hright ?_
  · change (1 : ℝ) ≤ Real.exp ((p + 2) ^ k)
    exact Real.one_le_exp_iff.mpr (pow_nonneg (by linarith) _)
  · exact Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2) (by linarith) k)
  · exact Real.exp_le_exp.mpr (covered.pCover_le.trans hcoverNext)
  · dsimp only
    intro x hx a r ha hr
    exact covered.recovery a r ha hr (observable x) ℓ hℓ (hLip x hx) (hpositive x hx)

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

variable {L M κ : Type} [LieRing L] [LieAlgebra ℚ L]
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
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {inputDenominator k e : ℕ} {pGeo geoCost dictBound : ℝ}
    (rightDictionary : D.NativeGridRightDictionary inputDenominator dictBound)
    (covered : RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram
      D Fmark φ hφ W k rightDictionary.denominator pGeo geoCost)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include covered htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_covered_nativeReset_degreeRule
    {Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt denominator
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hpGeo : 0 ≤ pGeo) (hDGeo : D.GeometryComplexityLE pGeo)
    (hpGeoInput : p ≤ pGeo)
    (hpGeoRec : pGeo ≤ finiteFreezingRecursiveParameter C p)
    (hcoveredRec : geoCost ≤ finiteFreezingRecursiveParameter C p)
    (hℓ : (ℓ : ℝ) ≤ Real.exp pGeo)
    (hRightCount : (rightDictionary.count : ℝ) ≤ Real.exp (finiteFreezingRecursiveParameter C p))
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hfullLeft : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1))).coord i| ≤
        Real.exp ((pGeo + 2) ^ k))
    (hfullRight : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2))).coord ∈
        realDenominatorGrid inputDenominator)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s k e + 2)
      (finiteFreezingRecursiveParameter C p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
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
  let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
  let left (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
      sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1)
  let right (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
      sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2)
  have hrecovery (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    (P₀.withKeep keep hkeep).refilteredFrozenObservable_recovery_of_coveredDiagram
      A Fmark φ hφ W rightDictionary covered (left ij) (right ij) ℓ hℓ
      (fun x _ => hOriginalLip x) (fun x _ => hpositive x) (hfullLeft ij) (hfullRight ij)
  apply P₀.conclusion_of_globalNativeReset_dictionary_successor Fmark φ hφ keep hkeep W
    covered.Dref covered.Dref_filtration covered.Fref covered.Fref_filtration
    sectionMap hSectionFilt c ν hF factors reset tests htests hσ1 H hH hchart hsmall hp
    covered.Q covered.Q_filtration covered.Fquot covered.Fquot_filtration K
    C hp0 hC dictionary hslowMark hgrid hdensity hfloor hBweight hBobs hLip hweight hnorm hlip
    hweightCap hobsCap hlipCap hscoreInput hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount
    hmassLog hmassInput hsection dw hdb hW hsurj hξ1 hrecovery
  intro ij lowerProblem
  have hnet := (P₀.withKeep keep hkeep).exists_covered_refilteredQuotient_uniform_member_nets
    A Fmark φ hφ W k e rightDictionary covered (left ij) (right ij)
    (factors.markedMiddleOn covered.Fref covered.Fref_filtration) ℓ hpGeo hDGeo hpGeoRec hcoveredRec
    hℓ hRightCount (fun x _ => hOriginalLip x) (fun x _ => hpositive x) hOriginalNet
    (hfullLeft ij) (hfullRight ij)
  let lowerObservable := (P₀.withKeep keep hkeep).refilteredQuotientObservable
    A Fmark φ hφ W covered.Dref covered.Fref covered.Q (left ij) (right ij)
    (factors.markedMiddleOn covered.Fref covered.Fref_filtration) K
  have hLowerLip (x : X → ℤ) : LipschitzWith K (lowerObservable x) := by
    apply positiveImageSlice_lipschitz
    intro source
    exact (hpositive x _).2.1
  have hLowerPositive (x : X → ℤ) (y : covered.Q.Space) :
      (lowerObservable x y).im = 0 ∧ 0 ≤ (lowerObservable x y).re ∧
        (lowerObservable x y).re ≤ 1 :=
    positiveImageExtension_unit_interval _ _ _ _
  exact lowerIH covered.Q covered.Fquot
    (covered.Dref.topQuotientMarkedMap covered.Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W covered.Dref covered.Dref_filtration
        covered.Fref covered.Fref_filtration))
    covered.lower_mark_filtered covered.lower_mark_strong
    (covered.Q_geometry.mono covered.Q hcoveredRec)
    (covered.Fquot_geometry.mono covered.Fquot hcoveredRec)
    (fun i j => (covered.lower_mark_height i j).trans hcoveredRec)
    (covered.Fref.topQuotientOrbit covered.Fquot covered.Fquot_filtration
      (factors.markedMiddleOn covered.Fref covered.Fref_filtration))
    lowerObservable K (Real.exp_le_exp.mpr (covered.pCover_le.trans hcoveredRec))
    hLowerLip hLowerPositive hnet
    (fun x => (hweight x).trans (hweightCap.trans
      (Real.exp_le_exp.mpr (hpGeoInput.trans hpGeoRec)))) lowerProblem

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

variable {L M κ : Type} [LieRing L] [LieAlgebra ℚ L]
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
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {inputDenominator k e : ℕ} {pGeo geoCost dictBound : ℝ}
    (rightDictionary : D.NativeGridRightDictionary inputDenominator dictBound)
    (covered : RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram
      D Fmark φ hφ W k rightDictionary.denominator pGeo geoCost)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include covered htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_covered_nativeReset_familyRule
    {Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt denominator
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hpGeo : 0 ≤ pGeo) (hDGeo : D.GeometryComplexityLE pGeo)
    (hpGeoInput : p ≤ pGeo)
    (hpGeoRec : pGeo ≤ finiteFreezingRecursiveParameter C p)
    (hcoveredRec : geoCost ≤ finiteFreezingRecursiveParameter C p)
    (hℓ : (ℓ : ℝ) ≤ Real.exp pGeo)
    (hRightCount : (rightDictionary.count : ℝ) ≤ Real.exp (finiteFreezingRecursiveParameter C p))
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hfullLeft : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1))).coord i| ≤
        Real.exp ((pGeo + 2) ^ k))
    (hfullRight : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2))).coord ∈
        realDenominatorGrid inputDenominator)
    (outputCost : ℝ)
    (lowerIH :
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
      let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
      ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
        A.FamilyGlobalizationAt (E := E) covered.Q covered.Fquot
          (covered.Dref.topQuotientMarkedMap covered.Fref
            (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
            (D.refilteredMarkedMap_mem_layer Fmark φ hφ W covered.Dref covered.Dref_filtration
              covered.Fref covered.Fref_filtration))
          (covered.Fref.topQuotientOrbit covered.Fquot covered.Fquot_filtration
            (factors.markedMiddleOn covered.Fref covered.Fref_filtration))
          ((P₀.withKeep keep hkeep).refilteredQuotientObservable
            A Fmark φ hφ W covered.Dref covered.Fref covered.Q
            (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
              sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1))
            (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
              sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2))
            (factors.markedMiddleOn covered.Fref covered.Fref_filtration) K)
          weight K
          (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s k e + 2)
          (finiteFreezingRecursiveParameter C p) outputCost) :
    Nonempty (P₀.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
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
  let K : ℝ≥0 := ⟨Real.exp covered.pCover, (Real.exp_pos _).le⟩
  let left (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
      sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1)
  let right (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
      sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2)
  have hrecovery (ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) :=
    (P₀.withKeep keep hkeep).refilteredFrozenObservable_recovery_of_coveredDiagram
      A Fmark φ hφ W rightDictionary covered (left ij) (right ij) ℓ hℓ
      (fun x _ => hOriginalLip x) (fun x _ => hpositive x) (hfullLeft ij) (hfullRight ij)
  apply P₀.conclusion_of_globalNativeReset_dictionary_successor Fmark φ hφ keep hkeep W
    covered.Dref covered.Dref_filtration covered.Fref covered.Fref_filtration
    sectionMap hSectionFilt c ν hF factors reset tests htests hσ1 H hH hchart hsmall hp
    covered.Q covered.Q_filtration covered.Fquot covered.Fquot_filtration K
    C hp0 hC dictionary hslowMark hgrid hdensity hfloor hBweight hBobs hLip hweight hnorm hlip
    hweightCap hobsCap hlipCap hscoreInput hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount
    hmassLog hmassInput hsection dw hdb hW hsurj hξ1 hrecovery
  intro ij lowerProblem
  have hnet := (P₀.withKeep keep hkeep).exists_covered_refilteredQuotient_uniform_member_nets
    A Fmark φ hφ W k e rightDictionary covered (left ij) (right ij)
    (factors.markedMiddleOn covered.Fref covered.Fref_filtration) ℓ hpGeo hDGeo hpGeoRec hcoveredRec
    hℓ hRightCount (fun x _ => hOriginalLip x) (fun x _ => hpositive x) hOriginalNet
    (hfullLeft ij) (hfullRight ij)
  let lowerObservable := (P₀.withKeep keep hkeep).refilteredQuotientObservable
    A Fmark φ hφ W covered.Dref covered.Fref covered.Q (left ij) (right ij)
    (factors.markedMiddleOn covered.Fref covered.Fref_filtration) K
  have hLowerLip (x : X → ℤ) : LipschitzWith K (lowerObservable x) := by
    apply positiveImageSlice_lipschitz
    intro source
    exact (hpositive x _).2.1
  have hLowerPositive (x : X → ℤ) (y : covered.Q.Space) :
      (lowerObservable x y).im = 0 ∧ 0 ≤ (lowerObservable x y).re ∧
        (lowerObservable x y).re ≤ 1 :=
    positiveImageExtension_unit_interval _ _ _ _
  exact lowerIH ij
    covered.lower_mark_filtered covered.lower_mark_strong
    (covered.Q_geometry.mono covered.Q hcoveredRec)
    (covered.Fquot_geometry.mono covered.Fquot hcoveredRec)
    (fun i j => (covered.lower_mark_height i j).trans hcoveredRec)
    (Real.exp_le_exp.mpr (covered.pCover_le.trans hcoveredRec))
    hLowerLip hLowerPositive hnet
    (fun x => (hweight x).trans (hweightCap.trans
      (Real.exp_le_exp.mpr (hpGeoInput.trans hpGeoRec)))) lowerProblem

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

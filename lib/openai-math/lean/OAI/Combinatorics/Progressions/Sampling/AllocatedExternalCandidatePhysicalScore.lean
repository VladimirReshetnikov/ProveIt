import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

namespace AllocatedExternalCandidateProblem
variable {A D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def physicalIntegerPoint (x : X → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  fullTaggedPhysicalIntegerPoint J poly (fun j => (P.centerLift j).val) x

noncomputable def ambientPhysicalValue
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (x : X → ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fullTaggedVariableWeight J) (P.physicalIntegerPoint x) ambient)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem chartValues_eq_physicalIntegerPoint (z : P.productive)
    (u : (P.chart z).Variables → ℤ) (hu : u ∈ (P.chart z).slice.integerPoints) :
    (P.chart z).chartValues u = P.physicalIntegerPoint ((P.chart z).physical u) :=
  (P.chart z).chartValues_eq_physicalIntegerPoint_of_center
    hσ1 H hH hchart hsmall hp P.centerLift (P.chart_centerLift z) u hu

theorem ambientScore_eq_physical
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ))
    (hpoints : points ⊆ (P.chart z).slice.integerPoints) :
    P.ambientScore ambient z points =
      (𝔼 u ∈ points, weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u)
          (P.ambientPhysicalValue ambient ((P.chart z).physical u))).re := by
  unfold ambientScore ambientPhysicalValue
  apply congrArg Complex.re
  apply Finset.expect_congr rfl
  intro u hu
  rw [P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u (hpoints hu)]

theorem localLaw_ambientPhysicalValue_score
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) :
    ((P.chart z).localLaw.complexMean (fun site => weight (A.physical z.val site) *
      observable (A.physical z.val site)
        (P.ambientPhysicalValue ambient (A.physical z.val site)))).re =
      P.ambientScore ambient z (P.chart z).slice.integerPoints := by
  rw [P.ambientScore_eq_physical hσ1 H hH hchart hsmall hp ambient z _ (Finset.Subset.refl _)]
  have he := (P.chart z).localLaw_complexMean_physical (fun x =>
    weight x * observable x (P.ambientPhysicalValue ambient x))
  rw [P.chart_path z] at he
  exact congrArg Complex.re he

theorem candidate_mark_eq_physical (z : P.productive)
    (u : (P.chart z).Variables → ℤ) (hu : u ∈ (P.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval
        (fun _ : (P.chart z).Variables => 1) u (P.candidate z).orbit) =
      Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (P.physicalIntegerPoint ((P.chart z).physical u)) marked := by
  rw [(P.candidate z).mark_on_slice u hu,
    P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu]

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

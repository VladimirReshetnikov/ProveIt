import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateOptionJointConclusion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

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
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

namespace AllocatedExternalLocalChart

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (g : (F.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group)

theorem globalOrbit_chart_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g) =
      F.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (C.chartValues u i : ℝ))
        ((F.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm g) := by
  rw [F.adaptedPolynomialRealValueHom_weightedChart]
  have heval : (fun i => MvPolynomial.eval (fun j => (u j : ℝ))
      (integerSampledRealChart C.integerChart i)) =
      (fun i => (C.chartValues u i : ℝ)) := by
    funext i
    exact integerSampledRealChart_eval C.integerChart u i
  rw [heval]
  rfl

theorem globalOrbit_chart_integer_values (u : C.Variables → ℤ) :
    F.adaptedPolynomialRealValueHom (fun _ : C.Variables => 1) (fun i => (u i : ℝ))
      (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
        C.integerChart_support g) =
      F.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (C.chartValues u)
        ((F.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm g) := by
  simpa only [polynomialOrbitRealEval_integer] using C.globalOrbit_chart_values F g u

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI

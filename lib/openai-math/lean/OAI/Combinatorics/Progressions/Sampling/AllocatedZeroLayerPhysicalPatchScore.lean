import OAI.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
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
    {V : Type*} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    {f : (X → ℤ) → ℝ} {lam cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold)

namespace AllocatedExternalCandidateProblem

theorem ambientScore_zeroLayer_patch
    (ambient : (polynomialShearFiltration patch.weight s patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ))
    (hpoints : points ⊆ (P.chart z).slice.integerPoints) :
    P.ambientScore ambient z points =
      𝔼 u ∈ points, (f ((P.chart z).physical u) - lam) *
        (patch.ofZeroLayerShearOrbit ambient).value
          (fun i => ((P.chart z).physical u i : ℝ)) := by
  rw [P.ambientScore_eq_physical
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) ambient z points hpoints]
  simp only [ambientPhysicalValue, physicalIntegerPoint,
    fullTaggedPhysicalIntegerPoint_zero_layers,
    Complex.re_expect, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply Finset.expect_congr rfl
  intro u _
  congr 1
  exact (patch.ofZeroLayerShearOrbit_value_integer ambient ((P.chart z).physical u)).symm

theorem Conclusion.zeroLayer_patch_score
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore) (z : out.retained) :
    outputScore ≤ 𝔼 u ∈ (out.slice z).integerPoints,
      (f ((P.chart ⟨z.val, out.subset z.property⟩).physical u) - lam) *
        (patch.ofZeroLayerShearOrbit out.ambient).value
          (fun i => ((P.chart ⟨z.val, out.subset z.property⟩).physical u i : ℝ)) := by
  rw [← P.ambientScore_zeroLayer_patch patch out.ambient
    ⟨z.val, out.subset z.property⟩ (out.slice z).integerPoints (out.inside z)]
  exact out.score z

theorem Conclusion.zeroLayer_siteLaw_score
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore) (z : out.retained) :
    outputScore ≤ (out.siteLaw z).mean (fun site =>
      (f (A.physical z.val site) - lam) *
        (patch.ofZeroLayerShearOrbit out.ambient).value
          (fun i => (A.physical z.val site i : ℝ))) := by
  have he := congrArg Complex.re (out.siteLaw_complexMean_physical z (fun x =>
    (((f x - lam) * (patch.ofZeroLayerShearOrbit out.ambient).value
      (fun i => (x i : ℝ)) : ℝ) : ℂ)))
  simp only [FiniteProbabilityWeights.complexMean_re, Complex.re_expect,
    Complex.ofReal_re] at he
  rw [he]
  exact Conclusion.zeroLayer_patch_score patch P out z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

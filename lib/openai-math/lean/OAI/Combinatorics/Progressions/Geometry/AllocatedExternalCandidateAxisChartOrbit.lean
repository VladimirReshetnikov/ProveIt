import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] polynomialOrbitRealChart realChartSubstitute

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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

include hkeep in

theorem axisPolynomial_freeze (p : MvPolynomial (LayerSamplerVariables G I n B) ℝ) :
    freezePolynomial keep (fun i => (C.axisFixed keep fixed i : ℝ)) p =
      MvPolynomial.aeval (C.axisPolynomial keep fixed)
        (freezePolynomial C.keep (fun i => (C.fixed i : ℝ)) p) := by
  unfold freezePolynomial
  rw [MvPolynomial.comp_aeval_apply]
  apply congrArg (fun f => MvPolynomial.aeval f p)
  funext i
  by_cases hk : keep i
  · have hc := hkeep i hk
    simp [frozenCoordinate, axisPolynomial, hk, hc]
  · by_cases hc : C.keep i
    · simp [frozenCoordinate, axisPolynomial, axisFixed, hk, hc]
    · simp [frozenCoordinate, axisFixed, hk, hc]

theorem restrictAxes_integerSampledRealChart :
    integerSampledRealChart (C.restrictAxes keep hkeep fixed hfixed).integerChart =
      fun i => MvPolynomial.aeval (C.axisPolynomial keep fixed)
        (integerSampledRealChart C.integerChart i) := by
  funext i
  change integerSampledRealChart
      (fun z => freezePolynomial keep (C.axisFixed keep fixed)
        (allocatedRecoveredIntegerFullChart B U b o poly hm C.centerLift
          C.path.1.val C.path.2.val C.sample z)) i =
    MvPolynomial.aeval (C.axisPolynomial keep fixed)
      (integerSampledRealChart
        (fun z => freezePolynomial C.keep C.fixed
          (allocatedRecoveredIntegerFullChart B U b o poly hm C.centerLift
            C.path.1.val C.path.2.val C.sample z)) i)
  rw [integerSampledRealChart_freeze, integerSampledRealChart_freeze]
  exact C.axisPolynomial_freeze keep hkeep fixed _

theorem restrictAxes_polynomialOrbitRealChart
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)
    (g : F.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)) :
    F.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart (C.restrictAxes keep hkeep fixed hfixed).integerChart)
      (C.restrictAxes keep hkeep fixed hfixed).integerChart_support g =
    F.polynomialOrbitRealChart (fun _ : C.Variables => 1) (fun _ => 1)
      (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
      (F.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support g) := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change (F.polynomialOrbitRealChart _ _ _ _ g).log =
    (F.polynomialOrbitRealChart _ _ _ _ (F.polynomialOrbitRealChart _ _ _ _ g)).log
  simp only [polynomialOrbitRealChart_log]
  rw [C.restrictAxes_integerSampledRealChart keep hkeep fixed hfixed]
  exact (realChartSubstitute_comp (integerSampledRealChart C.integerChart)
    (C.axisPolynomial keep fixed) g.log).symm

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI

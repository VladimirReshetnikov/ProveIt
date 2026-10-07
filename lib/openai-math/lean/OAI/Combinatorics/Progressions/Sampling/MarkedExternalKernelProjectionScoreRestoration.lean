import OAI.Combinatorics.Progressions.Estimates.FormalMarkedOrbitTranslation

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ τ Ω J X : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [Fintype Ω] [Fintype J]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

theorem exists_external_kernelProjection_prescribed_marked_orbit
    (tests : X → D.Niltest w) (htests : ∀ x, (tests x).UnitIntervalValued)
    (G : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (hkernel : K ≤ LinearMap.ker φ.toLinearMap)
    (orbit : D.filtration.realification.PolynomialOrbit v)
    (marked : G.realification.PolynomialOrbit v)
    (hmark : map (realLieHomToRat (realificationLieHom φ)).toLinearMap orbit.log = marked.log)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (localLaw : Ω → FiniteProbabilityWeights J)
    (physical : Ω → J → X) (point : Ω → J → τ → ℤ) (weight : Ω → J → ℂ)
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ)
    (hweight : ∀ a ∈ H, ∀ j, ‖weight a j‖ ≤ B)
    (hscore : ∀ a ∈ H, δ ≤ ((localLaw a).complexMean
      (fun j => weight a j * (((tests (physical a j)).kernelProjection K hK).withOrbit orbit).eval
        (point a j))).re) :
    ∃ restored : D.filtration.realification.PolynomialOrbit v,
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap restored.log = marked.log ∧
      ∃ z : D.RealGroup,
        restored = D.filtration.realification.constantGroupOrbit v z * orbit ∧
        z.coord ∈ K.baseChange ℝ ∧
        NilpotentLieBCHGroup.realificationMap
          (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := G.lowerCentralSeries_eq_bot) φ z = 1 ∧
        (∀ x, ((tests x).withOrbit restored).observable = (tests x).observable ∧
          ((tests x).withOrbit restored).normBound = (tests x).normBound ∧
          ((tests x).withOrbit restored).lipBound = (tests x).lipBound ∧
          ((tests x).withOrbit restored).UnitIntervalValued ∧
          ∀ p, ((tests x).withOrbit restored).ComplexityLE p ↔ (tests x).ComplexityLE p) ∧
        ∃ H' : Finset Ω, H' ⊆ H ∧ 0 < outer.mass H' ∧
          δ / (2 * B) * outer.mass H ≤ outer.mass H' ∧
          ∀ a ∈ H', δ / 2 ≤ ((localLaw a).complexMean
            (fun j => weight a j * ((tests (physical a j)).withOrbit restored).eval
              (point a j))).re := by
  obtain ⟨z, hz, _, H', hsub, hpos, hmass, hs⟩ :=
    exists_external_kernelProjection_restored_orbit tests htests K hK orbit
      outer H hH localLaw physical point weight hB hδ hweight hscore
  have hzmark : NilpotentLieBCHGroup.realificationMap
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z = 1 :=
    (NilpotentLieBCHGroup.coord_mem_realificationKernel_iff
      (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z).mp
        (Submodule.baseChange_mono ℝ hkernel hz)
  let restored := D.filtration.realification.constantGroupOrbit v z * orbit
  have hrestored : map (realLieHomToRat (realificationLieHom φ)).toLinearMap
      restored.log = marked.log :=
    (D.filtration.map_log_constantGroupOrbit_mul_of_realificationMap_eq_one
      G φ v orbit z hzmark).trans hmark
  refine ⟨restored, hrestored, z, rfl, hz, hzmark, ?_, H', hsub, hpos, hmass, ?_⟩
  · intro x
    exact ⟨rfl, rfl, rfl, htests x, fun _ => Iff.rfl⟩
  · intro a ha
    exact hs a ha

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI

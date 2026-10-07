import OAI.Combinatorics.Progressions.Linear.SplitCoverProjection

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem largerLattice_cyclicOrbitPoint_dist_le
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (Γ : Subgroup D.filtration.Group)
    (m : ℕ) (hm : 0 < m)
    (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Γ)
    (hout : bchSubgroupCoordinates D.basis Γ ⊆ denominatorGrid m)
    (hΓ : D.lattice ≤ Γ) {w : σ → ℕ}
    (g : D.filtration.realification.PolynomialOrbit w) (N : ℕ) [NeZero N]
    (x y : σ → ZMod N) :
    let E := D.withLattice Γ m hm hin hout
    letI := D.metricSpace
    letI := E.metricSpace
    dist (E.cyclicOrbitPoint g N x) (E.cyclicOrbitPoint g N y) ≤
      dist (D.cyclicOrbitPoint g N x) (D.cyclicOrbitPoint g N y) := by
  let E := D.withLattice Γ m hm hin hout
  let := D.metricSpace
  let := E.metricSpace
  have h := (sublatticeProjection_lipschitz E D hΓ rfl).dist_le_mul
    (D.cyclicOrbitPoint g N x) (D.cyclicOrbitPoint g N y)
  change dist (E.cyclicOrbitPoint g N x) (E.cyclicOrbitPoint g N y) ≤
    (1 : ℝ) * dist (D.cyclicOrbitPoint g N x) (D.cyclicOrbitPoint g N y) at h
  simpa only [one_mul] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI

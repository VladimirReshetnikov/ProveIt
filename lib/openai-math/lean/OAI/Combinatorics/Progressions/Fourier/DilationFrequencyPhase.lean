import OAI.Combinatorics.Progressions.Estimates.NativeDilationObservable

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem NilpotentLieFiltration.realDilationPair_frequency_phase
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairFiltration (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairFiltration (q : ℚ)).realification.subgroup s) :
    (realifyFunctional η (F.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ s) • (realifyFunctional η
        (F.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

theorem MultidegreeLieFiltration.realDilationPair_frequency_phase
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)
    (q : ℤ) (η : L →ₗ[ℚ] ℚ)
    (g : (F.dilationPairMultidegree (q : ℚ)).realification.Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).realification.subgroup bound) :
    (realifyFunctional η (F.ordinary.realDilationPairProjection (q : ℚ) 0 g).coord : CircleFourier.Circle) =
      (q ^ ∑ i, bound i) • (realifyFunctional η
        (F.ordinary.realDilationPairProjection (q : ℚ) 1 g).coord : CircleFourier.Circle) := by
  rw [F.realDilationPair_top_group_relation q g hg, NilpotentLieBCHGroup.coord_zpow,
    map_zsmul, AddCircle.coe_zsmul]

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Sampling.MarkedKernelProjectionScoreRestoration

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}

theorem map_log_constantGroupOrbit_mul_of_realificationMap_eq_one
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M) (w : σ → ℕ)
    (orbit : F.realification.PolynomialOrbit w) (z : F.realification.Group)
    (hz : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ z = 1) :
    VectorPolynomial.map (realLieHomToRat (realificationLieHom φ)).toLinearMap
        (F.realification.constantGroupOrbit w z * orbit).log =
      VectorPolynomial.map (realLieHomToRat (realificationLieHom φ)).toLinearMap orbit.log := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  have he : realificationMap (hnil := F.lowerCentralSeries_eq_bot)
      (hM := G.lowerCentralSeries_eq_bot) φ
        (F.realification.polynomialOrbitRealEval w x
          (F.realification.constantGroupOrbit w z * orbit)) =
      realificationMap (hnil := F.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
          (F.realification.polynomialOrbitRealEval w x orbit) := by
    rw [map_mul, polynomialOrbitRealEval_constantGroupOrbit, map_mul, hz, one_mul]
  have hc := congrArg NilpotentLieBCHGroup.coord he
  calc
    _ = realificationLieHom φ
        (eval₂ x (F.realification.constantGroupOrbit w z * orbit).log) :=
      eval₂_map (realificationLieHom φ).toLinearMap x _
    _ = realificationLieHom φ (eval₂ x orbit.log) := hc
    _ = _ := (eval₂_map (realificationLieHom φ).toLinearMap x orbit.log).symm

end Erdos3.NilpotentLieFiltration

end

end OAI

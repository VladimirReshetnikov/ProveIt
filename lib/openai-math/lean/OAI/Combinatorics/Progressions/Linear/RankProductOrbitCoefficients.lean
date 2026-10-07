import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization

namespace OAI

section

namespace Erdos3.NativeRankInterval

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  (I : NativeRankInterval W out H t branch p q) (i : Fin I.expansion.count)

theorem rankProjection_coefficient (α : Unit →₀ ℕ) (k : Fin 4) :
    (LinearMap.proj k).baseChange ℝ
        ((I.rankProjection i).toLinearMap.baseChange ℝ (coefficients (I.productOrbit i).log α)) =
      coefficients ((W.fourPointFactors out (rankQuadrupleParameters t)
        (cyclicBranchOffset t.1 branch) ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit).log α := by
  change realificationLieHom (liePiEval k)
    (realificationLieHom (I.rankProjection i) (coefficients (I.productOrbit i).log α)) = _
  have h := realification_liePiEval_liePiMap (M := fun _ : Fin 4 => W.L)
    (fun j : Fin 4 => (liePiEval (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) j)) :
      (∀ a : Option (Fin 4), optionLieSpace (I.expansion.L i) (fun _ : Fin 4 => W.L) a) →ₗ⁅ℚ⁆ W.L))
    (coefficients (I.productOrbit i).log α) k
  apply h.trans
  exact NilpotentLieFiltration.piRealOrbit_coefficient
    (fun j => (I.productModels i j).filtration) (fun j => (I.productTests i j).orbit)
    α (some ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))

theorem rankProjection_component_log (k : Fin 4) :
    VectorPolynomial.map
        ((realificationLieHom ((liePiEval k).comp (I.rankProjection i))).toLinearMap.restrictScalars ℚ)
        (I.productOrbit i).log =
      (W.fourPointFactors out (rankQuadrupleParameters t) (cyclicBranchOffset t.1 branch)
        ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)).orbit.log := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  change ((LinearMap.proj k).comp (I.rankProjection i).toLinearMap).baseChange ℝ
    (coefficients (I.productOrbit i).log α) = _
  rw [LinearMap.baseChange_comp, LinearMap.comp_apply]
  exact I.rankProjection_coefficient i α k

end Erdos3.NativeRankInterval

end

end OAI

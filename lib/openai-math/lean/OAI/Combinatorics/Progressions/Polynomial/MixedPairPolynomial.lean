/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.NativeMixedPairNiltest

namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def mixedPairPolynomial :
    ((pi V.mixedPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin (n + 2) => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.mixedPairModels k).filtration)
    (fun k => (V.mixedPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

def mixedPairProjection (k : Fin 2) : V.MixedPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem mixedPairFrequency_apply (x : V.MixedPairAlgebra) :
    piFrequency V.mixedPairFrequencies x =
      W.vertical.frequency (V.mixedPairProjection 0 x) -
        W.vertical.frequency (V.mixedPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem mixedPairFrequency_real (x : ℝ ⊗[ℚ] V.MixedPairAlgebra) :
    realifyFunctional (piFrequency V.mixedPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedPairProjection 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.mixedPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairPolynomial_eq_test : V.mixedPairPolynomial =
    ⟨⟨V.mixedPairNiltest.orbit.log, V.mixedPairNiltest.orbit.property⟩⟩ := rfl

theorem mixedPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.MixedPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.mixedPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.mixedPairNiltest.symbol b w hF =
      (pi V.mixedPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin (n + 2) => 1) V.mixedPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

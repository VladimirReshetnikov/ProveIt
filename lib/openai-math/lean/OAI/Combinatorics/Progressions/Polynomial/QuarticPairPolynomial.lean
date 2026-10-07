/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.QuarticPairNiltest

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

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def quarticPairPolynomial :
    ((pi V.quarticPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.quarticPairModels k).filtration)
    (fun k => (V.quarticPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

def quarticPairProjection (k : Fin 2) : V.QuarticPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem quarticPairFrequency_apply (x : V.QuarticPairAlgebra) :
    piFrequency V.quarticPairFrequencies x =
      W.vertical.frequency (V.quarticPairProjection 0 x) -
        W.vertical.frequency (V.quarticPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem quarticPairFrequency_real (x : ℝ ⊗[ℚ] V.QuarticPairAlgebra) :
    realifyFunctional (piFrequency V.quarticPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticPairProjection 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.quarticPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

theorem quarticPairPolynomial_eq_test : V.quarticPairPolynomial =
    ⟨⟨V.quarticPairNiltest.orbit.log, V.quarticPairNiltest.orbit.property⟩⟩ := rfl

theorem quarticPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.QuarticPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.quarticPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.quarticPairNiltest.symbol b w hF =
      (pi V.quarticPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin 4 => 1) V.quarticPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

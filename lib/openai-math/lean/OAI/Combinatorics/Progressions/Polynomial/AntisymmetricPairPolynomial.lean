/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.AntisymmetricPairNiltest

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
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

noncomputable def antisymmetricPairPolynomial :
    ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.antisymmetricPairModels k).filtration)
    (fun k => (V.antisymmetricPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

def antisymmetricPairProjection (k : Fin 2) : V.AntisymmetricPairAlgebra →ₗ⁅ℚ⁆ W.L :=
  liePiEval (some k)

theorem antisymmetricPairFrequency_apply (x : V.AntisymmetricPairAlgebra) :
    piFrequency V.antisymmetricPairFrequencies x =
      W.vertical.frequency (V.antisymmetricPairProjection 1 x) -
        W.vertical.frequency (V.antisymmetricPairProjection 0 x) := by
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  change 0 + (-W.vertical.frequency (x (some 0)) + W.vertical.frequency (x (some 1))) =
    W.vertical.frequency (x (some 1)) - W.vertical.frequency (x (some 0))
  ring

theorem antisymmetricPairFrequency_real (x : ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra) :
    realifyFunctional (piFrequency V.antisymmetricPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 1) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.antisymmetricPairProjection 0) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul scalar element =>
    simp only [realifyFunctional_tmul, V.antisymmetricPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add left right hleft hright => simp only [map_add, hleft, hright]; ring

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem antisymmetricPairPolynomial_eq_test : V.antisymmetricPairPolynomial =
    ⟨⟨V.antisymmetricPairNiltest.orbit.log, V.antisymmetricPairNiltest.orbit.property⟩⟩ := rfl

theorem antisymmetricPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.AntisymmetricPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.antisymmetricPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.antisymmetricPairNiltest.symbol b w hF =
      (pi V.antisymmetricPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin 2 => 1) V.antisymmetricPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

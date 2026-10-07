/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Nilpotent.CubicPairNiltest

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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
  {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

noncomputable def cubicPairPolynomial :
    ((pi V.cubicPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 3 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun k => (V.cubicPairModels k).filtration)
    (fun k => (V.cubicPairTests k).orbit)
  ⟨⟨o.log, o.property⟩⟩

def cubicPairProjection (k : Fin 2) : V.CubicPairAlgebra →ₗ⁅ℚ⁆ W.L := liePiEval (some k)

theorem cubicPairFrequency_apply (x : V.CubicPairAlgebra) :
    piFrequency V.cubicPairFrequencies x =
      2 * (W.vertical.frequency (V.cubicPairProjection 1 x) -
        W.vertical.frequency (V.cubicPairProjection 0 x)) := by
  have h (x₀ x₁ : W.L) :
      0 + ((-(2 • W.vertical.frequency)) x₀ + (2 • W.vertical.frequency) x₁) =
        2 * (W.vertical.frequency x₁ - W.vertical.frequency x₀) := by
    simp only [LinearMap.neg_apply, LinearMap.smul_apply, nsmul_eq_mul]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem cubicPairFrequency_real (x : ℝ ⊗[ℚ] V.CubicPairAlgebra) :
    realifyFunctional (piFrequency V.cubicPairFrequencies) x =
      2 * (realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 1) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.cubicPairProjection 0) x)) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.cubicPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_sub]
    ring
  | add x y hx hy => simp only [map_add, hx, hy]; ring

variable
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

theorem cubicPairPolynomial_eq_test : V.cubicPairPolynomial =
    ⟨⟨V.cubicPairNiltest.orbit.log, V.cubicPairNiltest.orbit.property⟩⟩ := rfl

theorem cubicPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.CubicPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.cubicPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.cubicPairNiltest.symbol b w hF =
      (pi V.cubicPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin 3 => 1) V.cubicPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

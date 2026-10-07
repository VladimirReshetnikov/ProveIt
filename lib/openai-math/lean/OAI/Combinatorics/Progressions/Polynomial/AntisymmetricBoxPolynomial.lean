import OAI.Combinatorics.Progressions.Geometry.MixedCoordinateTransfer

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def antisymmetricBoxPolynomial (i j : Fin W.outputDim) :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group :=
  let o := NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 => W.model.filtration)
    (fun k => (W.antisymmetricBoxFactors i j k).orbit)
  ⟨⟨o.log, o.property⟩⟩

theorem antisymmetricBoxPolynomial_mono (hpq : p ≤ q) (i j : Fin W.outputDim) :
    (W.mono hpq).antisymmetricBoxPolynomial i j = W.antisymmetricBoxPolynomial i j := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  apply congrArg (fun o : (pi (fun _ : Fin 8 => W.model)).filtration.realification.PolynomialOrbit
    (fun _ : Fin 4 => 1) => o.log)
  apply congrArg (NilpotentLieFiltration.piRealOrbit (fun _ : Fin 8 => W.model.filtration))
  funext k
  fin_cases k <;> rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

theorem antisymmetricBoxPolynomial_eq_test (hp : 0 ≤ p) (i j : Fin W.outputDim) :
    W.antisymmetricBoxPolynomial i j =
      ⟨⟨(W.antisymmetricBoxNiltest hp i j).orbit.log,
        (W.antisymmetricBoxNiltest hp i j).orbit.property⟩⟩ := rfl

theorem antisymmetricBoxNiltest_symbol (hp : 0 ≤ p) (i j : Fin W.outputDim)
    {ι : Type*} (b : Module.Basis ι ℚ (Fin 8 → W.L)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (fun _ : Fin 8 => W.model)).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ ω a})) :
    (W.antisymmetricBoxNiltest hp i j).symbol b ω hF =
      (pi (fun _ : Fin 8 => W.model)).filtration.realPolynomialSymbolHom b ω hF
        (fun _ : Fin 4 => 1) (W.antisymmetricBoxPolynomial i j) := rfl

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI

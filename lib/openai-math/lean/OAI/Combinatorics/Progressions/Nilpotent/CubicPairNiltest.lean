import OAI.Combinatorics.Progressions.Estimates.CubicRootPermutation

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
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

noncomputable def cubicPairNiltest : (pi V.cubicPairModels).Niltest (fun _ : Fin 3 => 1) :=
  piNiltest V.cubicPairModels V.cubicPairTests
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ cubicPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le))
    V.cubicPairTests_complexity

theorem cubicPairNiltest_complexity :
    V.cubicPairNiltest.ComplexityLE (productNiltestBudget (cubicPairBudget p q)) :=
  piNiltest_complexity V.cubicPairModels V.cubicPairTests _ _ _

theorem cubicPairNiltest_eval (n : Fin 3 → ℤ) :
    V.cubicPairNiltest.eval n =
      W.cubicAntisymmetricPair i j (n 1) (n 2) (n 0 + shift) * star (V.test.eval n) := by
  rw [cubicPairNiltest, piNiltest_eval]
  exact V.cubicPairTests_eval n

theorem cubicPairNiltest_vertical (z : (pi V.cubicPairModels).RealGroup)
    (hz : z ∈ (pi V.cubicPairModels).filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : (pi V.cubicPairModels).Space) :
    V.cubicPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.cubicPairFrequencies) z.coord : ℝ) : CircleFourier.Circle) *
          V.cubicPairNiltest.observable x :=
  piNiltest_vertical V.cubicPairModels V.cubicPairTests V.cubicPairFrequencies _ _ _
    V.cubicPairTests_vertical z hz x

theorem cubicPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 n ∈ integerBox (fun _ : Fin 3 => N), V.cubicPairNiltest.eval n‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.cubicPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI

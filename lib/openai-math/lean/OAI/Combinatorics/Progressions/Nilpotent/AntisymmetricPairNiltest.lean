import OAI.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator

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
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def antisymmetricPairNiltest :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels V.antisymmetricPairTests
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    V.antisymmetricPairTests_complexity

theorem antisymmetricPairNiltest_complexity :
    V.antisymmetricPairNiltest.ComplexityLE (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels V.antisymmetricPairTests _ _ _

theorem antisymmetricPairNiltest_eval (n : Fin 2 → ℤ) :
    V.antisymmetricPairNiltest.eval n =
      W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) := by
  rw [antisymmetricPairNiltest, piNiltest_eval]
  exact V.antisymmetricPairTests_eval n

theorem antisymmetricPairNiltest_vertical
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (pi V.antisymmetricPairModels).Space) :
    V.antisymmetricPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.antisymmetricPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * V.antisymmetricPairNiltest.observable x :=
  piNiltest_vertical V.antisymmetricPairModels V.antisymmetricPairTests
    V.antisymmetricPairFrequencies _ _ _ V.antisymmetricPairTests_vertical z hz x

theorem antisymmetricPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 n ∈ integerBox (fun _ : Fin 2 => N), V.antisymmetricPairNiltest.eval n‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.antisymmetricPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI

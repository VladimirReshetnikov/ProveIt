import OAI.Combinatorics.Progressions.Estimates.QuarticPairFactors

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
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

noncomputable def quarticPairNiltest : (pi V.quarticPairModels).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest V.quarticPairModels V.quarticPairTests
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ quarticPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le))
    V.quarticPairTests_complexity

theorem quarticPairNiltest_complexity :
    V.quarticPairNiltest.ComplexityLE (productNiltestBudget (quarticPairBudget p q)) :=
  piNiltest_complexity V.quarticPairModels V.quarticPairTests _ _ _

theorem quarticPairNiltest_eval (n : Fin 4 → ℤ) :
    V.quarticPairNiltest.eval n =
      W.quarticAntisymmetric i j n * star (V.test.eval n) := by
  rw [quarticPairNiltest, piNiltest_eval]
  exact V.quarticPairTests_eval n

theorem quarticPairNiltest_vertical (z : (pi V.quarticPairModels).RealGroup)
    (hz : z ∈ (pi V.quarticPairModels).filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : (pi V.quarticPairModels).Space) :
    V.quarticPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.quarticPairFrequencies) z.coord : ℝ) : CircleFourier.Circle) *
          V.quarticPairNiltest.observable x :=
  piNiltest_vertical V.quarticPairModels V.quarticPairTests V.quarticPairFrequencies _ _ _
    V.quarticPairTests_vertical z hz x

theorem quarticPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 n ∈ integerBox (fun _ : Fin 4 => N), V.quarticPairNiltest.eval n‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.quarticPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI

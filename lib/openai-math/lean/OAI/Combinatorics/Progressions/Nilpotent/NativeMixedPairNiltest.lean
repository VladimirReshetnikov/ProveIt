import OAI.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence

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
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedPairNiltest : (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels V.mixedPairTests
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    V.mixedPairTests_complexity

theorem mixedPairNiltest_complexity :
    V.mixedPairNiltest.ComplexityLE (productNiltestBudget (mixedPairBudget p q)) :=
  piNiltest_complexity V.mixedPairModels V.mixedPairTests _ _ _

theorem mixedPairNiltest_eval (x : Fin (n + 2) → ℤ) :
    V.mixedPairNiltest.eval x =
      W.mixedAntisymmetric i j x * star (V.test.eval x) := by
  rw [mixedPairNiltest, piNiltest_eval]
  exact V.mixedPairTests_eval x

theorem mixedPairNiltest_vertical (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (pi V.mixedPairModels).Space) :
    V.mixedPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedPairFrequencies) z.coord : ℝ) : CircleFourier.Circle) *
          V.mixedPairNiltest.observable x :=
  piNiltest_vertical V.mixedPairModels V.mixedPairTests V.mixedPairFrequencies _ _ _
    V.mixedPairTests_vertical z hz x

theorem mixedPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 x ∈ integerBox (fun _ : Fin (n + 2) => N), V.mixedPairNiltest.eval x‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.mixedPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop

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

noncomputable def pairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.antisymmetricPairModels l).Niltest (fun _ : Fin 2 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some l =>
      ![![W.pairComponent out 0 1, (W.pairComponent out 1 0).oneOnOrbit],
        ![(W.pairComponent out 0 1).oneOnOrbit, W.pairComponent out 1 0]] k l

theorem pairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.pairCoordinateTests k out l).ComplexityLE (antisymmetricPairBudget p q) := by
  have htwo : 2 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (2 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact V.antisymmetricPairTests_complexity (some 0)
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.antisymmetricPairTests_complexity (some 0)).1
    · exact V.antisymmetricPairTests_complexity (some 1)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

noncomputable def pairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.antisymmetricPairModels).Niltest (fun _ : Fin 2 => 1) :=
  piNiltest V.antisymmetricPairModels (V.pairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le)
    (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
    (V.pairCoordinateTests_complexity k out)

theorem pairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.pairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels (V.pairCoordinateTests k out) _ _ _

theorem pairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.antisymmetricPairModels).Space) :
    (V.pairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.antisymmetricPairModels (some k) x) := by
  change (∏ l, (V.pairCoordinateTests k out l).observable
    (productProjection V.antisymmetricPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.antisymmetricPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.antisymmetricPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.QuarticPairFrozenEquivalence

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
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def quarticPairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.quarticPairModels l).Niltest (fun _ : Fin 4 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some l =>
      ![![W.quarticPairComponent out id, (W.quarticPairComponent out ![1, 0, 2, 3]).oneOnOrbit],
        ![(W.quarticPairComponent out id).oneOnOrbit, W.quarticPairComponent out ![1, 0, 2, 3]]] k l

theorem quarticPairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.quarticPairCoordinateTests k out l).ComplexityLE (quarticPairBudget (tensorPowerBudget 6 p) q) := by
  have htwo : 2 ≤ quarticPairBudget (tensorPowerBudget 6 p) q :=
    (by norm_num : (2 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.quarticPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact (W.quarticPairComponent_complexity out id).mono V.quarticOriginalPairComparison_component_cost
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.quarticPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.quarticPairTests_complexity (some 0)).1
    · exact (W.quarticPairComponent_complexity out ![1, 0, 2, 3]).mono V.quarticOriginalPairComparison_component_cost

variable [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

noncomputable def quarticPairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.quarticPairModels).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest V.quarticPairModels (V.quarticPairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ quarticPairBudget (tensorPowerBudget 6 p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le))
    (V.quarticPairCoordinateTests_complexity k out)

theorem quarticPairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.quarticPairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q)) :=
  piNiltest_complexity V.quarticPairModels (V.quarticPairCoordinateTests k out) _ _ _

theorem quarticPairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.quarticPairModels).Space) :
    (V.quarticPairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.quarticPairModels (some k) x) := by
  change (∏ l, (V.quarticPairCoordinateTests k out l).observable
    (productProjection V.quarticPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.quarticPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.quarticPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

theorem quarticPairCoordinateNiltest_orbit (k : Fin 2) (out : Fin W.outputDim) :
    (V.quarticPairCoordinateNiltest k out).orbit = V.quarticPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun l => (V.quarticPairModels l).filtration))
  funext l
  cases l with
  | none => rfl
  | some l => fin_cases k <;> fin_cases l <;> rfl

theorem quarticPairCoordinateNiltest_eval (k : Fin 2) (out : Fin W.outputDim) (n : Fin 4 → ℤ) :
    (V.quarticPairCoordinateNiltest k out).eval n =
      W.eval out (quarticInput (n (![0, 1] k)) ![n (![1, 0] k), n 2, n 3]) := by
  rw [quarticPairCoordinateNiltest, piNiltest_eval, Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * ((W.quarticPairComponent out id).eval n * 1) = _
    rw [one_mul, mul_one, W.quarticPairComponent_eval]
    rfl
  · change 1 * (1 * (W.quarticPairComponent out ![1, 0, 2, 3]).eval n) = _
    rw [one_mul, one_mul, W.quarticPairComponent_eval]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

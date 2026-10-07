import OAI.Combinatorics.Progressions.Estimates.MixedPairFrozenEquivalence

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

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

noncomputable def mixedPairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.mixedPairModels l).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some l =>
      ![![W.mixedPairComponent out id, (W.mixedPairComponent out (mixedExchangeCoordinate n)).oneOnOrbit],
        ![(W.mixedPairComponent out id).oneOnOrbit, W.mixedPairComponent out (mixedExchangeCoordinate n)]] k l

theorem mixedPairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.mixedPairCoordinateTests k out l).ComplexityLE (mixedPairBudget (tensorPowerBudget m p) q) := by
  have htwo : 2 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact (W.mixedPairComponent_complexity out id).mono V.mixedOriginalPairComparison_component_cost
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.mixedPairTests_complexity (some 0)).1
    · exact (W.mixedPairComponent_complexity out (mixedExchangeCoordinate n)).mono V.mixedOriginalPairComparison_component_cost

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedPairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedPairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget (tensorPowerBudget m p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedPairCoordinateTests_complexity k out)

theorem mixedPairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.mixedPairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedPairCoordinateTests k out) _ _ _

theorem mixedPairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedPairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.mixedPairModels (some k) x) := by
  change (∏ l, (V.mixedPairCoordinateTests k out l).observable
    (productProjection V.mixedPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.mixedPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.mixedPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

theorem mixedPairCoordinateNiltest_orbit (k : Fin 2) (out : Fin W.outputDim) :
    (V.mixedPairCoordinateNiltest k out).orbit = V.mixedPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun l => (V.mixedPairModels l).filtration))
  funext l
  cases l with
  | none => rfl
  | some l => fin_cases k <;> fin_cases l <;> rfl

theorem mixedPairCoordinateNiltest_eval (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    (V.mixedPairCoordinateNiltest k out).eval x =
      W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k))
        (fun j => x j.succ.succ)) := by
  rw [mixedPairCoordinateNiltest, piNiltest_eval, Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * ((W.mixedPairComponent out id).eval x * 1) = _
    rw [one_mul, mul_one, W.mixedPairComponent_eval]
    rfl
  · change 1 * (1 * (W.mixedPairComponent out (mixedExchangeCoordinate n)).eval x) = _
    rw [one_mul, one_mul, W.mixedPairComponent_eval]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

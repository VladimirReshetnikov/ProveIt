import OAI.Combinatorics.Progressions.Estimates.CubicPairFactoredModel

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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  (V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift)))

noncomputable def cubicPairCoordinateTests (k : Fin 2) (out : Fin W.outputDim) :
    ∀ l, (V.cubicPairModels l).Niltest (fun _ : Fin 3 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some l =>
      ![![W.cubicOriginalComponent out 1 2 0 shift, (W.cubicOriginalComponent out 2 1 0 shift).oneOnOrbit],
        ![(W.cubicOriginalComponent out 1 2 0 shift).oneOnOrbit, W.cubicOriginalComponent out 2 1 0 shift]] k l

theorem cubicPairCoordinateTests_complexity (k : Fin 2) (out : Fin W.outputDim) (l : Option (Fin 2)) :
    (V.cubicPairCoordinateTests k out l).ComplexityLE (cubicPairBudget p q) := by
  have htwo : 2 ≤ cubicPairBudget p q :=
    (by norm_num : (2 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  cases l with
  | none => exact Niltest.oneOnOrbit_complexity _ htwo (V.cubicPairTests_complexity none).1
  | some l =>
    fin_cases k <;> fin_cases l
    · exact (W.cubicOriginalComponent_complexity out 1 2 0 shift).mono V.cubicOriginalComponent_cost
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.cubicPairTests_complexity (some 1)).1
    · exact Niltest.oneOnOrbit_complexity _ htwo (V.cubicPairTests_complexity (some 0)).1
    · exact (W.cubicOriginalComponent_complexity out 2 1 0 shift).mono V.cubicOriginalComponent_cost

variable [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

noncomputable def cubicPairCoordinateNiltest (k : Fin 2) (out : Fin W.outputDim) :
    (pi V.cubicPairModels).Niltest (fun _ : Fin 3 => 1) :=
  piNiltest V.cubicPairModels (V.cubicPairCoordinateTests k out)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ cubicPairBudget p q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le))
    (V.cubicPairCoordinateTests_complexity k out)

theorem cubicPairCoordinateNiltest_complexity (k : Fin 2) (out : Fin W.outputDim) :
    (V.cubicPairCoordinateNiltest k out).ComplexityLE
      (productNiltestBudget (cubicPairBudget p q)) :=
  piNiltest_complexity V.cubicPairModels (V.cubicPairCoordinateTests k out) _ _ _

theorem cubicPairCoordinateNiltest_observable (k : Fin 2) (out : Fin W.outputDim)
    (x : (pi V.cubicPairModels).Space) :
    (V.cubicPairCoordinateNiltest k out).observable x =
      W.vertical.observable out (productProjection V.cubicPairModels (some k) x) := by
  change (∏ l, (V.cubicPairCoordinateTests k out l).observable
    (productProjection V.cubicPairModels l x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * (W.vertical.observable out
      (productProjection V.cubicPairModels (some 0) x) * 1) = _
    simp only [one_mul, mul_one]
    rfl
  · change 1 * (1 * W.vertical.observable out
      (productProjection V.cubicPairModels (some 1) x)) = _
    simp only [one_mul]
    rfl

theorem cubicPairCoordinateNiltest_orbit (k : Fin 2) (out : Fin W.outputDim) :
    (V.cubicPairCoordinateNiltest k out).orbit = V.cubicPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun l => (V.cubicPairModels l).filtration))
  funext l
  cases l with
  | none => rfl
  | some l => fin_cases k <;> fin_cases l <;> rfl

theorem cubicPairCoordinateNiltest_eval (k : Fin 2) (out : Fin W.outputDim) (n : Fin 3 → ℤ) :
    (V.cubicPairCoordinateNiltest k out).eval n =
      W.eval out (cubicTrilinearInput (n k.succ) (n k.rev.succ) (n 0 + shift)) := by
  rw [cubicPairCoordinateNiltest, piNiltest_eval, Fintype.prod_option, Fin.prod_univ_two]
  fin_cases k
  · change 1 * ((W.cubicOriginalComponent out 1 2 0 shift).eval n * 1) = _
    rw [one_mul, mul_one, W.cubicOriginalComponent_eval]
    rfl
  · change 1 * (1 * (W.cubicOriginalComponent out 2 1 0 shift).eval n) = _
    rw [one_mul, one_mul, W.cubicOriginalComponent_eval]
    rfl

end Erdos3.NativeSampleCorrelation

end

end OAI

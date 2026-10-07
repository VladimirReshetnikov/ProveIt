/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Fourier.MixedOriginalPairFrequency

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n m : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem mixedOriginalPairComparison_component_cost : p + 4 ≤ mixedPairBudget (tensorPowerBudget m p) q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : p ≤ tensorPowerBudget m p := (tensorPowerBudget_bounds m hp).1
  have hcost := V.mixedPairComparison_component_cost
  linarith only [hpow, hcost]

noncomputable def mixedOriginalPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => (W.tensorPower m).L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem mixedOriginalPairFrequency_apply (x : V.MixedPairAlgebra) :
    piFrequency V.mixedOriginalPairFrequencies x =
      W.vertical.frequency (V.mixedOriginalPairProjection 0 x) -
        W.vertical.frequency (V.mixedOriginalPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem mixedOriginalPairFrequency_real (x : ℝ ⊗[ℚ] V.MixedPairAlgebra) :
    realifyFunctional (piFrequency V.mixedOriginalPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.mixedOriginalPairProjection 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.mixedOriginalPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

noncomputable def mixedOriginalPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.mixedPairModels k).Niltest (fun _ : Fin (n + 2) => 1)
  | none => (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega :
      n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).oneOnOrbit
  | some k => ![W.mixedPairComponent a id, (W.mixedPairComponent b (mixedExchangeCoordinate n)).conjugate] k

theorem mixedOriginalPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.mixedOriginalPairComparisonTests a b k).ComplexityLE (mixedPairBudget (tensorPowerBudget m p) q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
      (V.mixedPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.mixedPairComponent_complexity a id).mono V.mixedOriginalPairComparison_component_cost
    · exact (W.mixedPairComponent_complexity b (mixedExchangeCoordinate n)).mono V.mixedOriginalPairComparison_component_cost

theorem mixedOriginalPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (V.mixedPairModels k).Space) :
    (V.mixedOriginalPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedOriginalPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedOriginalPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical a id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical b (mixedExchangeCoordinate n)) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

noncomputable def mixedOriginalPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.mixedPairModels).Niltest (fun _ : Fin (n + 2) => 1) :=
  piNiltest V.mixedPairModels (V.mixedOriginalPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ mixedPairBudget (tensorPowerBudget m p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le))
    (V.mixedOriginalPairComparisonTests_complexity a b)

theorem mixedOriginalPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.mixedOriginalPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) :=
  piNiltest_complexity V.mixedPairModels (V.mixedOriginalPairComparisonTests a b) _ _ _

theorem mixedOriginalPairComparisonNiltest_orbit (a b : Fin W.outputDim) :
    (V.mixedOriginalPairComparisonNiltest a b).orbit = V.mixedPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun k => (V.mixedPairModels k).filtration))
  funext k
  cases k with
  | none => rfl
  | some k => fin_cases k <;> rfl

theorem mixedOriginalPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable x =
      W.vertical.observable a (productProjection V.mixedPairModels (some 0) x) *
        star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x)) := by
  change (∏ k, (V.mixedOriginalPairComparisonTests a b k).observable
    (productProjection V.mixedPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (W.vertical.observable a
    (productProjection V.mixedPairModels (some 0) x) *
      star (W.vertical.observable b (productProjection V.mixedPairModels (some 1) x))) = _
  exact one_mul _

theorem mixedOriginalPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.mixedOriginalPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.mixedOriginalPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.mixedPairModels (V.mixedOriginalPairComparisonTests a b)
    V.mixedOriginalPairFrequencies _ _ _ (V.mixedOriginalPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} [NeZero m] {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixed_original_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.mixedPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : MixedReplicatedIndex (n + 1), 1)) (x : (pi V.mixedPairModels).Space) :
    (V.mixedOriginalPairComparisonNiltest a b).observable (z • x) =
      (V.mixedOriginalPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.mixedPairModels).filtration.realification.subgroup
      (∑ _ : MixedReplicatedIndex (n + 1), 1) :=
    (pi V.mixedPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.mixedOriginalPairComparisonNiltest_vertical a b z htop,
    V.mixedOriginalPairFrequency_real, R.mixed_original_pair_top_agreement z.coord hz,
    sub_self]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairFrozenVector (k : Fin 2)
    (a b : (pi V.mixedPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin (n + 2) → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.mixedPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

theorem mixedPairFrozenVector_unit (k : Fin 2)
    (a b : (pi V.mixedPairModels).RealGroup) (x : Fin (n + 2) → ℤ) :
    ∑ out, ‖R.mixedPairFrozenVector k a b out x‖ ^ 2 = 1 :=
  W.vertical.unit _

def HasMixedPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ den : ℕ, 0 < den → (den : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.mixedPairModels).RealGroup,
      (∀ i, |((pi V.mixedPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.mixedPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid den →
      NativeIntegerVectorEquivalence (n + 1) b (R.mixedPairFrozenVector 0 a r) (R.mixedPairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

theorem exists_mixed_frozen_equivalence_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p q r u : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r → 0 ≤ u →
      ∃ t : ℝ, 0 ≤ t ∧ r ≤ t ∧ u ≤ t ∧ p ≤ t ∧
        productNiltestBudget (mixedPairBudget p q) ≤ t ∧
        t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r u hp hq hr hu
  let v := p + q + r + u
  let b := 4 * (v + 1) + raisedNiltestBudget v + 6
  let t := productNiltestBudget b + v + 3
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hpt : p ≤ t := by dsimp [t, v]; linarith
  have hBt : mixedPairBudget p q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget p q := by
    unfold mixedPairBudget raisedNiltestBudget
    positivity
  have hprodmono : productNiltestBudget (mixedPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  exact ⟨t, ht, hrt, hut, hpt, htest, hsum⟩

theorem exists_mixed_pair_frozen_equivalence (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasMixedPairFrozenEquivalence u ((tensorPowerBudget m p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion (n + 1)
  have hdegree : n + 1 + 1 = ∑ _ : MixedReplicatedIndex (n + 1), 1 :=
    (mixedReplicated_totalDegree n).symm
  rw [hdegree] at hfrozen
  obtain ⟨C, hC, hbudget⟩ := exists_mixed_frozen_equivalence_budget a
  refine ⟨C, hC, ?_⟩
  intro p q r u m _ W N _ i j V R _ _ _ _ hr hu den hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpk : p ≤ tensorPowerBudget m p := (tensorPowerBudget_bounds m hp).1
  obtain ⟨t, ht, hrt, hut, hpt, htest, hsum⟩ :=
    hbudget (tensorPowerBudget m p) q r u (hp.trans hpk) hq hr hu
  have htC : t ≤ (tensorPowerBudget m p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((tensorPowerBudget m p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpk.trans (hpt.trans htC)))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.mixedPairModels) (R.mono hrt hN)
    (V.mixedOriginalPairComparisonNiltest out₀ out₁) ht ((V.mixedOriginalPairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.mixed_original_pair_comparison_invariant out₀ out₁) den hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1)
      ((tensorPowerBudget m p + q + r + u + C) ^ C) (fun x =>
        (V.mixedOriginalPairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x)))) :=
    ⟨F.mono hcost⟩
  have heq : (fun x : Fin (n + 2) → ℤ =>
      (V.mixedOriginalPairComparisonNiltest out₀ out₁).observable
        (QuotientGroup.mk (R.frozenMiddleValue left right x))) =
      (fun x => R.mixedPairFrozenVector 0 left right out₀ x *
        star (R.mixedPairFrozenVector 1 left right out₁ x)) := by
    funext x
    rw [V.mixedOriginalPairComparisonNiltest_observable]
    rfl
  exact (congrArg (fun f : (Fin (n + 2) → ℤ) → ℂ =>
    Nonempty (NativeIntegerExpansion (fun _ : Fin (n + 2) => 1) (n + 1)
      ((tensorPowerBudget m p + q + r + u + C) ^ C) f)) heq).mp hF

end Erdos3

end

end OAI

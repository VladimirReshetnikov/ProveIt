/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Fourier.QuarticOriginalPairFrequency

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

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

include V in
theorem quarticOriginalPairComparison_component_cost : p + 4 ≤ quarticPairBudget (tensorPowerBudget 6 p) q := by
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : p ≤ tensorPowerBudget 6 p := (tensorPowerBudget_bounds 6 hp).1
  have hcost := V.quarticPairComparison_component_cost
  linarith only [hpow, hcost]

noncomputable def quarticOriginalPairFrequencies :
    ∀ k, optionLieSpace V.L (fun _ : Fin 2 => (W.tensorPower 6).L) k →ₗ[ℚ] ℚ
  | none => 0
  | some k => ![W.vertical.frequency, -W.vertical.frequency] k

theorem quarticOriginalPairFrequency_apply (x : V.QuarticPairAlgebra) :
    piFrequency V.quarticOriginalPairFrequencies x =
      W.vertical.frequency (V.quarticOriginalPairProjection 0 x) -
        W.vertical.frequency (V.quarticOriginalPairProjection 1 x) := by
  have h (x₀ x₁ : W.L) :
      0 + (W.vertical.frequency x₀ + (-W.vertical.frequency) x₁) =
        W.vertical.frequency x₀ - W.vertical.frequency x₁ := by
    simp only [LinearMap.neg_apply]
    ring
  rw [piFrequency_apply, Fintype.sum_option, Fin.sum_univ_two]
  exact h (x (some 0)) (x (some 1))

theorem quarticOriginalPairFrequency_real (x : ℝ ⊗[ℚ] V.QuarticPairAlgebra) :
    realifyFunctional (piFrequency V.quarticOriginalPairFrequencies) x =
      realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticOriginalPairProjection 0) x) -
        realifyFunctional W.vertical.frequency (realificationLieHom (V.quarticOriginalPairProjection 1) x) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, V.quarticOriginalPairFrequency_apply,
      realificationLieHom_tmul, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

noncomputable def quarticOriginalPairComparisonTests (a b : Fin W.outputDim) :
    ∀ k, (V.quarticPairModels k).Niltest (fun _ : Fin 4 => 1)
  | none => (V.test.raiseStep (by decide)).oneOnOrbit
  | some k => ![W.quarticPairComponent a id, (W.quarticPairComponent b ![1, 0, 2, 3]).conjugate] k

theorem quarticOriginalPairComparisonTests_complexity (a b : Fin W.outputDim) (k : Option (Fin 2)) :
    (V.quarticOriginalPairComparisonTests a b k).ComplexityLE (quarticPairBudget (tensorPowerBudget 6 p) q) := by
  cases k with
  | none =>
    exact Niltest.oneOnOrbit_complexity _
      ((by norm_num : (2 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le)
      (V.quarticPairTests_complexity none).1
  | some k =>
    fin_cases k
    · exact (W.quarticPairComponent_complexity a id).mono V.quarticOriginalPairComparison_component_cost
    · exact (W.quarticPairComponent_complexity b ![1, 0, 2, 3]).mono V.quarticOriginalPairComparison_component_cost

theorem quarticOriginalPairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.quarticPairModels k).RealGroup)
    (hz : z ∈ (V.quarticPairModels k).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1)) (x : (V.quarticPairModels k).Space) :
    (V.quarticOriginalPairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.quarticOriginalPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.quarticOriginalPairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact W.quarticPairComponent_vertical a id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.quarticPairComponent_vertical b ![1, 0, 2, 3]) z hz x

variable [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

noncomputable def quarticOriginalPairComparisonNiltest (a b : Fin W.outputDim) :
    (pi V.quarticPairModels).Niltest (fun _ : Fin 4 => 1) :=
  piNiltest V.quarticPairModels (V.quarticOriginalPairComparisonTests a b)
    ((by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le)
    (by simpa using (show (3 : ℝ) ≤ quarticPairBudget (tensorPowerBudget 6 p) q from
      (by norm_num : (3 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le))
    (V.quarticOriginalPairComparisonTests_complexity a b)

theorem quarticOriginalPairComparisonNiltest_complexity (a b : Fin W.outputDim) :
    (V.quarticOriginalPairComparisonNiltest a b).ComplexityLE
      (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q)) :=
  piNiltest_complexity V.quarticPairModels (V.quarticOriginalPairComparisonTests a b) _ _ _

theorem quarticOriginalPairComparisonNiltest_orbit (a b : Fin W.outputDim) :
    (V.quarticOriginalPairComparisonNiltest a b).orbit = V.quarticPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun k => (V.quarticPairModels k).filtration))
  funext k
  cases k with
  | none => rfl
  | some k => fin_cases k <;> rfl

theorem quarticOriginalPairComparisonNiltest_observable (a b : Fin W.outputDim)
    (x : (pi V.quarticPairModels).Space) :
    (V.quarticOriginalPairComparisonNiltest a b).observable x =
      W.vertical.observable a (productProjection V.quarticPairModels (some 0) x) *
        star (W.vertical.observable b (productProjection V.quarticPairModels (some 1) x)) := by
  change (∏ k, (V.quarticOriginalPairComparisonTests a b k).observable
    (productProjection V.quarticPairModels k x)) = _
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change 1 * (W.vertical.observable a
    (productProjection V.quarticPairModels (some 0) x) *
      star (W.vertical.observable b (productProjection V.quarticPairModels (some 1) x))) = _
  exact one_mul _

theorem quarticOriginalPairComparisonNiltest_vertical (a b : Fin W.outputDim)
    (z : (pi V.quarticPairModels).RealGroup)
    (hz : z ∈ (pi V.quarticPairModels).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1)) (x : (pi V.quarticPairModels).Space) :
    (V.quarticOriginalPairComparisonNiltest a b).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.quarticOriginalPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * (V.quarticOriginalPairComparisonNiltest a b).observable x :=
  piNiltest_vertical V.quarticPairModels (V.quarticOriginalPairComparisonTests a b)
    V.quarticOriginalPairFrequencies _ _ _ (V.quarticOriginalPairComparisonTests_vertical a b) z hz x

end NativeSampleCorrelation

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

theorem quartic_original_pair_comparison_invariant (a b : Fin W.outputDim)
    (z : (pi V.quarticPairModels).RealGroup)
    (hz : z.coord ∈ (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer
      R.subalgebra (∑ _ : QuarticReplicatedIndex, 1)) (x : (pi V.quarticPairModels).Space) :
    (V.quarticOriginalPairComparisonNiltest a b).observable (z • x) =
      (V.quarticOriginalPairComparisonNiltest a b).observable x := by
  have htop : z ∈ (pi V.quarticPairModels).filtration.realification.subgroup
      (∑ _ : QuarticReplicatedIndex, 1) :=
    (pi V.quarticPairModels).filtration.realGradedRefiltrationLayer_le R.subalgebra _ hz
  rw [V.quarticOriginalPairComparisonNiltest_vertical a b z htop,
    V.quarticOriginalPairFrequency_real, R.quartic_original_pair_top_agreement z.coord hz,
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

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

noncomputable def quarticPairFrozenVector (k : Fin 2)
    (a b : (pi V.quarticPairModels).RealGroup) (out : Fin W.outputDim)
    (x : Fin 4 → ℤ) : ℂ :=
  W.vertical.observable out (productProjection V.quarticPairModels (some k)
    (QuotientGroup.mk (R.frozenMiddleValue a b x)))

theorem quarticPairFrozenVector_unit (k : Fin 2)
    (a b : (pi V.quarticPairModels).RealGroup) (x : Fin 4 → ℤ) :
    ∑ out, ‖R.quarticPairFrozenVector k a b out x‖ ^ 2 = 1 :=
  W.vertical.unit _

def HasQuarticPairFrozenEquivalence (u b : ℝ) : Prop :=
  ∀ m : ℕ, 0 < m → (m : ℝ) ≤ Real.exp u →
    ∀ a r : (pi V.quarticPairModels).RealGroup,
      (∀ i, |((pi V.quarticPairModels).basis.baseChange ℝ).repr a.coord i| ≤ Real.exp u) →
      ((pi V.quarticPairModels).basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m →
      NativeIntegerVectorEquivalence 3 b (R.quarticPairFrozenVector 0 a r) (R.quarticPairFrozenVector 1 a r)

end NativePolynomialOrbitFactors

theorem exists_quartic_frozen_equivalence_budget (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p q r u : ℝ, 0 ≤ p → 0 ≤ q → 0 ≤ r → 0 ≤ u →
      ∃ t : ℝ, 0 ≤ t ∧ r ≤ t ∧ u ≤ t ∧ p ≤ t ∧
        productNiltestBudget (quarticPairBudget p q) ≤ t ∧
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
  have hBt : quarticPairBudget p q ≤ b := by
    dsimp [quarticPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ quarticPairBudget p q := by
    unfold quarticPairBudget raisedNiltestBudget
    positivity
  have hprodmono : productNiltestBudget (quarticPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (quarticPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  exact ⟨t, ht, hrt, hut, hpt, htest, hsum⟩

theorem exists_quartic_pair_frozen_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)],
      0 ≤ r → 0 ≤ u → R.HasQuarticPairFrozenEquivalence u ((tensorPowerBudget 6 p + q + r + u + C) ^ C) := by
  obtain ⟨a, _, hfrozen⟩ := exists_native_frozen_middle_expansion 3
  obtain ⟨C, hC, hbudget⟩ := exists_quartic_frozen_equivalence_budget a
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R _ _ _ _ hr hu m hm hmb left right hleft hright
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  have hpk : p ≤ tensorPowerBudget 6 p := (tensorPowerBudget_bounds 6 hp).1
  obtain ⟨t, ht, hrt, hut, hpt, htest, hsum⟩ :=
    hbudget (tensorPowerBudget 6 p) q r u (hp.trans hpk) hq hr hu
  have htC : t ≤ (tensorPowerBudget 6 p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcost : (t + a) ^ a ≤ (tensorPowerBudget 6 p + q + r + u + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hsum
  have hdim : (Fintype.card (Fin W.outputDim) : ℝ) ≤ Real.exp ((tensorPowerBudget 6 p + q + r + u + C) ^ C) := by
    simpa only [Fintype.card_fin] using W.output_bound.trans (Real.exp_le_exp.mpr (hpk.trans (hpt.trans htC)))
  refine ⟨hdim, hdim, ?_⟩
  intro out₀ out₁
  have hN : ∀ _k : Fin 4, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨F⟩ := hfrozen (pi V.quarticPairModels) (R.mono hrt hN)
    (V.quarticOriginalPairComparisonNiltest out₀ out₁) ht ((V.quarticOriginalPairComparisonNiltest_complexity out₀ out₁).mono htest)
    (R.quartic_original_pair_comparison_invariant out₀ out₁) m hm (hmb.trans (Real.exp_le_exp.mpr hut)) left right
    (fun k => (hleft k).trans (Real.exp_le_exp.mpr hut)) hright
  have hF : Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3
      ((tensorPowerBudget 6 p + q + r + u + C) ^ C) (fun x =>
        (V.quarticOriginalPairComparisonNiltest out₀ out₁).observable
          (QuotientGroup.mk (R.frozenMiddleValue left right x)))) :=
    ⟨F.mono hcost⟩
  have heq : (fun x : Fin 4 → ℤ =>
      (V.quarticOriginalPairComparisonNiltest out₀ out₁).observable
        (QuotientGroup.mk (R.frozenMiddleValue left right x))) =
      (fun x => R.quarticPairFrozenVector 0 left right out₀ x *
        star (R.quarticPairFrozenVector 1 left right out₁ x)) := by
    funext x
    rw [V.quarticOriginalPairComparisonNiltest_observable]
    rfl
  exact (congrArg (fun f : (Fin 4 → ℤ) → ℂ =>
    Nonempty (NativeIntegerExpansion (fun _ : Fin 4 => 1) 3
      ((tensorPowerBudget 6 p + q + r + u + C) ^ C) f)) heq).mp hF

end Erdos3

end

end OAI

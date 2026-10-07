import OAI.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
import OAI.Combinatorics.Progressions.Geometry.MixedPairCoordinateTest

namespace OAI

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

noncomputable def mixedPairAnchoredVector (y : Fin (n + 2) → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ℂ :=
  R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

def HasMixedPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin (n + 2) → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
          R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

theorem hasMixedPairLocalApproximation_mono {a b : ℝ}
    (h : R.HasMixedPairLocalApproximation a) (hab : a ≤ b) : R.HasMixedPairLocalApproximation b := by
  obtain ⟨P, hP, hPb, hlocal⟩ := h
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  exact (hlocal y hy k out x δ hδ hx hres hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) hδ)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.MixedPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.MixedPairAlgebra)]

theorem mixedPairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) :
    W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) =
      R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  have hpoly : V.mixedPairPolynomial =
      ⟨⟨(V.mixedPairCoordinateNiltest k out).orbit.log,
        (V.mixedPairCoordinateNiltest k out).orbit.property⟩⟩ := by
    rw [V.mixedPairCoordinateNiltest_orbit]
    exact V.mixedPairPolynomial_eq_test
  calc
    _ = (V.mixedPairCoordinateNiltest k out).eval x :=
      (V.mixedPairCoordinateNiltest_eval k out x).symm
    _ = _ := (R.eval_niltest (V.mixedPairCoordinateNiltest k out) hpoly x).trans
      (V.mixedPairCoordinateNiltest_observable k out _)

theorem mixedPairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin (n + 2) → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.mixedPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.mixedPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.mixedPairModels).basis.baseChange ℝ)
    ‖W.eval out (mixedSlotInput (x (![0, 1] k)) (x (![1, 0] k)) (fun j => x j.succ.succ)) -
        R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.mixedPairModels
  let T := V.mixedPairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin (n + 2) => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) := by
    have h := T.observable_budget (V.mixedPairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.mixedPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.mixedPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.mixedPairCoordinateNiltest_observable, mixedPairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.mixedPairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_mixed_pair_local_approximation (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairLocalApproximation ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control
    (∑ _ : MixedReplicatedIndex (n + 1), 1)
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + Polynomial.C (n + 2)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r m W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := tensorPowerBudget m p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + ((n + 2 : ℕ) : ℝ)
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : tensorPowerBudget m p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have hdim : (0 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin (n + 2)) : ℝ) ≤ t := by
    simp only [Fintype.card_fin]
    dsimp [t]
    linarith
  have hBt : mixedPairBudget (tensorPowerBudget m p) q ≤ b := by
    dsimp [mixedPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ mixedPairBudget (tensorPowerBudget m p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.mixedPairBudget_six_le
  have hprodmono : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (mixedPairBudget (tensorPowerBudget m p) q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  let D := pi V.mixedPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.mixedPairNiltest_complexity).1.mono D htest
  have hN : ∀ _k : Fin (n + 2), (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.mixedPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.mixedPairFrozenVector_error k out x y (hcosets x y hres).1
  have hdist := hmotion x y δ hδ hx hy hnear
  apply herror.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((t + a) ^ a) * δ) :=
      mul_le_mul (Real.exp_le_exp.mpr htest) hdist
        (@dist_nonneg D.RealGroup
          (rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
            (D.basis.baseChange ℝ)).toPseudoMetricSpace (R.slowValue x) (R.slowValue y))
        (Real.exp_nonneg t)
    _ = Real.exp (t + (t + a) ^ a) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcost) hδ

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

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

theorem hasMixedPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasMixedPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasMixedPairFrozenEquivalence u b := by
  intro den hm hmb left right hleft hright
  exact (h den hm hmb left right hleft hright).mono hab

def HasMixedPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasMixedPairFrozenEquivalence u b

theorem hasMixedPairFrozenReduction_mono {a b : ℝ}
    (h : R.HasMixedPairFrozenReduction a) (hab : a ≤ b) : R.HasMixedPairFrozenReduction b := by
  obtain ⟨u, hu, hua, houter, hequiv⟩ := h
  exact ⟨u, hu, hua.trans hab, houter, R.hasMixedPairFrozenEquivalence_mono hequiv hab⟩

theorem mixedPairFrozenEquivalence_at {b : ℝ} (h : R.HasMixedPairFrozenReduction b)
    (x : Fin (n + 2) → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence (n + 1) b
      (R.mixedPairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.mixedPairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨den, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv den hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_mixed_pair_frozen_reduction (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ} {m : ℕ} [NeZero m]
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r), 0 ≤ r →
      R.HasMixedPairFrozenReduction ((tensorPowerBudget m p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_mixed_pair_outer_control n
  obtain ⟨B, _, hfrozen⟩ := exists_mixed_pair_frozen_equivalence n
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r m _ W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget m p := hW.trans (tensorPowerBudget_bounds m hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget m p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (tensorPowerBudget m p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.MixedPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.MixedPairAlgebra) :=
    IsModuleTopology.isTopologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.mixedPairModels).basis
  exact ⟨u, hu, huC, houter (W := W.tensorPower m) (V := V) R hr,
    R.hasMixedPairFrozenEquivalence_mono (hfrozen (W := W) (V := V) R hr hu) hBC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

def mixedPairPartitionErrorBudget (n : ℕ) : ℕ := 12 * (n + 2) + 12

namespace NativePolynomialOrbitFactors

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
    V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
    (fun _ : Fin (n + 2) => (N : ℝ)) r)

theorem mixedPairAnchoredVector_norm (y : Fin (n + 2) → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin (n + 2) → ℤ) : ‖R.mixedPairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

theorem select_mixed_pair_local_partition {b c : ℝ}
    (hlocal : R.HasMixedPairLocalApproximation b) (hred : R.HasMixedPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin (n + 2) → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin (n + 2) → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence (n + 1) c
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ (k : Fin 2) (out : Fin W.outputDim),
            (𝔼 x : Fin (n + 2) → ZMod N,
              ∑ j, A j x * ‖W.eval out
                (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ)
                  (fun j => ((x j.succ.succ).val : ℤ))) -
                  R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) k out
                    (fun i => ((x i).val : ℤ))‖) ≤
              Real.exp b * ρ + 2 * ((n + 2 : ℕ) : ℝ) * B.card / N := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) => ((x i).val : ℤ)
  have hv (x : Fin (n + 2) → ZMod N) (i : Fin (n + 2)) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin (n + 2) → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.mixedPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro k out
  let F := fun x : Fin (n + 2) → ZMod N => W.eval out (mixedSlotInput (v x (![0, 1] k)) (v x (![1, 0] k)) (fun j => v x j.succ.succ))
  let G := fun j (x : Fin (n + 2) → ZMod N) => R.mixedPairAnchoredVector (v (y j)) k out (v x)
  let E := coordinateExceptional (ι := Fin (n + 2)) B
  have hpoint (j : I) (x : Fin (n + 2) → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - G j x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hmodel (v (y j)) (hv (y j)) k out (v x) ρ hρ (hv x) hres
      (by simpa only [v, Int.cast_natCast] using hnear)
  have herr := weighted_partition_mean_error E A G F
    (mul_nonneg (Real.exp_nonneg b) hρ) hA hsum
    (fun j x => R.mixedPairAnchoredVector_norm _ _ _ _)
    (fun x => W.norm_eval out _) (fun j x hx hAx => hpoint j x hx hAx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin (n + 2) → ZMod N) ≤ ((n + 2 : ℕ) : ℝ) * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin (n + 2)) B
  have herr' : (𝔼 x : Fin (n + 2) → ZMod N, ∑ j, A j x * ‖F x - G j x‖) ≤
      Real.exp b * ρ + 2 * ((E.card : ℝ) / Fintype.card (Fin (n + 2) → ZMod N)) := by
    simpa only [mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + 2 * (((n + 2 : ℕ) : ℝ) * (B.card : ℝ) / N) := by gcongr
    _ = _ := by ring

end NativePolynomialOrbitFactors

theorem exists_mixed_pair_local_partition (n a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ P : ℕ, ∃ hP : 0 < P,
        letI : NeZero P := ⟨hP.ne'⟩
        (P : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ cells : ℕ, 0 < cells ∧
          (Fintype.card (Fin (n + 2) → Fin cells × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
          ∃ A : (Fin cells × ZMod P) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            ∃ y : (Fin (n + 2) → Fin cells × ZMod P) → (Fin (n + 2) → ZMod N),
              (∀ j, NativeIntegerVectorEquivalence (n + 1) ((t + C) ^ C)
                (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
                (R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
              ∀ (k : Fin 2) (out : Fin W.outputDim),
                (𝔼 x : Fin (n + 2) → ZMod N,
                  ∑ j, (∏ i, A (j i) (x i) : ℝ) * ‖W.eval out
                    (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ)
                  (fun j => ((x j.succ.succ).val : ℤ))) -
                      R.mixedPairAnchoredVector (fun i => ((y j i).val : ℤ)) k out
                        (fun i => ((x i).val : ℤ))‖) ≤
                  Real.exp (t + mixedPairPartitionErrorBudget n) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Polynomial.C (mixedPairPartitionErrorBudget n) +
      Polynomial.C (n + 2) * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t m W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_mixed_pair_local_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨cells, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + mixedPairPartitionErrorBudget n + ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have hdim : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 2 by omega)
  have hK : (0 : ℝ) ≤ mixedPairPartitionErrorBudget n := Nat.cast_nonneg _
  have hmul : 0 ≤ ((n + 2 : ℕ) : ℝ) * (t + B) ^ B := mul_nonneg (by linarith) hpow
  have htC : t ≤ (t + C) ^ C := by linarith
  have hdimCost : ((n + 2 : ℕ) : ℝ) * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C :=
    (le_mul_of_one_le_left hpow hdim).trans hdimCost
  let w := productPartitionWeight (fun _ : Fin (n + 2) => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin (n + 2) => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨y, hequiv, herr⟩ := hselect E w hρ.le hw hwSum hcells
  refine ⟨P, hP, hPt.trans (Real.exp_le_exp.mpr htC), cells, hn, ?_, A,
    fun j => (hA j).mono le_rfl hcost, hsum, y,
    fun j => (hequiv j).mono (hct.trans htC), ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ (n + 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard (n + 2)
      _ = Real.exp (((n + 2 : ℕ) : ℝ) * (t + B) ^ B) := (Real.exp_nat_mul _ (n + 2)).symm
      _ ≤ _ := Real.exp_le_exp.mpr hdimCost
  · intro k out
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    let d : ℝ := (n + 2 : ℕ)
    let K : ℝ := mixedPairPartitionErrorBudget n
    have hd : 0 ≤ d := Nat.cast_nonneg _
    have hKexp : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
    have hcoeff : 1 + 12 * d ≤ K := by
      dsimp [d, K, mixedPairPartitionErrorBudget]
      push_cast
      linarith
    have hcoeff' : 6 * d ≤ K := by linarith
    have hscaleD : 2 * d ≤ 2 * d * Real.exp t :=
      le_mul_of_one_le_right (by positivity) (Real.one_le_exp ht)
    apply (herr k out).trans
    calc
      _ = Real.exp b * ρ + 2 * d * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp t * ρ + 2 * d * (6 * ρ + 3 / N) := by gcongr
      _ ≤ Real.exp t * ρ + 2 * d * Real.exp t * (6 * ρ + 3 / N) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hscaleD
          (by positivity : (0 : ℝ) ≤ 6 * ρ + 3 / N))
      _ = Real.exp t * ((1 + 12 * d) * ρ + (6 * d) * (1 / N)) := by ring
      _ ≤ Real.exp t * (K * ρ + K * (1 / N)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_right hcoeff hρ.le)
            (mul_le_mul_of_nonneg_right hcoeff' hN)) (Real.exp_nonneg t)
      _ = K * Real.exp t * (ρ + 1 / N) := by ring
      _ ≤ Real.exp K * Real.exp t * (ρ + 1 / N) := by gcongr
      _ = Real.exp (t + mixedPairPartitionErrorBudget n) * (ρ + 1 / N) := by
        rw [← Real.exp_add, add_comm K t]
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

section Data

variable {n m : ℕ} {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p} {i j : Fin (W.tensorPower m).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}

structure NativeMixedPairPartition
    (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin (n + 2) → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin (n + 2) → I) → (Fin (n + 2) → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence (n + 1) b
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.mixedPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin (n + 2) → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (mixedSlotInput ((x (![0, 1] k)).val : ℤ) ((x (![1, 0] k)).val : ℤ)
                  (fun j => ((x j.succ.succ).val : ℤ))) -
          R.mixedPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeMixedPairPartition.finite

noncomputable def NativeMixedPairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
      V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
      (fun _ : Fin (n + 2) => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativeMixedPairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativeMixedPairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    weighted_approximation := fun k out => (P.weighted_approximation k out).trans hεδ }

end Data

theorem exists_mixed_pair_precise_partition (n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ} {m : ℕ}
      {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower m).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
        Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower m).mixedAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.mixedPairModels)
        V.mixedPairPolynomial (piFrequency V.mixedPairFrequencies)
        (fun _ : Fin (n + 2) => (N : ℝ)) r),
      R.HasMixedPairLocalApproximation b → R.HasMixedPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeMixedPairPartition R ((t + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨A, _, hpartition⟩ := exists_mixed_pair_local_partition n 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + Polynomial.C (mixedPairPartitionErrorBudget n + 40)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e m W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + ((mixedPairPartitionErrorBudget n + 40 : ℕ) : ℝ)
  have hK : (0 : ℝ) ≤ mixedPairPartitionErrorBudget n := Nat.cast_nonneg _
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : (u + A) ^ A + 2 * u ≤ (t + e + C) ^ C := by
    simpa [T, X, u, Polynomial.eval₂_pow] using hbudget (t + e) (add_nonneg ht he)
  have hcost : (u + A) ^ A ≤ (t + e + C) ^ C := by linarith
  have hscale : 2 * u ≤ (t + e + C) ^ C := by
    have : 0 ≤ (u + A) ^ A := by positivity
    linarith
  let ρ := Real.exp (-(2 * u))
  have hρ : 0 < ρ := Real.exp_pos _
  have hprec : 1 / ρ ≤ Real.exp ((u + 2) ^ 2) := by
    dsimp [ρ]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg u]
  obtain ⟨P, hP, hPb, cells, hn, hcard, weight, hpositive, htotal, anchor, hequiv, herr⟩ :=
    hpartition R hlocal hred hu (hbt.trans (by dsimp [u]; push_cast; linarith))
      (hct.trans (by dsimp [u]; push_cast; linarith)) hρ hprec
  let : NeZero P := ⟨hP.ne'⟩
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  have herror : Real.exp (u + mixedPairPartitionErrorBudget n) * (ρ + 1 / N) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (u + mixedPairPartitionErrorBudget n) * (2 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
      _ = 2 * Real.exp (mixedPairPartitionErrorBudget n - u) := by
        dsimp [ρ]
        rw [← mul_assoc, mul_comm (Real.exp (u + mixedPairPartitionErrorBudget n)) 2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * (Real.exp (-e) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (Real.exp_le_exp.mpr (show (mixedPairPartitionErrorBudget n : ℝ) - u ≤ -e - 1 by dsimp [u]; push_cast; linarith)).trans
        exact exp_sub_one_le_half_exp (-e)
      _ = _ := by ring
  exact ⟨{
    I := Fin cells × ZMod P
    card_bound := hcard.trans (Real.exp_le_exp.mpr hcost)
    weight := weight
    positive := fun j => (hpositive j).mono le_rfl hcost
    total := htotal
    anchor := anchor
    equivalence := fun j => (hequiv j).mono hcost
    weighted_approximation := fun k out => (herr k out).trans herror }⟩

end Erdos3

end

end OAI

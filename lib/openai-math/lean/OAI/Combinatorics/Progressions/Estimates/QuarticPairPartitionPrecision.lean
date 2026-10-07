/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.CubicPairPartitionPrecision
import OAI.Combinatorics.Progressions.Geometry.QuarticPairCoordinateTest

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quartic_pair_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control 4 4
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 3
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : quarticPairBudget p q ≤ b := by
    dsimp [quarticPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ quarticPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  have hprodmono : productNiltestBudget (quarticPairBudget p q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (quarticPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.quarticPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.quarticPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ quarticPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le))
      (fun k => (V.quarticPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin 4, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hout : R.HasOuterValueControl ((t + a) ^ a) :=
    hcontrol (R.mono hrt hN) ht hD hN (by simp)
  exact R.hasOuterValueControl_mono hout hcost

end Erdos3

end

section

namespace Erdos3.NativePolynomialOrbitFactors

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

noncomputable def quarticPairAnchoredVector (y : Fin 4 → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 4 → ℤ) : ℂ :=
  R.quarticPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

def HasQuarticPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin 4 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin 4 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (quarticInput (x (![0, 1] k)) ![x (![1, 0] k), x 2, x 3]) -
          R.quarticPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

theorem hasQuarticPairLocalApproximation_mono {a b : ℝ}
    (h : R.HasQuarticPairLocalApproximation a) (hab : a ≤ b) : R.HasQuarticPairLocalApproximation b := by
  obtain ⟨P, hP, hPb, hlocal⟩ := h
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  exact (hlocal y hy k out x δ hδ hx hres hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) hδ)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

theorem quarticPairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin 4 → ℤ) :
    W.eval out (quarticInput (x (![0, 1] k)) ![x (![1, 0] k), x 2, x 3]) =
      R.quarticPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  have hpoly : V.quarticPairPolynomial =
      ⟨⟨(V.quarticPairCoordinateNiltest k out).orbit.log,
        (V.quarticPairCoordinateNiltest k out).orbit.property⟩⟩ := by
    rw [V.quarticPairCoordinateNiltest_orbit]
    exact V.quarticPairPolynomial_eq_test
  calc
    _ = (V.quarticPairCoordinateNiltest k out).eval x :=
      (V.quarticPairCoordinateNiltest_eval k out x).symm
    _ = _ := (R.eval_niltest (V.quarticPairCoordinateNiltest k out) hpoly x).trans
      (V.quarticPairCoordinateNiltest_observable k out _)

theorem quarticPairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin 4 → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.quarticPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.quarticPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.quarticPairModels).basis.baseChange ℝ)
    ‖W.eval out (quarticInput (x (![0, 1] k)) ![x (![1, 0] k), x 2, x 3]) -
        R.quarticPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.quarticPairModels
  let T := V.quarticPairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q)) := by
    have h := T.observable_budget (V.quarticPairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.quarticPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.quarticPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.quarticPairCoordinateNiltest_observable, quarticPairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.quarticPairFrozenVector_diagonal k out x] using hraw

end Erdos3.NativePolynomialOrbitFactors

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_quartic_pair_local_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r), 0 ≤ r →
      R.HasQuarticPairLocalApproximation ((tensorPowerBudget 6 p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control 4
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget 6 p := hW.trans (tensorPowerBudget_bounds 6 hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := tensorPowerBudget 6 p + q + r
  let b := 4 * (u + 1) + raisedNiltestBudget u + 6
  let t := productNiltestBudget b + u + 4
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : tensorPowerBudget 6 p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have htwo : (Fintype.card (Fin 4) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  have hBt : quarticPairBudget (tensorPowerBudget 6 p) q ≤ b := by
    dsimp [quarticPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ quarticPairBudget (tensorPowerBudget 6 p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  have hprodmono : productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (tensorPowerBudget 6 p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (tensorPowerBudget 6 p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.quarticPairModels).basis
  let D := pi V.quarticPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.quarticPairNiltest_complexity).1.mono D htest
  have hN : ∀ _k : Fin 4, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.quarticPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.quarticPairFrozenVector_error k out x y (hcosets x y hres).1
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

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

theorem hasQuarticPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasQuarticPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasQuarticPairFrozenEquivalence u b := by
  intro m hm hmb left right hleft hright
  exact (h m hm hmb left right hleft hright).mono hab

def HasQuarticPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasQuarticPairFrozenEquivalence u b

theorem hasQuarticPairFrozenReduction_mono {a b : ℝ}
    (h : R.HasQuarticPairFrozenReduction a) (hab : a ≤ b) : R.HasQuarticPairFrozenReduction b := by
  obtain ⟨u, hu, hua, houter, hequiv⟩ := h
  exact ⟨u, hu, hua.trans hab, houter, R.hasQuarticPairFrozenEquivalence_mono hequiv hab⟩

theorem quarticPairFrozenEquivalence_at {b : ℝ} (h : R.HasQuarticPairFrozenReduction b)
    (x : Fin 4 → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence 3 b
      (R.quarticPairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.quarticPairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨m, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv m hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_quartic_pair_frozen_reduction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r), 0 ≤ r →
      R.HasQuarticPairFrozenReduction ((tensorPowerBudget 6 p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_quartic_pair_outer_control
  obtain ⟨B, _, hfrozen⟩ := exists_quartic_pair_frozen_equivalence
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget 6 p := hW.trans (tensorPowerBudget_bounds 6 hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (tensorPowerBudget 6 p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (tensorPowerBudget 6 p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (tensorPowerBudget 6 p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.quarticPairModels).basis
  exact ⟨u, hu, huC, houter (W := W.tensorPower 6) (V := V) R hr,
    R.hasQuarticPairFrozenEquivalence_mono (hfrozen (W := W) (V := V) R hr hu) hBC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativePolynomialOrbitFactors.FrozenMiddleRealization

variable {p q r b : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r}
  [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.quarticPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

noncomputable def quarticPairMiddleTest (k : Fin 2) (out : Fin W.outputDim) :
    M.model.Niltest (fun _ : Fin 4 => 1) :=
  M.pullTest (V.quarticPairCoordinateNiltest k out) (fun x => by
    rw [V.quarticPairCoordinateNiltest_observable]
    exact W.vertical.norm out _)

theorem quarticPairMiddleTest_eval (k : Fin 2) (out : Fin W.outputDim) (x : Fin 4 → ℤ) :
    (M.quarticPairMiddleTest k out).eval x = R.quarticPairFrozenVector k a c out x := by
  rw [quarticPairMiddleTest, M.pullTest_eval, V.quarticPairCoordinateNiltest_observable]
  rfl

theorem quarticPairMiddleTest_unit (k : Fin 2) (x : M.model.Space) :
    ∑ out, ‖(M.quarticPairMiddleTest k out).observable x‖ ^ 2 = 1 := by
  change ∑ out, ‖(V.quarticPairCoordinateNiltest k out).observable (M.spaceMap x)‖ ^ 2 = 1
  simp only [V.quarticPairCoordinateNiltest_observable]
  exact W.vertical.unit _

theorem quarticPairMiddleTest_complexity (hb : 0 ≤ b) (k : Fin 2) (out : Fin W.outputDim) :
    (M.quarticPairMiddleTest k out).ComplexityLE
      (productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) + b + 4) := by
  apply M.pullTest_complexity _ _ _ hb (V.quarticPairCoordinateNiltest_complexity k out)
  have hB : 0 ≤ quarticPairBudget (tensorPowerBudget 6 p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  unfold productNiltestBudget productObservableLipBudget
  positivity

theorem quarticPairMiddleTest_common_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1))
    (x : M.model.Space) :
    (M.quarticPairMiddleTest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency
          (realificationLieHom (V.quarticOriginalPairProjection 0)
            (realificationLieHom
              ((pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
              z.coord)) : ℝ) : CircleFourier.Circle) *
      (M.quarticPairMiddleTest k out).observable x := by
  let D := pi V.quarticPairModels
  let φ := realificationMap (hnil := M.model.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have htop : φ z ∈ D.filtration.realification.subgroup (∑ _ : QuarticReplicatedIndex, 1) :=
    D.filtration.realGradedRefiltrationLayer_le R.subalgebra _ (M.inclusion_mem_top z hz)
  have heq := R.quartic_original_pair_top_agreement (φ z).coord (M.inclusion_mem_top z hz)
  change (V.quarticPairCoordinateNiltest k out).observable (M.spaceMap (z • x)) = _
  rw [M.spaceMap_top_smul z hz, V.quarticPairCoordinateNiltest_observable,
    productProjection_smul]
  have hv := W.quarticPairComponent_vertical out id
    (productProjectionHom V.quarticPairModels (some k) (φ z))
    (productProjectionHom_mem_layer V.quarticPairModels (some k) _ (φ z) htop)
    (productProjection V.quarticPairModels (some k) (M.spaceMap x))
  change W.vertical.observable out _ = _ at hv
  refine hv.trans ?_
  change CircleFourier.character
      ((realifyFunctional W.vertical.frequency
        (realificationLieHom (V.quarticOriginalPairProjection k) (φ z).coord) : ℝ) :
        CircleFourier.Circle) * W.vertical.observable out _ = _
  have hphase : realifyFunctional W.vertical.frequency
      (realificationLieHom (V.quarticOriginalPairProjection k) (φ z).coord) =
    realifyFunctional W.vertical.frequency
      (realificationLieHom (V.quarticOriginalPairProjection 0) (φ z).coord) := by
    fin_cases k
    · rfl
    · exact heq.symm
  rw [hphase]
  congr 1
  exact (V.quarticPairCoordinateNiltest_observable k out (M.spaceMap x)).symm

end NativePolynomialOrbitFactors.FrozenMiddleRealization

theorem exists_quartic_pair_middle_model :
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
      [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ r → 0 ≤ u → R.HasOuterValueControl u → ∀ y : Fin 4 → ℤ,
      (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
      ∃ M : R.FrozenMiddleRealization (R.slowValue y) (R.rationalValue y)
          ((tensorPowerBudget 6 p + q + r + u + C) ^ C),
        (∀ k out, (M.quarticPairMiddleTest k out).ComplexityLE ((tensorPowerBudget 6 p + q + r + u + C) ^ C)) ∧
        (∀ k out x, (M.quarticPairMiddleTest k out).eval x = R.quarticPairAnchoredVector y k out x) := by
  obtain ⟨a, _, hmodel⟩ := exists_native_frozen_middle_realization 4
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j V R _ _ _ _ _ _ _ _ hr hu houter y hy
  have hW : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hp : 0 ≤ tensorPowerBudget 6 p := hW.trans (tensorPowerBudget_bounds 6 hW).1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := tensorPowerBudget 6 p + q + r + u
  let b := 4 * (v + 1) + raisedNiltestBudget v + 6
  let t := productNiltestBudget b + v + 4
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hpqv : tensorPowerBudget 6 p + q ≤ v := by dsimp [v]; linarith
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, v]; linarith
  have hut : u ≤ t := by dsimp [t, v]; linarith
  have hBt : quarticPairBudget (tensorPowerBudget 6 p) q ≤ b := by
    dsimp [quarticPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ quarticPairBudget (tensorPowerBudget 6 p) q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.quarticPairBudget_six_le
  have hprodmono : productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) ≤ productNiltestBudget b :=
    productNiltestBudget_mono hB0 hBt
  have htest : productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a + 4 ≤ (tensorPowerBudget 6 p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have hcost : (t + a) ^ a ≤ (tensorPowerBudget 6 p + q + r + u + C) ^ C := by linarith
  have hN : ∀ _k : Fin 4, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter
  obtain ⟨M⟩ := @hmodel V.QuarticPairAlgebra (Fin 4) _ _ _ _ _ _ _
    (pi V.quarticPairModels) _ _ _ t (R.mono hrt hN)
    (inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ]
      (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ]
      (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (T2Space (ℝ ⊗[ℚ]
      (pi V.quarticPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra))) ht
    (V.quarticPairNiltest_complexity.mono htest).1
    m hm (hmb.trans (Real.exp_le_exp.mpr hut)) (R.slowValue y) (R.rationalValue y)
    (fun k => (hslow y hy k).trans (Real.exp_le_exp.mpr hut)) (hrat y)
  rcases M with ⟨D', hD'F, hD', hinc, orbit, hzero, heval, f, hf, K, hK, hLip⟩
  let M' : R.FrozenMiddleRealization (R.slowValue y) (R.rationalValue y) ((t + a) ^ a) :=
    ⟨D', hD'F, hD', hinc, orbit, hzero, heval, f, hf, K, hK, hLip⟩
  refine ⟨M'.mono hcost, ?_, ?_⟩
  · intro k out
    exact (M'.quarticPairMiddleTest_complexity (by positivity) k out).mono
      ((by linarith : productNiltestBudget (quarticPairBudget (tensorPowerBudget 6 p) q) + (t + a) ^ a + 4 ≤
        t + (t + a) ^ a + 4).trans hsum)
  · intro k out x
    exact (M'.mono hcost).quarticPairMiddleTest_eval k out x

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

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
  (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
    V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
    (fun _ : Fin 4 => (N : ℝ)) r)

theorem quarticPairAnchoredVector_norm (y : Fin 4 → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin 4 → ℤ) : ‖R.quarticPairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

theorem select_quartic_pair_local_partition {b c : ℝ}
    (hlocal : R.HasQuarticPairLocalApproximation b) (hred : R.HasQuarticPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 4 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 4 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 3 c
            (R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ (k : Fin 2) (out : Fin W.outputDim),
            (𝔼 x : Fin 4 → ZMod N,
              ∑ j, A j x * ‖W.eval out
                (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) -
                  R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) k out
                    (fun i => ((x i).val : ℤ))‖) ≤
              Real.exp b * ρ + 8 * B.card / N := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 4 → ZMod N) (i : Fin 4) => ((x i).val : ℤ)
  have hv (x : Fin 4 → ZMod N) (i : Fin 4) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 4 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.quarticPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro k out
  let F := fun x : Fin 4 → ZMod N => W.eval out (quarticInput (v x (![0, 1] k)) ![v x (![1, 0] k), v x 2, v x 3])
  let G := fun j (x : Fin 4 → ZMod N) => R.quarticPairAnchoredVector (v (y j)) k out (v x)
  let E := coordinateExceptional (ι := Fin 4) B
  have hpoint (j : I) (x : Fin 4 → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - G j x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hmodel (v (y j)) (hv (y j)) k out (v x) ρ hρ (hv x) hres
      (by simpa only [v, Int.cast_natCast] using hnear)
  have herr := weighted_partition_mean_error E A G F
    (mul_nonneg (Real.exp_nonneg b) hρ) hA hsum
    (fun j x => R.quarticPairAnchoredVector_norm _ _ _ _)
    (fun x => W.norm_eval out _) (fun j x hx hAx => hpoint j x hx hAx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin 4 → ZMod N) ≤ 4 * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin 4) B
  have herr' : (𝔼 x : Fin 4 → ZMod N, ∑ j, A j x * ‖F x - G j x‖) ≤
      Real.exp b * ρ + 2 * ((E.card : ℝ) / Fintype.card (Fin 4 → ZMod N)) := by
    simpa only [mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + 2 * (4 * (B.card : ℝ) / N) := by gcongr
    _ = _ := by ring

end NativePolynomialOrbitFactors

theorem exists_quartic_pair_local_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r),
      R.HasQuarticPairLocalApproximation b → R.HasQuarticPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ P : ℕ, ∃ hP : 0 < P,
        letI : NeZero P := ⟨hP.ne'⟩
        (P : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧
          (Fintype.card (Fin 4 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
          ∃ A : (Fin n × ZMod P) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            ∃ y : (Fin 4 → Fin n × ZMod P) → (Fin 4 → ZMod N),
              (∀ j, NativeIntegerVectorEquivalence 3 ((t + C) ^ C)
                (R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
                (R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
              ∀ (k : Fin 2) (out : Fin W.outputDim),
                (𝔼 x : Fin 4 → ZMod N,
                  ∑ j, (∏ i, A (j i) (x i) : ℝ) * ‖W.eval out
                    (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) -
                      R.quarticPairAnchoredVector (fun i => ((y j i).val : ℤ)) k out
                        (fun i => ((x i).val : ℤ))‖) ≤
                  Real.exp (t + 60) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + 4 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_quartic_pair_local_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + 4 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hfour : 4 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 4 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 4 => A) i j x :=
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
  refine ⟨P, hP, hPt.trans (Real.exp_le_exp.mpr htC), n, hn, ?_, A,
    fun j => (hA j).mono le_rfl hcost, hsum, y,
    fun j => (hequiv j).mono (hct.trans htC), ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 4
      _ = Real.exp (4 * (t + B) ^ B) := (Real.exp_nat_mul _ 4).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfour
  · intro k out
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have h60 : (60 : ℝ) ≤ Real.exp 60 := by linarith [Real.add_one_le_exp (60 : ℝ)]
    apply (herr k out).trans
    calc
      _ = Real.exp b * ρ + 8 * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp t * ρ + 8 * (6 * ρ + 3 / N) := by gcongr
      _ ≤ Real.exp t * ρ + 8 * Real.exp t * (6 * ρ + 3 / N) := by
        gcongr
        nlinarith [Real.one_le_exp ht]
      _ = Real.exp t * (49 * ρ + 24 * (1 / N)) := by ring
      _ ≤ Real.exp t * (60 * (ρ + 1 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg t)
      _ = 60 * Real.exp t * (ρ + 1 / N) := by ring
      _ ≤ Real.exp 60 * Real.exp t * (ρ + 1 / N) := by gcongr
      _ = Real.exp (t + 60) * (ρ + 1 / N) := by rw [← Real.exp_add, add_comm 60 t]

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

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}

structure NativeQuarticPairPartition
    (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
      V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
      (fun _ : Fin 4 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 4 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 4 → I) → (Fin 4 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 3 b
    (R.quarticPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.quarticPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 4 → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (quarticInput ((x (![0, 1] k)).val : ℤ) ![((x (![1, 0] k)).val : ℤ), ((x 2).val : ℤ), ((x 3).val : ℤ)]) -
          R.quarticPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeQuarticPairPartition.finite

noncomputable def NativeQuarticPairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
      V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
      (fun _ : Fin 4 => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativeQuarticPairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativeQuarticPairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    weighted_approximation := fun k out => (P.weighted_approximation k out).trans hεδ }

end Data

theorem exists_quartic_pair_precise_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin (W.tensorPower 6).outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
        Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ)))}
      (R : NativePolynomialOrbitFactors (pi V.quarticPairModels)
        V.quarticPairPolynomial (piFrequency V.quarticPairFrequencies)
        (fun _ : Fin 4 => (N : ℝ)) r),
      R.HasQuarticPairLocalApproximation b → R.HasQuarticPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeQuarticPairPartition R ((t + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨A, _, hpartition⟩ := exists_quartic_pair_local_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j V R hlocal hred ht he hbt hct hN
  let u := t + e + 100
  have hu : 0 ≤ u := by dsimp [u]; linarith
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
  obtain ⟨P, hP, hPb, n, hn, hcard, weight, hpositive, htotal, anchor, hequiv, herr⟩ :=
    hpartition R hlocal hred hu (hbt.trans (by dsimp [u]; linarith))
      (hct.trans (by dsimp [u]; linarith)) hρ hprec
  let : NeZero P := ⟨hP.ne'⟩
  have hrecip : 1 / (N : ℝ) ≤ ρ := by
    have hh := one_div_le_one_div_of_le (Real.exp_pos (2 * u))
      ((Real.exp_le_exp.mpr hscale).trans hN)
    simpa only [ρ, one_div, Real.exp_neg] using hh
  have herror : Real.exp (u + 60) * (ρ + 1 / N) ≤ Real.exp (-e) := by
    calc
      _ ≤ Real.exp (u + 60) * (2 * ρ) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg _)
      _ = 2 * Real.exp (60 - u) := by
        dsimp [ρ]
        rw [← mul_assoc, mul_comm (Real.exp (u + 60)) 2, mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ 2 * (Real.exp (-e) / 2) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply (Real.exp_le_exp.mpr (show 60 - u ≤ -e - 1 by dsimp [u]; linarith)).trans
        exact exp_sub_one_le_half_exp (-e)
      _ = _ := by ring
  exact ⟨{
    I := Fin n × ZMod P
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

/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Geometry.CubicPairCoordinateTest

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

theorem exists_cubic_pair_outer_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r), 0 ≤ r →
      R.HasOuterValueControl ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_outer_control 3 3
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j shift V R hr
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
  have hBt : cubicPairBudget p q ≤ b := by
    dsimp [cubicPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ cubicPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  have hprodmono : productNiltestBudget (cubicPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (cubicPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.cubicPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.cubicPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ cubicPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le))
      (fun k => (V.cubicPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin 3, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

noncomputable def cubicPairAnchoredVector (y : Fin 3 → ℤ)
    (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) : ℂ :=
  R.cubicPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x

def HasCubicPairLocalApproximation (b : ℝ) : Prop :=
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
    ∀ y : Fin 3 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
      ∀ (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.eval out (cubicTrilinearInput (x k.succ) (x k.rev.succ) (x 0 + shift)) -
          R.cubicPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤ Real.exp b * δ

theorem hasCubicPairLocalApproximation_mono {a b : ℝ}
    (h : R.HasCubicPairLocalApproximation a) (hab : a ≤ b) : R.HasCubicPairLocalApproximation b := by
  obtain ⟨P, hP, hPb, hlocal⟩ := h
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  exact (hlocal y hy k out x δ hδ hx hres hnear).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hab) hδ)

variable [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]

theorem cubicPairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) :
    W.eval out (cubicTrilinearInput (x k.succ) (x k.rev.succ) (x 0 + shift)) =
      R.cubicPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  have hpoly : V.cubicPairPolynomial =
      ⟨⟨(V.cubicPairCoordinateNiltest k out).orbit.log,
        (V.cubicPairCoordinateNiltest k out).orbit.property⟩⟩ := by
    rw [V.cubicPairCoordinateNiltest_orbit]
    exact V.cubicPairPolynomial_eq_test
  calc
    _ = (V.cubicPairCoordinateNiltest k out).eval x :=
      (V.cubicPairCoordinateNiltest_eval k out x).symm
    _ = _ := (R.eval_niltest (V.cubicPairCoordinateNiltest k out) hpoly x).trans
      (V.cubicPairCoordinateNiltest_observable k out _)

theorem cubicPairFrozenVector_error (k : Fin 2) (out : Fin W.outputDim) (x y : Fin 3 → ℤ)
    (hcoset : (QuotientGroup.mk (R.rationalValue x) : (pi V.cubicPairModels).Space) =
      QuotientGroup.mk (R.rationalValue y)) :
    letI := rightMetricSpace
      (hnil := (pi V.cubicPairModels).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi V.cubicPairModels).basis.baseChange ℝ)
    ‖W.eval out (cubicTrilinearInput (x k.succ) (x k.rev.succ) (x 0 + shift)) -
        R.cubicPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (cubicPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
  let D := pi V.cubicPairModels
  let T := V.cubicPairCoordinateNiltest k out
  let b := D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 3 => 1) (fun i => (x i : ℝ)) R.middle
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hright := D.observable_frozen_right_eq T.observable (R.slowValue x) b
    (R.rationalValue x) (R.rationalValue y) hcoset
  have hchange := D.frozen_observable_change_left T.observable T.lipschitz
    (R.slowValue x) (R.slowValue y) b (R.rationalValue y)
  rw [← hright] at hchange
  have hlip : (T.lipBound : ℝ) ≤ Real.exp (productNiltestBudget (cubicPairBudget p q)) := by
    have h := T.observable_budget (V.cubicPairCoordinateNiltest_complexity k out)
    linarith [T.normBound.coe_nonneg]
  have hraw : ‖R.cubicPairFrozenVector k (R.slowValue x) (R.rationalValue x) out x -
      R.cubicPairFrozenVector k (R.slowValue y) (R.rationalValue y) out x‖ ≤
      Real.exp (productNiltestBudget (cubicPairBudget p q)) *
        dist (R.slowValue x) (R.slowValue y) := by
    simpa only [T, V.cubicPairCoordinateNiltest_observable, cubicPairFrozenVector, frozenMiddleValue, b] using
      hchange.trans (mul_le_mul_of_nonneg_right hlip dist_nonneg)
  simpa only [← R.cubicPairFrozenVector_diagonal k out x] using hraw

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

theorem exists_cubic_pair_local_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r), 0 ≤ r →
      R.HasCubicPairLocalApproximation ((p + q + r + C) ^ C) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_local_control 3
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j shift V R hr
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
  have htwo : (Fintype.card (Fin 3) : ℝ) ≤ t := by norm_num; dsimp [t]; linarith
  have hBt : cubicPairBudget p q ≤ b := by
    dsimp [cubicPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ cubicPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  have hprodmono : productNiltestBudget (cubicPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (cubicPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hcost : t + (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hlocal : (t + a) ^ a ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left ht).trans hcost
  let : TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.cubicPairModels).basis
  let D := pi V.cubicPairModels
  have hD : D.GeometryComplexityLE t :=
    (V.cubicPairNiltest_complexity).1.mono D htest
  have hN : ∀ _k : Fin 3, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨P, hP, hPb, hcosets, hmotion⟩ := hcontrol (R.mono hrt hN) ht hD htwo hN
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hlocal), ?_⟩
  intro y hy k out x δ hδ hx hres hnear
  let : MetricSpace (pi V.cubicPairModels).RealGroup :=
    rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
  have herror := R.cubicPairFrozenVector_error k out x y (hcosets x y hres).1
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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

theorem hasCubicPairFrozenEquivalence_mono {u a b : ℝ}
    (h : R.HasCubicPairFrozenEquivalence u a) (hab : a ≤ b) : R.HasCubicPairFrozenEquivalence u b := by
  intro m hm hmb left right hleft hright
  exact (h m hm hmb left right hleft hright).mono hab

def HasCubicPairFrozenReduction (b : ℝ) : Prop :=
  ∃ u : ℝ, 0 ≤ u ∧ u ≤ b ∧ R.HasOuterValueControl u ∧ R.HasCubicPairFrozenEquivalence u b

theorem hasCubicPairFrozenReduction_mono {a b : ℝ}
    (h : R.HasCubicPairFrozenReduction a) (hab : a ≤ b) : R.HasCubicPairFrozenReduction b := by
  obtain ⟨u, hu, hua, houter, hequiv⟩ := h
  exact ⟨u, hu, hua.trans hab, houter, R.hasCubicPairFrozenEquivalence_mono hequiv hab⟩

theorem cubicPairFrozenEquivalence_at {b : ℝ} (h : R.HasCubicPairFrozenReduction b)
    (x : Fin 3 → ℤ) (hx : ∀ k, |(x k : ℝ)| ≤ (N : ℝ)) :
    NativeIntegerVectorEquivalence 2 b
      (R.cubicPairFrozenVector 0 (R.slowValue x) (R.rationalValue x))
      (R.cubicPairFrozenVector 1 (R.slowValue x) (R.rationalValue x)) := by
  obtain ⟨u, _hu, _hub, ⟨m, hm, hmb, hrat, hslow⟩, hequiv⟩ := h
  exact hequiv m hm hmb (R.slowValue x) (R.rationalValue x) (hslow x hx) (hrat x)

end NativePolynomialOrbitFactors

theorem exists_cubic_pair_frozen_reduction :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r), 0 ≤ r →
      R.HasCubicPairFrozenReduction ((p + q + r + C) ^ C) := by
  obtain ⟨A, _, houter⟩ := exists_cubic_pair_outer_control
  obtain ⟨B, _, hfrozen⟩ := exists_cubic_pair_frozen_equivalence
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (U + (X + U + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j shift V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let v := p + q + r
  let u := (v + A) ^ A
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hsum : u + (v + u + B) ^ B ≤ (p + q + r + C) ^ C := by
    simpa [X, U, u, v, Polynomial.eval₂_pow] using hbudget v hv
  have huC : u ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hBC : (v + u + B) ^ B ≤ (p + q + r + C) ^ C :=
    (le_add_of_nonneg_left hu).trans hsum
  let : TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra) := moduleTopology ℝ _
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi V.cubicPairModels).basis
  exact ⟨u, hu, huC, houter R hr,
    R.hasCubicPairFrozenEquivalence_mono (hfrozen R hr hu) hBC⟩

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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r}
  [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  [T2Space (ℝ ⊗[ℚ]
    (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
  {a c : (pi V.cubicPairModels).RealGroup}
  (M : R.FrozenMiddleRealization a c b)

noncomputable def cubicPairMiddleTest (k : Fin 2) (out : Fin W.outputDim) :
    M.model.Niltest (fun _ : Fin 3 => 1) :=
  M.pullTest (V.cubicPairCoordinateNiltest k out) (fun x => by
    rw [V.cubicPairCoordinateNiltest_observable]
    exact W.vertical.norm out _)

theorem cubicPairMiddleTest_eval (k : Fin 2) (out : Fin W.outputDim) (x : Fin 3 → ℤ) :
    (M.cubicPairMiddleTest k out).eval x = R.cubicPairFrozenVector k a c out x := by
  rw [cubicPairMiddleTest, M.pullTest_eval, V.cubicPairCoordinateNiltest_observable]
  rfl

theorem cubicPairMiddleTest_unit (k : Fin 2) (x : M.model.Space) :
    ∑ out, ‖(M.cubicPairMiddleTest k out).observable x‖ ^ 2 = 1 := by
  change ∑ out, ‖(V.cubicPairCoordinateNiltest k out).observable (M.spaceMap x)‖ ^ 2 = 1
  simp only [V.cubicPairCoordinateNiltest_observable]
  exact W.vertical.unit _

theorem cubicPairMiddleTest_complexity (hb : 0 ≤ b) (k : Fin 2) (out : Fin W.outputDim) :
    (M.cubicPairMiddleTest k out).ComplexityLE
      (productNiltestBudget (cubicPairBudget p q) + b + 4) := by
  apply M.pullTest_complexity _ _ _ hb (V.cubicPairCoordinateNiltest_complexity k out)
  have hB : 0 ≤ cubicPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  unfold productNiltestBudget productObservableLipBudget
  positivity

theorem cubicPairMiddleTest_common_vertical (k : Fin 2) (out : Fin W.outputDim)
    (z : M.model.RealGroup)
    (hz : z ∈ M.model.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1))
    (x : M.model.Space) :
    (M.cubicPairMiddleTest k out).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional W.vertical.frequency
          (realificationLieHom (V.cubicPairProjection 0)
            (realificationLieHom
              ((pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
              z.coord)) : ℝ) : CircleFourier.Circle) *
      (M.cubicPairMiddleTest k out).observable x := by
  let D := pi V.cubicPairModels
  let φ := realificationMap (hnil := M.model.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot)
    (D.filtration.gradedRefiltrationSubalgebra R.subalgebra).incl
  have htop : φ z ∈ D.filtration.realification.subgroup (∑ _ : CubicReplicatedIndex, 1) :=
    D.filtration.realGradedRefiltrationLayer_le R.subalgebra _ (M.inclusion_mem_top z hz)
  have heq := R.cubic_pair_top_agreement (φ z).coord (M.inclusion_mem_top z hz)
  change (V.cubicPairCoordinateNiltest k out).observable (M.spaceMap (z • x)) = _
  rw [M.spaceMap_top_smul z hz, V.cubicPairCoordinateNiltest_observable,
    productProjection_smul]
  have hv := W.cubicOriginalComponent_vertical out k.succ k.rev.succ 0 shift
    (productProjectionHom V.cubicPairModels (some k) (φ z))
    (productProjectionHom_mem_layer V.cubicPairModels (some k) _ (φ z) htop)
    (productProjection V.cubicPairModels (some k) (M.spaceMap x))
  change W.vertical.observable out _ = _ at hv
  refine hv.trans ?_
  change CircleFourier.character
      ((realifyFunctional W.vertical.frequency
        (realificationLieHom (V.cubicPairProjection k) (φ z).coord) : ℝ) :
        CircleFourier.Circle) * W.vertical.observable out _ = _
  have hphase : realifyFunctional W.vertical.frequency
      (realificationLieHom (V.cubicPairProjection k) (φ z).coord) =
    realifyFunctional W.vertical.frequency
      (realificationLieHom (V.cubicPairProjection 0) (φ z).coord) := by
    fin_cases k
    · rfl
    · exact heq.symm
  rw [hphase]
  congr 1
  exact (V.cubicPairCoordinateNiltest_observable k out (M.spaceMap x)).symm

end NativePolynomialOrbitFactors.FrozenMiddleRealization

theorem exists_cubic_pair_middle_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r u : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r)
      [TopologicalSpace (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [T2Space (ℝ ⊗[ℚ] V.CubicPairAlgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)]
      [T2Space (ℝ ⊗[ℚ]
        (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)],
      0 ≤ r → 0 ≤ u → R.HasOuterValueControl u → ∀ y : Fin 3 → ℤ,
      (∀ k, |(y k : ℝ)| ≤ (N : ℝ)) →
      ∃ M : R.FrozenMiddleRealization (R.slowValue y) (R.rationalValue y)
          ((p + q + r + u + C) ^ C),
        (∀ k out, (M.cubicPairMiddleTest k out).ComplexityLE ((p + q + r + u + C) ^ C)) ∧
        (∀ k out x, (M.cubicPairMiddleTest k out).eval x = R.cubicPairAnchoredVector y k out x) := by
  obtain ⟨a, _, hmodel⟩ := exists_native_frozen_middle_realization 3
  let X : Polynomial ℕ := Polynomial.X
  let B := 4 * (X + 1) + (X + (X + 2) ^ 2 + 3) + 6
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + Polynomial.C a) ^ a + 4)
  refine ⟨C, hC, ?_⟩
  intro p q r u W N _ i j shift V R _ _ _ _ _ _ _ _ hr hu houter y hy
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
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
  have hBt : cubicPairBudget p q ≤ b := by
    dsimp [cubicPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ cubicPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 6).trans V.cubicPairBudget_six_le
  have hprodmono : productNiltestBudget (cubicPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (cubicPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  have hsum : t + (t + a) ^ a + 4 ≤ (p + q + r + u + C) ^ C := by
    simpa [X, B, T, t, b, v, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget v hv
  have hcost : (t + a) ^ a ≤ (p + q + r + u + C) ^ C := by linarith
  have hN : ∀ _k : Fin 3, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := houter
  obtain ⟨M⟩ := @hmodel V.CubicPairAlgebra (Fin 3) _ _ _ _ _ _ _
    (pi V.cubicPairModels) _ _ _ t (R.mono hrt hN)
    (inferInstanceAs (TopologicalSpace (ℝ ⊗[ℚ]
      (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (IsTopologicalAddGroup (ℝ ⊗[ℚ]
      (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (ContinuousSMul ℝ (ℝ ⊗[ℚ]
      (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra)))
    (inferInstanceAs (T2Space (ℝ ⊗[ℚ]
      (pi V.cubicPairModels).filtration.gradedRefiltrationSubalgebra R.subalgebra))) ht
    (V.cubicPairNiltest_complexity.mono htest).1
    m hm (hmb.trans (Real.exp_le_exp.mpr hut)) (R.slowValue y) (R.rationalValue y)
    (fun k => (hslow y hy k).trans (Real.exp_le_exp.mpr hut)) (hrat y)
  rcases M with ⟨D', hD'F, hD', hinc, orbit, hzero, heval, f, hf, K, hK, hLip⟩
  let M' : R.FrozenMiddleRealization (R.slowValue y) (R.rationalValue y) ((t + a) ^ a) :=
    ⟨D', hD'F, hD', hinc, orbit, hzero, heval, f, hf, K, hK, hLip⟩
  refine ⟨M'.mono hcost, ?_, ?_⟩
  · intro k out
    exact (M'.cubicPairMiddleTest_complexity (by positivity) k out).mono
      ((by linarith : productNiltestBudget (cubicPairBudget p q) + (t + a) ^ a + 4 ≤
        t + (t + a) ^ a + 4).trans hsum)
  · intro k out x
    exact (M'.mono hcost).cubicPairMiddleTest_eval k out x

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

theorem norm_sub_positive_sum_le_weighted {I : Type*} [Fintype I]
    (w : I → ℝ) (c : I → ℂ) (t : ℂ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    ‖t - ∑ i, (w i : ℂ) * c i‖ ≤ ∑ i, w i * ‖t - c i‖ := by
  have hsumC : (∑ i, (w i : ℂ)) = 1 := by exact_mod_cast hsum
  have hid : t - ∑ i, (w i : ℂ) * c i = ∑ i, (w i : ℂ) * (t - c i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsumC, one_mul]
  rw [hid]
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i)]

theorem weighted_partition_mean_error {I X : Type*}
    [Fintype I] [Fintype X] [Nonempty X]
    (E : Finset X) (w : I → X → ℝ) (c : I → X → ℂ) (T : X → ℂ)
    {ε : ℝ} (hε : 0 ≤ ε) (hw : ∀ i x, 0 ≤ w i x)
    (hsum : ∀ x, ∑ i, w i x = 1) (hc : ∀ i x, ‖c i x‖ ≤ 1)
    (hT : ∀ x, ‖T x‖ ≤ 1)
    (hgood : ∀ i x, x ∉ E → 0 < w i x → ‖T x - c i x‖ ≤ ε) :
    (𝔼 x, ∑ i, w i x * ‖T x - c i x‖) ≤ ε + 2 * (E.card : ℝ) / Fintype.card X := by
  have hn (x : X) : 0 ≤ ∑ i, w i x * ‖T x - c i x‖ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i x) (norm_nonneg _))
  have hb (x : X) (d : ℝ) (h : ∀ i, 0 < w i x → ‖T x - c i x‖ ≤ d) :
      (∑ i, w i x * ‖T x - c i x‖) ≤ d := by
    calc
      _ ≤ ∑ i, w i x * d := by
        apply Finset.sum_le_sum
        intro i _
        rcases (hw i x).eq_or_lt with hi | hi
        · rw [← hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (h i hi) (hw i x)
      _ = d := by rw [← Finset.sum_mul, hsum, one_mul]
  have ha (x : X) : |∑ i, w i x * ‖T x - c i x‖| = ∑ i, w i x * ‖T x - c i x‖ :=
    abs_of_nonneg (hn x)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ∑ i, w i x * ‖T x - c i x‖) hε
    (fun x => by
      rw [ha]
      exact hb x 2 (fun i _ => (norm_sub_le _ _).trans (by linarith [hT x, hc i x])))
    (fun x hx => by rw [ha]; exact hb x ε (fun i hi => hgood i x hx hi))
  simpa only [ha] using herr

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
  (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
    V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
    (fun _ : Fin 3 => (N : ℝ)) r)

theorem cubicPairAnchoredVector_norm (y : Fin 3 → ℤ) (k : Fin 2)
    (out : Fin W.outputDim) (x : Fin 3 → ℤ) : ‖R.cubicPairAnchoredVector y k out x‖ ≤ 1 :=
  W.vertical.norm out _

theorem select_cubic_pair_local_partition {b c : ℝ}
    (hlocal : R.HasCubicPairLocalApproximation b) (hred : R.HasCubicPairFrozenReduction c) :
    ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp b ∧
      ∀ {I : Type*} [Fintype I] (B : Finset (ZMod N))
        (A : I → (Fin 3 → ZMod N) → ℝ) {ρ : ℝ}, 0 ≤ ρ →
        (∀ j x, 0 ≤ A j x) → (∀ x, ∑ j, A j x = 1) →
        (∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
          (∀ i, (P : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
          (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) →
        ∃ y : I → (Fin 3 → ZMod N),
          (∀ j, NativeIntegerVectorEquivalence 2 c
            (R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
            (R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
          ∀ (k : Fin 2) (out : Fin W.outputDim),
            (𝔼 x : Fin 3 → ZMod N,
              ∑ j, A j x * ‖W.eval out
                (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ) (((x 0).val : ℤ) + shift)) -
                  R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) k out
                    (fun i => ((x i).val : ℤ))‖) ≤
              Real.exp b * ρ + 6 * B.card / N := by
  classical
  obtain ⟨P, hP, hPb, hmodel⟩ := hlocal
  refine ⟨P, hP, hPb, ?_⟩
  intro I _ B A ρ hρ hA hsum hcells
  let v := fun (x : Fin 3 → ZMod N) (i : Fin 3) => ((x i).val : ℤ)
  have hv (x : Fin 3 → ZMod N) (i : Fin 3) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  have hchoose (j : I) : ∃ y : Fin 3 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  refine ⟨y, fun j => R.cubicPairFrozenEquivalence_at hred (v (y j)) (hv (y j)), ?_⟩
  intro k out
  let F := fun x : Fin 3 → ZMod N => W.eval out (cubicTrilinearInput (v x k.succ) (v x k.rev.succ) (v x 0 + shift))
  let G := fun j (x : Fin 3 → ZMod N) => R.cubicPairAnchoredVector (v (y j)) k out (v x)
  let E := coordinateExceptional (ι := Fin 3) B
  have hpoint (j : I) (x : Fin 3 → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - G j x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hmodel (v (y j)) (hv (y j)) k out (v x) ρ hρ (hv x) hres
      (by simpa only [v, Int.cast_natCast] using hnear)
  have herr := weighted_partition_mean_error E A G F
    (mul_nonneg (Real.exp_nonneg b) hρ) hA hsum
    (fun j x => R.cubicPairAnchoredVector_norm _ _ _ _)
    (fun x => W.norm_eval out _) (fun j x hx hAx => hpoint j x hx hAx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin 3 → ZMod N) ≤ 3 * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin 3) B
  have herr' : (𝔼 x : Fin 3 → ZMod N, ∑ j, A j x * ‖F x - G j x‖) ≤
      Real.exp b * ρ + 2 * ((E.card : ℝ) / Fintype.card (Fin 3 → ZMod N)) := by
    simpa only [mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + 2 * (3 * (B.card : ℝ) / N) := by gcongr
    _ = _ := by ring

end NativePolynomialOrbitFactors

theorem exists_cubic_pair_local_partition (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r),
      R.HasCubicPairLocalApproximation b → R.HasCubicPairFrozenReduction c →
      0 ≤ t → b ≤ t → c ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ P : ℕ, ∃ hP : 0 < P,
        letI : NeZero P := ⟨hP.ne'⟩
        (P : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ n : ℕ, 0 < n ∧
          (Fintype.card (Fin 3 → Fin n × ZMod P) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
          ∃ A : (Fin n × ZMod P) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            ∃ y : (Fin 3 → Fin n × ZMod P) → (Fin 3 → ZMod N),
              (∀ j, NativeIntegerVectorEquivalence 2 ((t + C) ^ C)
                (R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) 0)
                (R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) 1)) ∧
              ∀ (k : Fin 2) (out : Fin W.outputDim),
                (𝔼 x : Fin 3 → ZMod N,
                  ∑ j, (∏ i, A (j i) (x i) : ℝ) * ‖W.eval out
                    (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ) (((x 0).val : ℤ) + shift)) -
                      R.cubicPairAnchoredVector (fun i => ((y j i).val : ℤ)) k out
                        (fun i => ((x i).val : ℤ))‖) ≤
                  Real.exp (t + 60) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 60 + 3 * (X + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t W N _ i j shift V R hlocal hred ht hbt hct ρ hρ hprec
  obtain ⟨P, hP, hPb, hselect⟩ := R.select_cubic_pair_local_partition hlocal hred
  let : NeZero P := ⟨hP.ne'⟩
  have hPt : (P : ℝ) ≤ Real.exp t := hPb.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N P ht hPt hρ hprec
  have htotal : t + 60 + 3 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget t ht
  have hpow : 0 ≤ (t + B) ^ B := by positivity
  have htC : t ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hthree : 3 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 3 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 3 => A) i j x :=
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
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 3
      _ = Real.exp (3 * (t + B) ^ B) := (Real.exp_nat_mul _ 3).symm
      _ ≤ _ := Real.exp_le_exp.mpr hthree
  · intro k out
    have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have h60 : (60 : ℝ) ≤ Real.exp 60 := by linarith [Real.add_one_le_exp (60 : ℝ)]
    apply (herr k out).trans
    calc
      _ = Real.exp b * ρ + 6 * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp t * ρ + 6 * (6 * ρ + 3 / N) := by gcongr
      _ ≤ Real.exp t * ρ + 6 * Real.exp t * (6 * ρ + 3 / N) := by
        gcongr
        nlinarith [Real.one_le_exp ht]
      _ = Real.exp t * (37 * ρ + 18 * (1 / N)) := by ring
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
  {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p} {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
  {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
    Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}

structure NativeCubicPairPartition
    (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
      V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
      (fun _ : Fin 3 => (N : ℝ)) r) (b ε : ℝ) where
  I : Type
  [finite : Fintype I]
  card_bound : (Fintype.card (Fin 3 → I) : ℝ) ≤ Real.exp b
  weight : I → ZMod N → ℝ
  positive : ∀ j, PositiveCyclicNiltest.{0} 1 N b (weight j)
  total : ∀ x, ∑ j, weight j x = 1
  anchor : (Fin 3 → I) → (Fin 3 → ZMod N)
  equivalence : ∀ j, NativeIntegerVectorEquivalence 2 b
    (R.cubicPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 0)
    (R.cubicPairAnchoredVector (fun k => ((anchor j k).val : ℤ)) 1)
  weighted_approximation : ∀ (k : Fin 2) (out : Fin W.outputDim),
    (𝔼 x : Fin 3 → ZMod N,
      ∑ j, (∏ l, weight (j l) (x l) : ℝ) * ‖W.eval out
        (cubicTrilinearInput ((x k.succ).val : ℤ) ((x k.rev.succ).val : ℤ) (((x 0).val : ℤ) + shift)) -
          R.cubicPairAnchoredVector (fun l => ((anchor j l).val : ℤ)) k out
            (fun l => ((x l).val : ℤ))‖) ≤ ε

attribute [local instance] NativeCubicPairPartition.finite

noncomputable def NativeCubicPairPartition.mono
    {R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
      V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
      (fun _ : Fin 3 => (N : ℝ)) r} {a b ε δ : ℝ}
    (P : NativeCubicPairPartition R a ε) (hab : a ≤ b) (hεδ : ε ≤ δ) : NativeCubicPairPartition R b δ :=
  { P with
    card_bound := P.card_bound.trans (Real.exp_le_exp.mpr hab)
    positive := fun j => (P.positive j).mono le_rfl hab
    equivalence := fun j => (P.equivalence j).mono hab
    weighted_approximation := fun k out => (P.weighted_approximation k out).trans hεδ }

end Data

theorem exists_cubic_pair_precise_partition :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r b c t e : ℝ}
      {W : NativeMultidegreeNilcharacter (fun _ : CubicReplicatedIndex => 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim × Fin W.outputDim} {shift : ℤ}
      {V : NativeSampleCorrelation (fun _ : Fin 3 => 1) 2 q
        Finset.univ (fun z : Fin 3 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.cubicAntisymmetricPair i j (z 1).val (z 2).val (((z 0).val : ℤ) + shift))}
      (R : NativePolynomialOrbitFactors (pi V.cubicPairModels)
        V.cubicPairPolynomial (piFrequency V.cubicPairFrequencies)
        (fun _ : Fin 3 => (N : ℝ)) r),
      R.HasCubicPairLocalApproximation b → R.HasCubicPairFrozenReduction c →
      0 ≤ t → 0 ≤ e → b ≤ t → c ≤ t → Real.exp ((t + e + C) ^ C) ≤ (N : ℝ) →
      Nonempty (NativeCubicPairPartition R ((t + e + C) ^ C) (Real.exp (-e))) := by
  obtain ⟨A, _, hpartition⟩ := exists_cubic_pair_local_partition 2
  let X : Polynomial ℕ := Polynomial.X
  let T := X + 100
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((T + Polynomial.C A) ^ A + 2 * T)
  refine ⟨C, hC, ?_⟩
  intro p q r b c t e W N _ i j shift V R hlocal hred ht he hbt hct hN
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

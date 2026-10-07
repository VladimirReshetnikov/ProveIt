/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Mathematical statements are unchanged from the pinned upstream source.
Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
import OAI.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateFiber
import OAI.Combinatorics.Progressions.Linear.InducedUnitRankFamily

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_vertical_correlators :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)) (eta : L →ₗ[ℚ] ℚ),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ i, rationalLogHeight (eta (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ h, (S h).orbit = (T h).orbit ∧ (S h).normBound ≤ 1 ∧
          (S h).ComplexityLE ((p + C) ^ C)) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        (∀ h z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          (S h).observable (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * (S h).observable x) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional eta z.coord = n) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  classical
  obtain ⟨a, _, hverticalBudget⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 1 + (X + 1 + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ s d D T H hH p hp hT hcap hsame N _ weight hweight hcorr
  obtain ⟨h₀, hh₀⟩ := hH
  let q := (p + 1 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : p + 1 + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p + 1 ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hVq : verticalDecompositionBudget (p + 1) ≤ q := hverticalBudget (p + 1) (by linarith)
  have hrho : 0 < Real.exp (-p) / 2 := by positivity
  have hrhoinv : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div, Real.exp_neg]; field_simp
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨J, inst, eta, V, hcard, hheight, hV, hvert, hint, happ, _⟩ :=
    (T h₀).exists_vertical_decomposition_preserving_bounds (by linarith : 0 ≤ p + 1)
      ((hT h₀ hh₀).mono (by linarith : p ≤ p + 1)) hrho hrhoinv
  let := inst
  have hcardq : (Fintype.card J : ℝ) ≤ Real.exp q := hcard.trans (Real.exp_le_exp.mpr hVq)
  let U (h : G) (j : J) : D.Niltest (fun _ : Unit => 1) := { V j with orbit := (T h).orbit }
  have hchoose (h : {h // h ∈ H}) : ∃ j : J,
      Real.exp (-p) / (2 * Real.exp q) ≤
        ‖𝔼 x, weight h.val x * star ((U h.val j).evalCyclic N (fun _ => x))‖ := by
    apply exists_correlating_summand Finset.univ_nonempty (weight h.val)
      (fun x => (T h.val).evalCyclic N (fun _ => x))
      (fun j x => (U h.val j).evalCyclic N (fun _ => x))
      (Real.exp_pos (-p)) (Real.exp_pos q) hcardq
      (fun x _ => hweight h.val h.property x) _ (hcorr h.val h.property)
    intro x _
    change ‖(∑ j, (V j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1)
        (fun _ => (x.val : ℤ)) (T h.val).orbit))) -
      (T h.val).observable (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ => 1)
          (fun _ => (x.val : ℤ)) (T h.val).orbit))‖ ≤ _
    rw [hsame h.val h₀]
    exact happ _
  choose choice hchoice using hchoose
  let code : G → J := fun h => if hh : h ∈ H then choice ⟨h, hh⟩ else choice ⟨h₀, hh₀⟩
  obtain ⟨j, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H ⟨h₀, hh₀⟩ code Set.univ (Set.toFinite _)
      (fun _ _ => Set.mem_univ _) (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hcardq)
  have hselected (h : G) (hh : h ∈ H') : Real.exp (-p) / (2 * Real.exp q) ≤
      ‖𝔼 x, weight h x * star ((U h j).evalCyclic N (fun _ => x))‖ := by
    have hcode : choice ⟨h, hsub hh⟩ = j := by
      simpa only [code, dite_eq_left (hsub hh)] using hconstant h hh
    simpa only [hcode] using hchoice ⟨h, hsub hh⟩
  have hne : ∃ x, (V j).observable x ≠ 0 := by
    by_contra! hz
    obtain ⟨h, hh⟩ := hnonempty
    have hc := hselected h hh
    have hzero (x : ZMod N) : (U h j).evalCyclic N (fun _ => x) = 0 := hz _
    simp only [hzero, star_zero, mul_zero, Finset.expect_const_zero, norm_zero] at hc
    exact (not_le_of_gt (by positivity : 0 < Real.exp (-p) / (2 * Real.exp q))) hc
  refine ⟨H', fun h => U h j, eta j, hsub, hnonempty, ?_, ?_, ?_, fun _ _ => rfl,
    fun _ z hz x => hvert j z hz x, hint j hne, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro i
    exact (hheight j i).trans (hVq.trans hqC)
  · intro h
    refine ⟨rfl, ?_, ?_⟩
    · change (V j).normBound ≤ 1
      rw [(hV j).2.2.1]
      exact hcap h₀ hh₀
    · exact (hV j).1.mono hpC
  · intro h hh
    apply le_trans _ (hselected h hh)
    calc
      _ ≤ Real.exp (-(p + q) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(p + q)) / 2 := exp_sub_one_le_half_exp _
      _ = Real.exp (-p) / (2 * Real.exp q) := by
        rw [show -(p + q) = -p - q by ring, Real.exp_sub]
        ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_common_unit_vertical_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
              (Fin (n + 1)) ((p + C) ^ C),
            ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
                (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                  (fun _ => (x.val : ℤ)) (T h).orbit)))‖ := by
  obtain ⟨a, _, hvertical⟩ := exists_common_vertical_correlators
  obtain ⟨b, _, hcomplete⟩ := exists_native_unit_vertical_completion s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Q + (Q + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hnorm hsame N _ weight hweight hcorr
  let q := (p + a) ^ a
  let q₂ := (q + b) ^ b
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have htotal : p + q + q₂ + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, q₂, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
  obtain ⟨H', S, eta, hsub, hH', hdense, hheight, hS, hSsame, hvert, hint, hScorr⟩ :=
    hvertical D T H hH hp hT hnorm hsame weight hweight hcorr
  obtain ⟨h₀, hh₀⟩ := hH'
  have hmean : Real.exp (-q) ≤ 𝔼 x, ‖(S h₀).evalCyclic N (fun _ => x)‖ := by
    apply (hScorr h₀ hh₀).trans
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (hweight h₀ (hsub hh₀) x)
  obtain ⟨x₀, _, hx₀⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  let y : D.Space := QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
    (fun _ => (x₀.val : ℤ)) (S h₀).orbit)
  obtain ⟨n, hn, hnq, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvvertical⟩ :=
    hcomplete D (S h₀) hq (hS h₀).2.2 (hS h₀).2.1 eta (hvert h₀) y hx₀
  let V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
      (Fin (n + 1)) ((p + C) ^ C) := {
    observable := v
    unit := hvunit
    norm := hvnorm
    lipBound := K
    lip_bound := hK.trans (Real.exp_le_exp.mpr hq₂C)
    lipschitz := hvLip
    frequency := eta
    height := fun i => (hheight i).trans hqC
    vertical := hvvertical
    integral := hint
  }
  refine ⟨H', hsub, ⟨h₀, hh₀⟩,
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC)) (Nat.cast_nonneg _)).trans hdense,
    n, hn, hnq.trans (Real.exp_le_exp.mpr hq₂C), V, ?_⟩
  intro h hh
  have hvalue (x : ZMod N) : V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)) = (S h).evalCyclic N (fun _ => x) / 2 := by
    change v 0 _ = _
    rw [hv0, hSsame h₀ h]
    change (S h).observable _ / 2 = (S h).observable _ / 2
    rw [(hS h).1]
  have heq : (𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) =
      (𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))) / 2 := by
    simp only [hvalue, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div]
  rw [heq, norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  apply le_trans _ (div_le_div_of_nonneg_right (hScorr h hh) (by norm_num : (0 : ℝ) ≤ 2))
  apply le_trans _ (exp_sub_one_le_half_exp (-q))
  apply Real.exp_le_exp.mpr
  linarith

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_native_vertical_derivative_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      (∀ h, B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
        (B.test h).orbit = 1) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        Nonempty (NativeVerticalDerivativeData R) := by
  obtain ⟨a, _, hvertical⟩ := RationalFilteredNilmanifold.exists_common_vertical_correlators
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro s N _ p f hp hf B hnormalized
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, eta, _, hH, hdense, hheight, hS, hsame, hvert, hint, hcorr⟩ :=
    hvertical B.model B.test B.shifts B.nonempty hp (fun h _ => B.complexity h)
      (fun h _ => B.norm h) B.common_observable (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).2.1
    complexity := fun h => (hS h).2.2.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  refine ⟨R, ⟨{
    normalized := ?_
    frequency := eta
    height := fun i => (hheight i).trans hqC
    vertical := hvert
    integral := hint }⟩⟩
  intro h
  change B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (S h).orbit = 1
  rw [(hS h).1]
  exact hnormalized h

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_native_unit_factor_replacement (s degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (f : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p
        (fun _ : Unit => fun x => f h x * star ((T h).evalCyclic N (fun _ => x))))) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n : ℕ, 0 < n ∧ (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V : D.UnitVerticalObservable (D.filtration.realification.subgroup s)
              (Fin (n + 1)) ((p + C) ^ C),
            ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N ((p + C) ^ C)
              (fun _ : Unit => fun x => f h x * star (V.observable 0 (QuotientGroup.mk
                (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                  (fun _ => (x.val : ℤ)) (T h).orbit))))) := by
  classical
  obtain ⟨a, _, hselect⟩ := exists_common_unit_vertical_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (2 * X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hnorm hsame N _ f hf hcorr
  let W (h : {h // h ∈ H}) := Classical.choice (hcorr h.val h.property)
  let weight (h : G) (x : ZMod N) : ℂ :=
    if hh : h ∈ H then
      f h x * star (((W ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => x)) else 0
  have hweight (h : G) (hh : h ∈ H) (x : ZMod N) : ‖weight h x‖ ≤ 1 := by
    simp only [weight, dite_eq_left hh, norm_mul, norm_star]
    have hn : ‖((W ⟨h, hh⟩).test.expNormalize p).evalCyclic N (fun _ => x)‖ ≤ 1 := by
      apply (((W ⟨h, hh⟩).test.expNormalize p).norm_evalCyclic_le N (fun _ => x)).trans
      exact_mod_cast (W ⟨h, hh⟩).test.expNormalize_norm (W ⟨h, hh⟩).complexity
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x)).trans hn
  have hweightcorr (h : G) (hh : h ∈ H) : Real.exp (-(2 * p + 2)) ≤
      ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖ := by
    let Wh := W ⟨h, hh⟩
    have hscale (x : ZMod N) : (Wh.test.expNormalize p).evalCyclic N (fun _ => x) =
        (Real.exp (-p) : ℂ) * Wh.test.evalCyclic N (fun _ => x) := rfl
    have heq : (𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))) =
        (Real.exp (-p) : ℂ) * (𝔼 x, (f h x * star ((T h).evalCyclic N (fun _ => x))) *
          star (Wh.test.evalCyclic N (fun _ => x))) := by
      simp only [weight, dite_eq_left hh]
      change (𝔼 x, (f h x * star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))) *
        star ((T h).evalCyclic N (fun _ => x))) = _
      simp only [hscale, star_mul, Complex.star_def, Complex.conj_ofReal, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      ring
    rw [heq, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-p))]
    calc
      _ ≤ Real.exp (-p) * Real.exp (-p) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ _ := mul_le_mul_of_nonneg_left Wh.correlation (Real.exp_nonneg _)
  obtain ⟨H', hsub, hH', hdense, n, hn, hnq, V, hVc⟩ :=
    hselect D T H hH (by linarith : 0 ≤ 2 * p + 2)
      (fun h hh => (hT h hh).mono (by linarith : p ≤ 2 * p + 2)) hnorm hsame
      weight hweight hweightcorr
  let q := (2 * p + 2 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  refine ⟨H', hsub, hH',
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC)) (Nat.cast_nonneg _)).trans hdense,
    n, hn, hnq.trans (Real.exp_le_exp.mpr hqC), V.mono hqC, ?_⟩
  intro h hh
  let Wh := W ⟨h, hsub hh⟩
  refine ⟨{
    L := Wh.L
    dim := Wh.dim
    model := Wh.model
    test := Wh.test.expNormalize p
    complexity := (Wh.test.expNormalize_complexity Wh.complexity).mono hpC
    coordinate := ()
    correlation := ?_
  }⟩
  have hc := (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hVc h hh)
  have hweightval (x : ZMod N) : weight h x =
      f h x * star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x)) := by
    simp only [weight, dite_eq_left (hsub hh), Wh]
  change Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x,
    (f h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) *
      star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))‖
  have heq : (𝔼 x, (f h x * star (V.observable 0 (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (T h).orbit)))) *
        star ((Wh.test.expNormalize p).evalCyclic N (fun _ => x))) =
      (𝔼 x, weight h x * star (V.observable 0 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (T h).orbit)))) := by
    simp only [hweightval]
    apply Finset.expect_congr rfl
    intro x _
    ring
  rw [heq]
  exact hc

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_native_two_factor_unit_replacement (s t degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra ℚ L₁]
      [LieRing L₂] [LieAlgebra ℚ L₂]
      [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₂)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₂)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₂)] [T2Space (ℝ ⊗[ℚ] L₂)] {d₁ d₂ : ℕ}
      (D₁ : RationalFilteredNilmanifold L₁ s d₁) (D₂ : RationalFilteredNilmanifold L₂ t d₂)
      (T : G → D₁.Niltest (fun _ : Unit => 1)) (S : G → D₂.Niltest (fun _ : Unit => 1))
      (H : Finset G), H.Nonempty → ∀ {p : ℝ}, 0 ≤ p →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (S h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) → (∀ h ∈ H, (S h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      (∀ h k, (S h).observable = (S k).observable) →
      ∀ {N : ℕ} [NeZero N] (f : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation degree N p (fun _ : Unit => fun x =>
        f h x * star ((S h).evalCyclic N (fun _ => x)) * star ((T h).evalCyclic N (fun _ => x))))) →
      ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n₁ : ℕ, 0 < n₁ ∧ (n₁ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V₁ : D₁.UnitVerticalObservable (D₁.filtration.realification.subgroup s)
              (Fin (n₁ + 1)) ((p + C) ^ C),
            ∃ n₂ : ℕ, 0 < n₂ ∧ (n₂ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ V₂ : D₂.UnitVerticalObservable (D₂.filtration.realification.subgroup t)
                  (Fin (n₂ + 1)) ((p + C) ^ C),
                ∀ h ∈ H', Nonempty (NativeVectorCorrelation degree N ((p + C) ^ C)
                  (fun _ : Unit => fun x => f h x *
                    star (V₂.observable 0 (QuotientGroup.mk
                      (D₂.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (S h).orbit))) *
                    star (V₁.observable 0 (QuotientGroup.mk
                      (D₁.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (T h).orbit))))) := by
  obtain ⟨a, _, hfirst⟩ := exists_native_unit_factor_replacement s degree
  obtain ⟨b, _, hsecond⟩ := exists_native_unit_factor_replacement t degree
  let X : Polynomial ℕ := Polynomial.X
  let Q₁ : Polynomial ℕ := (X + Polynomial.C a) ^ a
  let P₂ : Polynomial ℕ := X + Q₁ + 2
  let Q₂ : Polynomial ℕ := (P₂ + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q₁ + Q₂ + 2)
  refine ⟨C, hC, ?_⟩
  intro G L₁ L₂ _ _ _ _ _ _ _ _ _ _ _ _ d₁ d₂ D₁ D₂ T S H hH p hp
    hT hS hnT hnS hcT hcS N _ f hf hcorr
  have hfS (h : G) (hh : h ∈ H) (x : ZMod N) :
      ‖f h x * star ((S h).evalCyclic N (fun _ => x))‖ ≤ 1 := by
    rw [norm_mul, norm_star]
    have hn : ‖(S h).evalCyclic N (fun _ => x)‖ ≤ 1 := by
      apply ((S h).norm_evalCyclic_le N (fun _ => x)).trans
      exact_mod_cast hnS h hh
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h hh x)).trans hn
  obtain ⟨H₁, hH₁H, hH₁, hdense₁, n₁, hn₁, hcount₁, V₁, hcorr₁⟩ :=
    hfirst D₁ T H hH hp hT hnT hcT
      (fun h x => f h x * star ((S h).evalCyclic N (fun _ => x))) hfS hcorr
  let q₁ := (p + a) ^ a
  let p₂ := p + q₁ + 2
  let q₂ := (p₂ + b) ^ b
  have hq₁ : 0 ≤ q₁ := by dsimp [q₁]; positivity
  have hp₂ : 0 ≤ p₂ := by dsimp [p₂]; positivity
  have hq₂ : 0 ≤ q₂ := by dsimp [q₂]; positivity
  have hpp₂ : p ≤ p₂ := by dsimp [p₂]; linarith
  have hq₁p₂ : q₁ ≤ p₂ := by dsimp [p₂]; linarith
  let f₂ (h : G) (x : ZMod N) := f h x * star (V₁.observable 0 (QuotientGroup.mk
    (D₁.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
      (fun _ => (x.val : ℤ)) (T h).orbit)))
  have hf₂ (h : G) (hh : h ∈ H₁) (x : ZMod N) : ‖f₂ h x‖ ≤ 1 := by
    change ‖f h x * star (V₁.observable 0 _)‖ ≤ 1
    rw [norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hf h (hH₁H hh) x)).trans (V₁.norm 0 _)
  have hcorr₂ (h : G) (hh : h ∈ H₁) : Nonempty (NativeVectorCorrelation degree N p₂
      (fun _ : Unit => fun x => f₂ h x * star ((S h).evalCyclic N (fun _ => x)))) := by
    obtain ⟨Wh⟩ := hcorr₁ h hh
    refine ⟨(Wh.mono hq₁p₂).mapCoordinates _ id ?_⟩
    intro i x
    dsimp only [id_eq, f₂]
    ring
  obtain ⟨H₂, hH₂H₁, hH₂, hdense₂, n₂, hn₂, hcount₂, V₂, hfinal⟩ :=
    hsecond D₂ S H₁ hH₁ hp₂ (fun h hh => (hS h (hH₁H hh)).mono hpp₂)
      (fun h hh => hnS h (hH₁H hh)) hcS f₂ hf₂ hcorr₂
  have htotal : p + q₁ + q₂ + 2 ≤ (p + C) ^ C := by
    simpa [X, Q₁, P₂, Q₂, q₁, p₂, q₂, Polynomial.eval₂_pow] using hbudget p hp
  have hq₁C : q₁ ≤ (p + C) ^ C := by linarith
  have hq₂C : q₂ ≤ (p + C) ^ C := by linarith
  refine ⟨H₂, hH₂H₁.trans hH₁H, hH₂, ?_, n₁, hn₁,
    hcount₁.trans (Real.exp_le_exp.mpr hq₁C), V₁.mono hq₁C, n₂, hn₂,
    hcount₂.trans (Real.exp_le_exp.mpr hq₂C), V₂.mono hq₂C, ?_⟩
  · calc
      _ ≤ Real.exp (-(q₁ + q₂)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q₂) * (Real.exp (-q₁) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q₂) * H₁.card := mul_le_mul_of_nonneg_left hdense₁ (Real.exp_nonneg _)
      _ ≤ _ := hdense₂
  · intro h hh
    obtain ⟨Wh⟩ := hfinal h hh
    refine ⟨(Wh.mono hq₂C).mapCoordinates _ id ?_⟩
    intro i x
    change f h x * star (V₂.observable 0 _) * star (V₁.observable 0 _) =
      f₂ h x * star (V₂.observable 0 _)
    dsimp only [f₂]
    ring

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_mixed_of_bounded (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type*} {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ (f : ZMod N → ℂ), (∀ x, ‖f x‖ ≤ 1) →
      ∀ H : Finset (ZMod N), H.Nonempty → Real.exp (-p) * N ≤ (H.card : ℝ) →
      ∀ (F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) I p) (i : I),
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
        star (F.eval i (correlationInput (h.val : ℤ) (n.val : ℤ)))‖) →
      Nonempty (NativeMixedCorrelation s N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hselect⟩ := RationalFilteredNilmanifold.exists_common_unit_vertical_correlators
    (∑ j, mixedCorrelationDegree s j)
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro I N _ p hp f hf H hH hdense F i hcorr
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpR : p ≤ (p + C) ^ C := by linarith
  have hqR : q ≤ (p + C) ^ C := by linarith
  have htwo : 2 ≤ (p + C) ^ C := by linarith
  let T (h : ZMod N) := F.slice i (h.val : ℤ)
  have hweight (h x : ZMod N) : ‖multiplicativeDerivative f h x‖ ≤ 1 := by
    simp only [multiplicativeDerivative, norm_mul, norm_star]
    exact (mul_le_mul (hf x) (hf (x + h)) (norm_nonneg _) (by norm_num)).trans_eq (one_mul 1)
  have hTcorr (h : ZMod N) (hh : h ∈ H) : Real.exp (-p) ≤
      ‖𝔼 x : ZMod N, multiplicativeDerivative f h x * star ((T h).evalCyclic N (fun _ => x))‖ := by
    simpa only [T, RationalFilteredNilmanifold.Niltest.evalCyclic, NativeBoundedMultidegreeFamily.slice_eval]
      using hcorr h hh
  obtain ⟨J, hJH, hJ, hJdense, n, _, hn, V, hVcorr⟩ :=
    hselect F.model T H hH hp (fun h _ => F.slice_complexity i h.val)
      (fun h _ => (F.slice_norm i h.val).le)
      (fun h k => (F.slice_observable i h.val).trans (F.slice_observable i k.val).symm)
      (multiplicativeDerivative f) (fun h _ x => hweight h x) hTcorr
  have hnR : (n + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) := hn.trans (Real.exp_le_exp.mpr hqR)
  let M := F.toNilcharacter hpR hnR (V.mono hqR)
  have hMeval (h x : ZMod N) : M.evalCyclic N (0 : Fin (n + 1)) (correlationInput h x) =
      V.observable 0 (QuotientGroup.mk (F.model.filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (T h).orbit)) := by
    have hinput : (fun j => ((correlationInput h x j).val : ℤ)) =
        correlationInput (h.val : ℤ) (x.val : ℤ) := by
      funext j
      exact Fin.cases rfl (fun _ => rfl) j
    change M.eval (0 : Fin (n + 1)) (fun j => ((correlationInput h x j).val : ℤ)) = _
    rw [hinput]
    change V.observable 0 (QuotientGroup.mk (F.multi.filtration.realification.polynomialOrbitEval
      (correlationInput (h.val : ℤ) (x.val : ℤ)) F.orbit)) = _
    rw [F.slice_orbit_eval i (h.val : ℤ)]
  refine ⟨{ shifts := J, nonempty := hJ, density := ?_, mixed := M, correlation := ?_ }⟩
  · simp only [ZMod.card]
    calc
      Real.exp (-((p + C) ^ C)) * N ≤ Real.exp (-(p + q)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H.card := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ J.card := hJdense
  · intro h hh
    apply NativeVectorCorrelation.exists_of_mean (s - 1) N (nativeMixedResidual f M h) htwo
    refine ⟨(0 : Fin (n + 1)), ?_⟩
    change Real.exp (-((p + C) ^ C)) ≤
      ‖𝔼 x : ZMod N, multiplicativeDerivative f h x *
        star (M.evalCyclic N (0 : Fin (n + 1)) (correlationInput h x))‖
    simp only [hMeval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hqR)).trans (hVcorr h hh)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem NativeUnitRankFamily.withOrbit_observable
    {σ τ I : Type*} [Fintype I] {w : σ → ℕ} {s r : ℕ} {p : ℝ}
    (F : NativeUnitRankFamily w s r τ I p) (i : I) (t : τ) :
    ((F.test i).withOrbit (F.orbit t)).observable = (F.test i).observable := rfl

theorem exists_native_correlation_of_sliced_unit_products
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p q P : ℝ} {f : ZMod N → ℂ}
    (J : Finset (ZMod N))
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (iM : K) (H : Finset {h // h ∈ J}) (hH : H.Nonempty)
    (hdense : Real.exp (-P) * N ≤ (H.card : ℝ)) (hpP : p ≤ P) (hqP : q ≤ P)
    {n₁ n₂ : ℕ} (hn₁ : (n₁ + 1 : ℝ) ≤ Real.exp q) (hn₂ : (n₂ + 1 : ℝ) ≤ Real.exp q)
    (V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
      (Fin (n₁ + 1)) q)
    (V₂ : M.model.UnitVerticalObservable
      (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i)) (Fin (n₂ + 1)) q)
    (hcorr : ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N q (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
        (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
        star (V₁.observable 0 (QuotientGroup.mk
          (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
            (fun _ => (x.val : ℤ)) (F.orbit h))))))) :
    Nonempty (NativeCorrelationStructure s r N P f) := by
  apply exists_native_correlation_of_unit_products J F M H hH hdense hpP
    (hn₁.trans (Real.exp_le_exp.mpr hqP)) (hn₂.trans (Real.exp_le_exp.mpr hqP))
    (V₁.mono hqP) (V₂.mono hqP)
  intro h hh
  obtain ⟨Wh⟩ := hcorr h hh
  refine ⟨(Wh.mono hqP).mapCoordinates _ id ?_⟩
  intro i x
  change multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
    (M.multi.filtration.realification.polynomialOrbitEval
      (correlationInput (h.val.val : ℤ) (x.val : ℤ)) M.orbit))) *
      star (V₁.observable 0 (QuotientGroup.mk
        (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (F.orbit h)))) =
    multiplicativeDerivative f h.val x * star (V₂.observable 0 (QuotientGroup.mk
      (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
      star (V₁.observable 0 (QuotientGroup.mk
        (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (x.val : ℤ)) (F.orbit h))))
  rw [M.slice_orbit_eval]

theorem exists_native_sliced_product_correlation
    {I K : Type} [Fintype I] {s r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    {J : Finset (ZMod N)}
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
    (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
    (iF : I) (iM : K) (h : {h // h ∈ J})
    (hcorr : Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x * star (M.eval iM
        (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
        star (F.eval h iF (fun _ => (x.val : ℤ)))))) :
    Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
      multiplicativeDerivative f h.val x *
        star ((M.slice iM (h.val.val : ℤ)).evalCyclic N (fun _ => x)) *
        star (((F.test iF).withOrbit (F.orbit h)).evalCyclic N (fun _ => x)))) := by
  obtain ⟨Wh⟩ := hcorr
  refine ⟨Wh.mapCoordinates _ id ?_⟩
  intro i x
  change multiplicativeDerivative f h.val x *
    star ((M.slice iM (h.val.val : ℤ)).eval (fun _ => (x.val : ℤ))) *
    star (((F.test iF).withOrbit (F.orbit h)).eval (fun _ => (x.val : ℤ))) = _
  rw [M.slice_eval, F.withOrbit_eval]

theorem exists_native_fixed_product_unit_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I K : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N))
      (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
      (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
      (iF : I) (iM : K) (H : Finset {h // h ∈ J}), H.Nonempty →
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
        multiplicativeDerivative f h.val x * star (M.eval iM
          (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
          star (F.eval h iF (fun _ => (x.val : ℤ)))))) →
      ∃ H' : Finset {h // h ∈ J}, H' ⊆ H ∧ H'.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        ∃ n₁ : ℕ, 0 < n₁ ∧ (n₁ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ V₁ : F.model.UnitVerticalObservable (F.model.filtration.realification.subgroup s)
              (Fin (n₁ + 1)) ((p + C) ^ C),
            ∃ n₂ : ℕ, 0 < n₂ ∧ (n₂ + 1 : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              ∃ V₂ : M.model.UnitVerticalObservable
                  (M.model.filtration.realification.subgroup (∑ i, mixedCorrelationDegree s i))
                  (Fin (n₂ + 1)) ((p + C) ^ C),
                ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                  (fun _ : Unit => fun x => multiplicativeDerivative f h.val x *
                    star (V₂.observable 0 (QuotientGroup.mk
                      (M.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) (M.slice iM (h.val.val : ℤ)).orbit))) *
                    star (V₁.observable 0 (QuotientGroup.mk
                      (F.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                        (fun _ => (x.val : ℤ)) ((F.test iF).withOrbit (F.orbit h)).orbit))))) := by
  obtain ⟨C, hC, hselect⟩ := exists_native_two_factor_unit_replacement s
    (∑ i, mixedCorrelationDegree s i) (s - 1)
  refine ⟨C, hC, ?_⟩
  intro I K _ r N _ p f J F M iF iM H hH hp hf hcorr
  let T (h : {h // h ∈ J}) := (F.test iF).withOrbit (F.orbit h)
  let S (h : {h // h ∈ J}) := M.slice iM (h.val.val : ℤ)
  have hmodels := by
    as_aux_lemma =>
      exact hselect (G := {h // h ∈ J}) F.model M.model
  have htests := by
    as_aux_lemma =>
      exact hmodels T S H hH hp
  have hbounded := by
    as_aux_lemma =>
      exact htests
        (fun h _ => ((F.test iF).withOrbit_complexity (F.orbit h) p).mpr (F.test_complexity iF))
        (fun h _ => M.slice_complexity iM (h.val.val : ℤ))
        (fun _ _ => (F.test_norm iF).le) (fun h _ => (M.slice_norm iM (h.val.val : ℤ)).le)
  have hcommon := by
    as_aux_lemma =>
      exact hbounded (N := N)
        (fun h k => (F.withOrbit_observable iF h).trans (F.withOrbit_observable iF k).symm)
        (fun h k => (M.slice_observable iM (h.val.val : ℤ)).trans
          (M.slice_observable iM (k.val.val : ℤ)).symm)
  have hweights := by
    as_aux_lemma =>
      exact hcommon (fun h x => multiplicativeDerivative f h.val x)
        (fun h _ x => multiplicativeDerivative_norm_le_one f hf h.val x)
  apply hweights
  intro h hh
  exact exists_native_sliced_product_correlation F M iF iM h (hcorr h hh)

theorem exists_native_fixed_product_verticalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I K : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N))
      (F : NativeUnitRankFamily (fun _ : Unit => 1) s r {h // h ∈ J} I p)
      (M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) K p)
      (iF : I) (iM : K) (H : Finset {h // h ∈ J}), H.Nonempty →
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p (fun _ : Unit => fun x =>
        multiplicativeDerivative f h.val x * star (M.eval iM
          (correlationInput (h.val.val : ℤ) (x.val : ℤ))) *
          star (F.eval h iF (fun _ => (x.val : ℤ)))))) →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hselect⟩ := exists_native_fixed_product_unit_data s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + Q + 2)
  refine ⟨C, hC, ?_⟩
  intro I K _ r N _ p f J F M iF iM H hH hp hf hdense hcorr
  obtain ⟨H₁, _, hH₁, hdense₁, n₁, _, hcount₁, V₁, n₂, _, hcount₂, V₂, hunit⟩ :=
    hselect J F M iF iM H hH hp hf hcorr
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * N ≤ (H₁.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + q)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H.card := mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hdense₁
  exact exists_native_correlation_of_sliced_unit_products J F M iM H₁ hH₁
    hfinaldensity hpC hqC hcount₁ hcount₂ V₁ V₂ hunit

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

def HasBoundedProductCorrelation {τ I : Type} [Fintype I]
    {s r degree N : ℕ} [NeZero N] (h : τ → ZMod N) (f : τ → ZMod N → ℂ)
    (mixedDim : ℕ) (B C Q : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
    ∃ F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ ((I × I) × (I × Fin k)) C,
      ∃ M : NativeBoundedMultidegreeFamily (mixedCorrelationDegree s) (Fin mixedDim × Fin k) Q,
        ∀ z, Nonempty (NativeVectorCorrelation degree N (B + 1)
          (fun ij : (Fin mixedDim × Fin k) × ((I × I) × (I × Fin k)) => fun a =>
            f z a * star (M.eval ij.1 (correlationInput ((h z).val : ℤ) (a.val : ℤ))) *
              star (F.eval z ij.2 (fun _ => (a.val : ℤ)))))

theorem HasBoundedProductCorrelation.mono {τ I : Type} [Fintype I]
    {s r degree N : ℕ} [NeZero N] {h : τ → ZMod N} {f : τ → ZMod N → ℂ}
    {mixedDim : ℕ} {B C Q B' C' Q' : ℝ}
    (hfamily : HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f mixedDim B C Q) (hBB' : B ≤ B') (hCC' : C ≤ C') (hQQ' : Q ≤ Q') :
    HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f mixedDim B' C' Q' := by
  obtain ⟨k, hk, hkB, F, M, hcorr⟩ := hfamily
  refine ⟨k, hk, hkB.trans (Real.exp_le_exp.mpr hBB'), F.mono hCC', M.mono hQQ', ?_⟩
  intro z
  obtain ⟨Cz⟩ := hcorr z
  exact ⟨Cz.mono (show B + 1 ≤ B' + 1 by linarith)⟩

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem HasUnitRankInducedCorrelationFamily.combineMixed
    {τ I : Type} [Fintype I] {s r N degree : ℕ} [NeZero N]
    {b p q P B C Q : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
    {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (f : τ → ZMod N → ℂ) (χ : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) Q)
    (hB : 0 ≤ B)
    (hfamily : D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree)
      t x y u c h₀ h
      (fun z i a => f z a * star (χ.evalCyclic N i (correlationInput (h z) a))) B C) :
    HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f χ.outputDim B C (productNiltestBudget (Q + B + 2 + 4)) := by
  obtain ⟨k, hk, hkB, F, m, hm, hmB, d, E, M, hMF, hM, hdata⟩ := hfamily
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hdata
  let F₀ := (D.markedQuotientMultidegree t).realification
  have hF : F₀ = M.filtration.realification := congrArg MultidegreeLieFiltration.realification hMF.symm
  let g := F₀.orbitEquivOfEq hF (D.localPhaseMarkedOrbit t x y u c h₀ m)
  obtain ⟨Ω, hΩ⟩ := χ.exists_product_with_bounded_family E M
    (mixedCorrelationDegree_sum s).symm g G hB hM hGn hGL
  refine ⟨k, hk, hkB, F, Ω, ?_⟩
  have hprod (ij : Fin χ.outputDim × Fin k) (a : Fin 2 → ℤ) :
      Ω.eval ij a = χ.eval ij.1 a * G ij.2 (QuotientGroup.mk
        (F₀.polynomialOrbitEval a (D.localPhaseMarkedOrbit t x y u c h₀ m))) / 2 :=
    (hΩ ij a).trans (congrArg (fun v : E.RealGroup => χ.eval ij.1 a * G ij.2 (QuotientGroup.mk v) / 2)
      (F₀.orbitEquivOfEq_eval hF (D.localPhaseMarkedOrbit t x y u c h₀ m) a))
  have hchi (i : Fin χ.outputDim) (z : τ) (a : ZMod N) :
      χ.evalCyclic N i (correlationInput (h z) a) =
        χ.eval i (correlationInput ((h z).val : ℤ) (a.val : ℤ)) := by
    unfold NativeMultidegreeNilcharacter.evalCyclic
    exact congrArg (χ.eval i) (map_correlationInput (fun z : ZMod N => (z.val : ℤ)) (h z) a)
  intro z
  obtain ⟨Cz⟩ := hcorr z
  obtain ⟨Dz⟩ := Cz.exists_half_signal
  refine ⟨Dz.mapCoordinates _ id ?_⟩
  intro ij a
  simp only [id_eq, hprod, hchi, star_div₀, star_mul, star_ofNat]
  ring

end NativeRankRelation.CommonData

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeUnitRankFamily.lie NativeUnitRankFamily.algebra
  NativeUnitRankFamily.topology NativeUnitRankFamily.topologicalAdd
  NativeUnitRankFamily.continuousSMul NativeUnitRankFamily.hausdorff
  NativeBoundedMultidegreeFamily.lie NativeBoundedMultidegreeFamily.algebra
  NativeBoundedMultidegreeFamily.topology NativeBoundedMultidegreeFamily.topologicalAdd
  NativeBoundedMultidegreeFamily.continuousSMul NativeBoundedMultidegreeFamily.hausdorff

theorem exists_native_product_verticalization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type} [Fintype I] {r N : ℕ} [NeZero N]
      {p : ℝ} {f : ZMod N → ℂ} (J : Finset (ZMod N)) (mixedDim : ℕ),
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → J.Nonempty →
      Real.exp (-p) * N ≤ (J.card : ℝ) →
      (mixedDim : ℝ) ≤ Real.exp p → (Fintype.card I : ℝ) ≤ Real.exp p →
      HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := s - 1)
        (fun h : {h // h ∈ J} => h.val) (fun h x => multiplicativeDerivative f h.val x)
        mixedDim p p p →
      Nonempty (NativeCorrelationStructure s r N ((p + C) ^ C) f) := by
  obtain ⟨a, _, hselect⟩ := exists_native_fixed_product_verticalization s
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (7 * X + 2 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro I _ r N _ p f J mixedDim hp hf hJ hdense hmixed hI hproduct
  classical
  obtain ⟨k, hk, hkB, F, M, hcorr⟩ := hproduct
  let G := {h // h ∈ J}
  have hG : (Finset.univ : Finset G).Nonempty := by
    obtain ⟨h, hh⟩ := hJ
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  have hlabels : (Fintype.card ((Fin mixedDim × Fin k) × ((I × I) × (I × Fin k))) : ℝ) ≤
      Real.exp (6 * p) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ ≤ (Real.exp p * Real.exp p) *
          ((Real.exp p * Real.exp p) * (Real.exp p * Real.exp p)) := by gcongr
      _ = Real.exp (6 * p) := by
        repeat rw [← Real.exp_add]
        congr 1
        ring
  obtain ⟨ij, H₀, _, hH₀, hdense₀, hfixed⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    (p := p + 1) (Finset.univ : Finset G) hG _ hlabels (fun h _ => hcorr h)
  rcases ij with ⟨iM, iF⟩
  let P := 7 * p + 2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpP : p ≤ P := by dsimp [P]; linarith
  have hp₁P : p + 1 ≤ P := by dsimp [P]; linarith
  have hfinal : (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Q, P, Polynomial.eval₂_pow] using hbudget p hp
  have hfiber : Real.exp (-(6 * p)) * J.card ≤ (H₀.card : ℝ) := by
    simpa only [G, Finset.card_univ, Fintype.card_coe] using hdense₀
  have hfixeddensity : Real.exp (-P) * N ≤ (H₀.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(7 * p)) * N :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by dsimp [P]; linarith))
          (Nat.cast_nonneg _)
      _ = Real.exp (-(6 * p)) * (Real.exp (-p) * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-(6 * p)) * J.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := hfiber
  have hselected := hselect J (F.mono hpP) (M.mono hpP) iF iM H₀ hH₀ hP hf hfixeddensity
  have hselected' : Nonempty (NativeCorrelationStructure s r N ((P + a) ^ a) f) := by
    apply hselected
    intro h hh
    obtain ⟨Wh⟩ := hfixed h hh
    exact ⟨Wh.mono hp₁P⟩
  obtain ⟨W⟩ := hselected'
  exact ⟨W.mono hfinal⟩

end Erdos3

end

end OAI

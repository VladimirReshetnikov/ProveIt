/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeProductVerticalization

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_derivative_correlators {s C N : ℕ} [NeZero N]
    (hI : CyclicNativeInverse s C) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-derivativeInverseBudget s p) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∃ (g : {h // h ∈ H} → ZMod N → ℂ)
        (_F : ∀ h, NativeCyclicModel s N ((derivativeInverseBudget s p + C) ^ C) (g h)),
        ∀ h, Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g h x)‖ := by
  classical
  obtain ⟨H, hH, hdense, hlarge⟩ := exists_many_large_gowers_derivatives s f hf hp hG
  have hchoose (h : {h // h ∈ H}) :
      ∃ g ∈ nativeCyclicFunctions s N ((derivativeInverseBudget s p + C) ^ C),
        Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g x)‖ :=
    hI (derivativeInverseBudget_ge_two s hp) (multiplicativeDerivative f h.val)
      (multiplicativeDerivative_norm_le_one f hf h.val) (hlarge h.val h.property)
  choose g hg hcorr using hchoose
  exact ⟨H, hH, hdense, g, (fun h => Classical.choice (hg h)), hcorr⟩

theorem exists_native_degree_one_derivative_correlators {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {p : ℝ} (hp : 0 ≤ p)
    (hG : Real.exp (-p) ≤ gowersNorm 3 f) :
    ∃ H : Finset (ZMod N), H.Nonempty ∧
      Real.exp (-(8 * p + 2)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      ∃ (g : {h // h ∈ H} → ZMod N → ℂ)
        (_F : ∀ h, NativeCyclicModel 1 N ((8 * p + 4) ^ 2) (g h)),
        ∀ h, Real.exp (-((8 * p + 4) ^ 2)) ≤
          ‖𝔼 x, multiplicativeDerivative f h.val x * star (g h x)‖ := by
  have hbudget : (derivativeInverseBudget 1 p + (2 : ℕ)) ^ 2 = (8 * p + 4) ^ 2 := by
    norm_num [derivativeInverseBudget]
    ring
  obtain ⟨H, hH, hdense, g, F, hcorr⟩ :=
    exists_native_derivative_correlators cyclicNativeInverse_one f hf hp hG
  refine ⟨H, hH, ?_, g, ?_, ?_⟩
  · simpa only [derivativeInverseBudget, Nat.reduceAdd, Nat.reducePow, Nat.cast_ofNat] using hdense
  · intro h
    rw [← hbudget]
    exact F h
  · intro h
    simpa only [hbudget] using hcorr h

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_common_observable_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h))
      (T : ∀ h, (D h).Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) → ∀ {N : ℕ} [NeZero N]
      (weight : G → ZMod N → ℂ), (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest (fun _ : Unit => 1)),
          H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          (∀ h, (S h).normBound ≤ 1 ∧ (S h).UnitIntervalValued ∧
            (S h).ComplexityLE ((p + C) ^ C)) ∧
          (∀ h k, (S h).observable = (S k).observable) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  obtain ⟨c, _, hmodels⟩ := exists_common_variable_dimension_niltest_model s
  obtain ⟨k, _, hfixed⟩ := exists_fixed_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C k) ^ k + (X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hcap N _ weight hweight hcorr
  let q := p + (p + c) ^ c + 2
  have hpow : 0 ≤ (p + c) ^ c := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hmodelq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hfixed0 : 0 ≤ (q + k) ^ k := by positivity
  have hcost : q + (q + k) ^ k + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfixedC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hmodelC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨h₀, hh₀, E, hE, H₁, P, hsub₁, hh₀', hlarge₁, hP⟩ :=
    hmodels D T H hH hp hT
  have hPeval (h : G) (hh : h ∈ H₁) (x : ZMod N) :
      (P h).evalCyclic N (fun _ => x) = (T h).evalCyclic N (fun _ => x) :=
    (hP h hh).2.2.1 _
  obtain ⟨H₂, S, hsub₂, hH₂, hlarge₂, hS, hsame, hcorrS⟩ :=
    hfixed E P H₁ ⟨h₀, hh₀'⟩ hq (hE.mono E hmodelq)
      (fun h hh => (hP h hh).1.mono hmodelq)
      (fun h hh => by rw [(hP h hh).2.1]; exact hcap h (hsub₁ hh)) weight
      (fun h hh x => hweight h (hsub₁ hh) x)
      (fun h hh => by
        simp_rw [hPeval h hh]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hcorr h (hsub₁ hh)))
  refine ⟨h₀, hh₀, E, hE.mono E hmodelC, H₂, S, hsub₂.trans hsub₁, hH₂, ?_,
    fun h => ⟨(hS h).2.1, (hS h).2.2.1, (hS h).2.2.2.mono hfixedC⟩, hsame, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤
          Real.exp (-((q + k) ^ k + (p + c) ^ c)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith)))
          (Nat.cast_nonneg _)
      _ = Real.exp (-((q + k) ^ k)) * (Real.exp (-((p + c) ^ c)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((q + k) ^ k)) * H₁.card :=
        mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_nonneg _)
      _ ≤ _ := hlarge₂
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hfixedC)).trans (hcorrS h hh)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

structure NativeUnitVerticalData {s N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
    (B : NativeCommonDerivativeModels s N p f) (V : NativeVerticalDerivativeData B) (q : ℝ) where
  tailDim : ℕ
  dimension : (tailDim + 1 : ℝ) ≤ Real.exp q
  observable : Fin (tailDim + 1) → B.model.Space → ℂ
  lipBound : ℝ≥0
  lip_bound : (lipBound : ℝ) ≤ Real.exp q
  unit : ∀ x, ∑ i, ‖observable i x‖ ^ 2 = 1
  norm : ∀ i x, ‖observable i x‖ ≤ 1
  lipschitz : letI := B.model.metricSpace; ∀ i, LipschitzWith lipBound (observable i)
  scalar : ∀ h x, observable 0 x = (B.test h).observable x / 2
  vertical : ∀ i z, z ∈ B.model.filtration.realification.subgroup s → ∀ x,
    observable i (z • x) =
      CircleFourier.character ((realifyFunctional V.frequency z.coord : ℝ) : CircleFourier.Circle) *
        observable i x

namespace NativeUnitVerticalData

variable {s N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} {V : NativeVerticalDerivativeData B}
  (U : NativeUnitVerticalData B V q)

noncomputable def mono {p' q' : ℝ} (hp : p ≤ p') (hq : q ≤ q') :
    NativeUnitVerticalData (B.mono hp) (V.mono hp) q' where
  tailDim := U.tailDim
  dimension := U.dimension.trans (Real.exp_le_exp.mpr hq)
  observable := U.observable
  lipBound := U.lipBound
  lip_bound := U.lip_bound.trans (Real.exp_le_exp.mpr hq)
  unit := U.unit
  norm := U.norm
  lipschitz := U.lipschitz
  scalar := U.scalar
  vertical := U.vertical

noncomputable def test (i : Fin (U.tailDim + 1)) (h : ZMod N) :
    B.model.Niltest (fun _ : Unit => 1) where
  orbit := (B.test h).orbit
  observable := U.observable i
  normBound := 1
  lipBound := U.lipBound
  norm_le := U.norm i
  lipschitz := U.lipschitz i

theorem test_zero_evalCyclic (h x : ZMod N) :
    (U.test 0 h).evalCyclic N (fun _ => x) = (B.test h).evalCyclic N (fun _ => x) / 2 :=
  U.scalar h _

theorem test_normalized (i : Fin (U.tailDim + 1)) (h : ZMod N) :
    B.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0 (U.test i h).orbit = 1 :=
  V.normalized h

theorem test_complexity (hpq : p ≤ q) (hq : 0 ≤ q)
    (i : Fin (U.tailDim + 1)) (h : ZMod N) : (U.test i h).ComplexityLE (q + 4) := by
  refine ⟨B.geometry.mono B.model (by linarith), ?_⟩
  have ht := niltest_log_bound_of_exp (1 : ℝ≥0) U.lipBound (a := 0) (b := q)
    (by norm_num) hq (by simp) U.lip_bound
  simpa only [test, zero_add] using ht

theorem test_zero_correlation (h : ZMod N) (hh : h ∈ B.shifts) :
    Real.exp (-(p + 1)) ≤
      ‖𝔼 x, multiplicativeDerivative f h x * star ((U.test 0 h).evalCyclic N (fun _ => x))‖ := by
  have heq :
      (𝔼 x, multiplicativeDerivative f h x * star ((U.test 0 h).evalCyclic N (fun _ => x))) =
      (𝔼 x, multiplicativeDerivative f h x * star ((B.test h).evalCyclic N (fun _ => x))) / 2 := by
    simp only [U.test_zero_evalCyclic, star_div₀, star_ofNat, ← mul_div_assoc, ← Finset.expect_div]
  rw [heq, norm_div]
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [htwo]
  have hsmall : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
    simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
  exact hsmall.trans (div_le_div_of_nonneg_right (B.correlation h hh) (by norm_num))

end NativeUnitVerticalData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_inverse_quadruples {s C N : ℕ} [NeZero N]
    (hI : CyclicNativeInverse s C) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    {p : ℝ} (hp : 0 ≤ p) (hG : Real.exp (-p) ≤ gowersNorm (s + 2) f) :
    let q := derivativeInverseBudget s p
    let r := (q + C) ^ C
    let rho := (Real.exp (-q) * Real.exp (-r)) ^ 4 / 2
    ∃ (H : Finset (ZMod N)) (g : ZMod N → ZMod N → ℂ), H.Nonempty ∧
      Real.exp (-q) * Fintype.card (ZMod N) ≤ (H.card : ℝ) ∧
      (∀ h ∈ H, g h ∈ nativeCyclicFunctions s N r) ∧
      (∀ h x, ‖g h x‖ ≤ 1) ∧
      (∀ h, h ∉ H → ∀ x, g h x = 0) ∧
      (∀ h ∈ H, Real.exp (-r) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖) ∧
      ∃ Q : Finset (ZMod N × ZMod N × ZMod N), Q.Nonempty ∧
        rho * (Fintype.card (ZMod N) : ℝ) ^ 3 ≤ (Q.card : ℝ) ∧
        ∀ t ∈ Q, t.2.1 ∈ H ∧ t.2.1 - t.1 ∈ H ∧ t.2.2 ∈ H ∧ t.2.2 - t.1 ∈ H ∧
          rho ≤ additiveQuadrupleCorrelation g t.1 t.2.1 t.2.2 := by
  classical
  dsimp only
  obtain ⟨H, hH, hdense, g₀, F, hcorr⟩ := exists_native_derivative_correlators hI f hf hp hG
  let g : ZMod N → ZMod N → ℂ := fun h => if hh : h ∈ H then g₀ ⟨h, hh⟩ else 0
  have hnative (h : ZMod N) (hh : h ∈ H) :
      g h ∈ nativeCyclicFunctions s N ((derivativeInverseBudget s p + C) ^ C) := by
    simp only [g, dite_eq_left hh]
    exact ⟨F ⟨h, hh⟩⟩
  have hzero (h : ZMod N) (hh : h ∉ H) (x : ZMod N) : g h x = 0 := by
    simp only [g, dite_eq_right hh, Pi.zero_apply]
  have hunit (h x : ZMod N) : ‖g h x‖ ≤ 1 := by
    by_cases hh : h ∈ H
    · exact nativeCyclicFunctions_norm (hnative h hh) x
    · rw [hzero h hh x, norm_zero]
      norm_num
  have hlarge (h : ZMod N) (hh : h ∈ H) :
      Real.exp (-((derivativeInverseBudget s p + C) ^ C)) ≤
        ‖𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ := by
    simpa only [g, dite_eq_left hh] using hcorr ⟨h, hh⟩
  obtain ⟨Q, hQ, hQdense, hQcorr⟩ := exists_many_correlated_additive_quadruples
    f g H hf hunit hzero (Real.exp_pos _) (Real.exp_pos _) hdense hlarge
  exact ⟨H, g, hH, hdense, hnative, hunit, hzero, hlarge, Q, hQ, hQdense, hQcorr⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCyclicModel.lie NativeCyclicModel.algebra
  NativeCyclicModel.topology NativeCyclicModel.topologicalAdd
  NativeCyclicModel.continuousSMul NativeCyclicModel.hausdorff

theorem exists_native_common_derivative_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) →
      Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeCommonDerivativeModels s N ((p + D) ^ D) f) := by
  classical
  obtain ⟨a, _, hcommon⟩ := RationalFilteredNilmanifold.exists_common_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := Polynomial.C (2 ^ (s + 2)) * X + 2
  let R := (Q + Polynomial.C C) ^ C
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (R + Polynomial.C a) ^ a + 2)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  let q := derivativeInverseBudget s p
  let r := (q + C) ^ C
  have hq : 0 ≤ q := by dsimp [q, derivativeInverseBudget]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hshared : 0 ≤ (r + a) ^ a := by positivity
  have hcost : q + (r + a) ^ a + 2 ≤ (p + D) ^ D := by
    simpa [Q, R, X, q, r, derivativeInverseBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hsharedD : (r + a) ^ a ≤ (p + D) ^ D := by linarith
  obtain ⟨H, hH, hdense, g, F, hcorr⟩ := exists_native_derivative_correlators hI f hf hp hG
  let J := {h // h ∈ H}
  have hJ : (Finset.univ : Finset J).Nonempty := by
    obtain ⟨h, hh⟩ := hH
    exact ⟨⟨h, hh⟩, Finset.mem_univ _⟩
  obtain ⟨h₀, _, E, hE, H₁, S, _, hH₁, hdense₁, hS, hsame, hcS⟩ :=
    hcommon (fun h : J => (F h).model) (fun h => (F h).test) Finset.univ hJ hr
      (fun h => (F h).complexity) (fun h _ => (F h).norm)
      (fun h x => multiplicativeDerivative f h.val x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h.val x)
      (fun h _ => by simpa only [← (F h).eval] using hcorr h)
  let H' := H₁.image Subtype.val
  let selected (h : ZMod N) : J := if hh : h ∈ H then ⟨h, hh⟩ else h₀
  have hcard : H'.card = H₁.card := Finset.card_image_of_injective _ Subtype.val_injective
  have huniv : (Finset.univ : Finset J).card = H.card := by simp [J]
  have hfinaldensity : Real.exp (-((p + D) ^ D)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(q + (r + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith)))
          (Nat.cast_nonneg _)
      _ = Real.exp (-((r + a) ^ a)) * (Real.exp (-q) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((r + a) ^ a)) * H.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_nonneg _)
      _ ≤ _ := by simpa only [hcard, huniv] using hdense₁
  refine ⟨{
    L := (F h₀).L
    dim := (F h₀).dim
    model := E
    geometry := hE.mono E hsharedD
    shifts := H'
    nonempty := hH₁.image _
    density := hfinaldensity
    test := fun h => S (selected h)
    norm := fun h => (hS (selected h)).1
    complexity := fun h => (hS (selected h)).2.2.mono hsharedD
    common_observable := fun h k => hsame (selected h) (selected k)
    correlation := ?_ }⟩
  intro h hh
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hh
  have hselect : selected j.val = j := by simp only [selected, dite_eq_left j.property]
  rw [hselect]
  exact (Real.exp_le_exp.mpr (neg_le_neg hsharedD)).trans (hcS j hj)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem NativeCommonDerivativeModels.exists_large_common_observable {s N : ℕ} [NeZero N]
    {p : ℝ} {f : ZMod N → ℂ} (B : NativeCommonDerivativeModels s N p f)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ∃ y : B.model.Space, Real.exp (-p) ≤ ‖(B.test 0).observable y‖ := by
  obtain ⟨h, hh⟩ := B.nonempty
  have hmean : Real.exp (-p) ≤ 𝔼 x, ‖(B.test h).evalCyclic N (fun _ => x)‖ := by
    apply (B.correlation h hh).trans
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply Finset.expect_le_expect
    intro x _
    rw [norm_mul, norm_star]
    exact mul_le_of_le_one_left (norm_nonneg _) (multiplicativeDerivative_norm_le_one f hf h x)
  obtain ⟨x, _, hx⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  refine ⟨QuotientGroup.mk (B.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (B.test h).orbit), ?_⟩
  rw [B.common_observable 0 h]
  exact hx

theorem exists_native_unit_vertical_data (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (B : NativeCommonDerivativeModels s N p f) (V : NativeVerticalDerivativeData B),
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) →
      Nonempty (NativeUnitVerticalData B V ((p + C) ^ C)) := by
  obtain ⟨C, hC, hcomplete⟩ := RationalFilteredNilmanifold.exists_native_unit_vertical_completion s
  refine ⟨C, hC, ?_⟩
  intro N _ p f B V hp hf
  obtain ⟨y, hy⟩ := B.exists_large_common_observable hf
  obtain ⟨n, _, hn, K, hK, v, hv0, hvunit, hvnorm, hvLip, hvvertical⟩ :=
    hcomplete B.model (B.test 0) hp (B.complexity 0) (B.norm 0) V.frequency
      (V.vertical 0) y hy
  refine ⟨{
    tailDim := n
    dimension := hn
    observable := v
    lipBound := K
    lip_bound := hK
    unit := hvunit
    norm := hvnorm
    lipschitz := hvLip
    scalar := ?_
    vertical := hvvertical
  }⟩
  intro h x
  rw [hv0, B.common_observable 0 h]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_normalized_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hmodels⟩ := exists_native_common_derivative_models hI
  obtain ⟨b, _, hnormalize⟩ := exists_normalized_native_common_models s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B⟩ := hmodels hp f hf hG
  obtain ⟨R, hR⟩ := hnormalize hq hf B
  exact ⟨R.mono hcost, hR⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_vertical_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
        Nonempty (NativeVerticalDerivativeData R) := by
  obtain ⟨a, _, hmodels⟩ := exists_normalized_native_inverse_models hI
  obtain ⟨b, _, hvertical⟩ := exists_native_vertical_derivative_models
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨B, hB⟩ := hmodels hp f hf hG
  obtain ⟨R, ⟨V⟩⟩ := hvertical hq hf B hB
  exact ⟨R.mono hcost, ⟨V.mono hcost⟩⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_unit_vertical_native_inverse_models {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ R : NativeCommonDerivativeModels s N ((p + D) ^ D) f,
      ∃ V : NativeVerticalDerivativeData R,
        Nonempty (NativeUnitVerticalData R V ((p + D) ^ D)) := by
  obtain ⟨a, _, hmodels⟩ := exists_vertical_native_inverse_models hI
  obtain ⟨b, _, hunit⟩ := exists_native_unit_vertical_data s
  let X : Polynomial ℕ := Polynomial.X
  let P := (X + Polynomial.C a) ^ a
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hp0 : 0 ≤ (p + a) ^ a := by positivity
  have hp1 : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have htotal : (p + a) ^ a + ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  have h0 : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  have h1 : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by linarith
  obtain ⟨B, ⟨V⟩⟩ := hmodels hp f hf hG
  obtain ⟨U⟩ := hunit B V hp0 hf
  exact ⟨B.mono h0, V.mono h0, ⟨U.mono h0 h1⟩⟩

end Erdos3

end

end OAI

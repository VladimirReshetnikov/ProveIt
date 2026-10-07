import OAI.Combinatorics.Progressions.Linear.AdaptedRankCorrelation
import OAI.Combinatorics.Progressions.Linear.NativeRankFamilyConstruction
import OAI.Combinatorics.Progressions.Linear.NativeRankIteration

namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def toCorrelationStructure (hcor : p + 1 ≤ q) (hq : 2 ≤ q) :
    NativeCorrelationStructure s r N q f := by
  have hpq : p ≤ q := by linarith
  have hq0 : 0 ≤ q := by linarith
  refine {
    shifts := B.shifts
    nonempty := B.nonempty
    density := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq))
      (Nat.cast_nonneg _)).trans B.density
    mixed := NativeMultidegreeNilcharacter.constOne (mixedCorrelationDegree s) hq0
    family := W.toFamily hpq
    correlation := ?_
  }
  intro h hh
  apply NativeVectorCorrelation.exists_of_mean (s - 1) N _ hq
  refine ⟨((0 : Fin 1), (0 : Fin (W.unit.tailDim + 1))), ?_⟩
  have hc := (Real.exp_le_exp.mpr (neg_le_neg hcor)).trans (W.toFamily_correlation hpq h hh)
  simpa only [nativeCorrelationResidual, NativeMultidegreeNilcharacter.constOne_evalCyclic,
    star_one, mul_one] using hc

end Erdos3.NativeDegreeRankDerivativeData

end

section

namespace Erdos3

theorem exists_initial_native_correlation_structure {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      Nonempty (NativeCorrelationStructure s s N ((p + D) ^ D) f) := by
  obtain ⟨a, _, hmodels⟩ := exists_degree_rank_native_inverse_models hI
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C 2)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : (p + a) ^ a + 2 ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hqD : (p + a) ^ a ≤ (p + D) ^ D := by linarith
  obtain ⟨B, ⟨W⟩⟩ := hmodels hp f hf hG
  exact ⟨(W.mono le_rfl hqD).toCorrelationStructure (by linarith) (by linarith)⟩

theorem exists_initial_native_correlation_structure_one :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      Nonempty (NativeCorrelationStructure 1 1 N ((p + D) ^ D) f) :=
  exists_initial_native_correlation_structure cyclicNativeInverse_one

end Erdos3

end

section

namespace Erdos3

theorem exists_adapted_initial_correlation_structure {s C : ℕ} (hI : CyclicNativeInverse s C) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ W : NativeCorrelationStructure s s N ((p + D) ^ D) f, W.family.AdaptedCoordinates := by
  obtain ⟨a, _, hinit⟩ := exists_initial_native_correlation_structure hI
  obtain ⟨b, _, hadapt⟩ := exists_adapted_correlation_structure
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨D, hD, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨D, hD, ?_⟩
  intro N _ p hp f hf hG
  obtain ⟨W⟩ := hinit hp f hf hG
  obtain ⟨V, hV, _⟩ := hadapt W
  have hcost : ((p + a) ^ a + b) ^ b ≤ (p + D) ^ D := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨V.mono hcost, hV⟩

theorem exists_adapted_initial_correlation_structure_one :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ W : NativeCorrelationStructure 1 1 N ((p + D) ^ D) f, W.family.AdaptedCoordinates :=
  exists_adapted_initial_correlation_structure cyclicNativeInverse_one

end Erdos3

end

section

namespace Erdos3

theorem exists_retained_inverse_intervals {s A : ℕ} (hs : 2 ≤ s)
    (hI : CyclicNativeInverse s A) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm (s + 2) f →
      ∃ q : ℝ, 0 ≤ q ∧ q ≤ (p + C) ^ C ∧
      ∃ W : NativeCorrelationStructure s 0 N q f,
      ∃ r : ℝ, 0 ≤ r ∧ r ≤ (p + C) ^ C ∧
      ∃ B : NativeRetainedMultilinearIntervalFamily W r,
      ∃ M : NativeMixedCorrelation s N ((p + C) ^ C) f,
        M.shifts = W.shifts ∧ M.mixed.dim = W.mixed.dim ∧
        NativeIntegerVectorEquivalence s ((p + C) ^ C) M.mixed.eval
          (fun k x => B.mixed.eval k (fun j => x j.1)) := by
  cases s with
  | zero => omega
  | succ s =>
    obtain ⟨a, _, hinitial⟩ := exists_initial_native_correlation_structure hI
    obtain ⟨b, _, hzero⟩ := exists_native_rank_zero_reduction (s + 1) hs (s + 1)
    obtain ⟨c, _, hfamily⟩ := exists_native_retained_multilinear_interval_family (s + 1)
    let X : Polynomial ℕ := Polynomial.X
    let P := (X + Polynomial.C a) ^ a
    let Q := (P + Polynomial.C b) ^ b
    let R := (Q + Polynomial.C c) ^ c
    let T := Q + 4
    let U := (T + 2) ^ 2 + T + (T + (T ^ 2 + T + 3) ^ 2) + T ^ 2 + 4
    obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + Q + R + U)
    refine ⟨C, hC, ?_⟩
    intro N _ p hp hN f hf hG
    let p₀ := (p + a) ^ a
    let q := (p₀ + b) ^ b
    let r := (q + c) ^ c
    have hp₀ : 0 ≤ p₀ := by dsimp [p₀]; positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hu : 0 ≤ productNiltestBudget (q + 4) := by
      unfold productNiltestBudget productObservableLipBudget
      positivity
    have hsum : p₀ + q + r + productNiltestBudget (q + 4) ≤ (p + C) ^ C := by
      simpa [X, P, Q, R, T, U, p₀, q, r, productNiltestBudget,
        productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp
    have hqC : q ≤ (p + C) ^ C := by linarith
    have hrC : r ≤ (p + C) ^ C := by linarith
    have huC : productNiltestBudget (q + 4) ≤ (p + C) ^ C := by linarith
    obtain ⟨W₁⟩ := hinitial hp f hf hG
    obtain ⟨W⟩ := hzero W₁ hf ((Real.exp_le_exp.mpr hqC).trans hN)
    obtain ⟨B⟩ := hfamily W hf
    let M := (W.absorbRankZero hq).mono huC
    exact ⟨q, hq, hqC, W, r, hr, hrC, B, M, rfl, rfl, B.equivalence.mono hrC⟩

end Erdos3

end

end OAI

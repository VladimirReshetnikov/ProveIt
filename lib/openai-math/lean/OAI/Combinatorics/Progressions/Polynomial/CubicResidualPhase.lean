/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.HigherResidualRowDifferences

namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

namespace NativeMixedCorrelation

theorem exists_fixed_residual_coordinate {s N : ℕ} [NeZero N] {p : ℝ}
    {f : ZMod N → ℂ} (W : NativeMixedCorrelation s N p f) :
    ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
      Real.exp (-(2 * p)) * N ≤ (H.card : ℝ) ∧
      ∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N p
        (fun _ : Unit => nativeMixedResidual f W.mixed h i)) := by
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := NativeVectorCorrelation.exists_fixed_coordinate
    W.shifts W.nonempty (nativeMixedResidual f W.mixed)
    (by simpa only [Fintype.card_fin] using W.mixed.output_bound) W.correlation
  refine ⟨i, H, hsub, hH, ?_, hcorr⟩
  have hW : Real.exp (-p) * N ≤ (W.shifts.card : ℝ) := by
    simpa only [ZMod.card] using W.density
  calc
    Real.exp (-(2 * p)) * N = Real.exp (-p) * (Real.exp (-p) * N) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ Real.exp (-p) * W.shifts.card := mul_le_mul_of_nonneg_left hW (Real.exp_nonneg _)
    _ ≤ H.card := hdense

theorem exists_cubic_residual_phases :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}, 0 ≤ p →
      (∀ x, ‖f x‖ ≤ 1) → ∀ W : NativeMixedCorrelation 2 N p f,
      ∃ i : Fin W.mixed.outputDim, ∃ H ⊆ W.shifts, H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ θ : ZMod N → ℝ, ∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 n : ZMod N, nativeMixedResidual f W.mixed h i n *
            star (CircleFourier.character (((n.val : ℝ) * θ h : ℝ) : CircleFourier.Circle))‖ := by
  obtain ⟨A, _, hphase⟩ := exists_stepOne_scalar_phase_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * X + (X + Polynomial.C A) ^ A)
  refine ⟨C, hC, ?_⟩
  intro N _ p f hp hf W
  classical
  have hcost : 2 * p + (p + A) ^ A ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + A) ^ A := by positivity
  have h2p : 2 * p ≤ (p + C) ^ C := by linarith
  have hphaseCost : (p + A) ^ A ≤ (p + C) ^ C := by linarith
  obtain ⟨i, H, hsub, hH, hdense, hcorr⟩ := W.exists_fixed_residual_coordinate
  have hlinear (h : ZMod N) (hh : h ∈ H) : ∃ β : ℝ,
      Real.exp (-((p + A) ^ A)) ≤ ‖𝔼 n : ZMod N, nativeMixedResidual f W.mixed h i n *
        star (CircleFourier.character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
    obtain ⟨V⟩ := hcorr h hh
    apply hphase V.model hp V.test V.complexity (nativeMixedResidual f W.mixed h i)
    · intro n
      change ‖multiplicativeDerivative f h n * star (W.mixed.evalCyclic N i (correlationInput h n))‖ ≤ 1
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (multiplicativeDerivative_norm_le_one f hf h n)).trans (W.mixed.norm_eval _ _)
    · exact V.correlation
  let θ (h : ZMod N) := if hh : h ∈ H then Classical.choose (hlinear h hh) else 0
  refine ⟨i, H, hsub, hH, ?_, θ, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h2p))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    dsimp only [θ]
    rw [dite_eq_left hh]
    exact (Real.exp_le_exp.mpr (neg_le_neg hphaseCost)).trans (Classical.choose_spec (hlinear h hh))

end NativeMixedCorrelation

theorem exists_cubic_fixed_phase_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      Real.exp ((p + C) ^ C) ≤ (N : ℝ) →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 4 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 2) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∃ θ : ZMod N → ℝ, ∀ h ∈ H,
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n)) *
                star (CircleFourier.character (((n.val : ℝ) * θ h : ℝ) : CircleFourier.Circle))‖ := by
  obtain ⟨A, _, hmixed⟩ := exists_cubic_native_mixed_correlation
  obtain ⟨B, _, hphase⟩ := NativeMixedCorrelation.exists_cubic_residual_phases
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp hN f hf hGowers
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (q + B) ^ B := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hphaseC : (q + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨W⟩ := hmixed hp ((Real.exp_le_exp.mpr hqC).trans hN) f hf hGowers
  obtain ⟨i, H, _, hH, hdense, θ, hcorr⟩ := hphase hq hf W
  refine ⟨H, hH, ?_, W.mixed.mono hqC, i, θ, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hphaseC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hphaseC)).trans (hcorr h hh)

end Erdos3

end

end OAI

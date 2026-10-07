import OAI.Combinatorics.Progressions.Estimates.NativeLocalPivotVerticalPartners
import OAI.Combinatorics.Progressions.Nilpotent.CoordinateNiltestSplitting

namespace OAI

section

namespace Erdos3

theorem exists_coordinate_reduction_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + b) ^ b ≤ (p + C) ^ C ∧
      3 * p + (p + a) ^ a + 1 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Y := (X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (3 * X + Y + (Y + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, fun p hp => ?_⟩
  have hY : 0 ≤ (p + a) ^ a := by positivity
  have hZ : 0 ≤ ((p + a) ^ a + b) ^ b := by positivity
  have hb : 3 * p + (p + a) ^ a + ((p + a) ^ a + b) ^ b + 2 ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  constructor
  · linarith only [hp, hY, hZ, hb]
  constructor <;> linarith only [hp, hY, hZ, hb]

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

def CoordinateErrorReductionStatement (σ : Type) [Fintype σ] [DecidableEq σ] (s C : ℕ) : Prop :=
  ∀ (i : σ) {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
    (T : D.Niltest (fun _ : σ => 1)), 2 ≤ p → T.ComplexityLE p →
    ∀ {G X : Type} (H : Finset G), H.Nonempty →
    ∀ (S : G → Finset X) (b : G → σ → ℤ) (n : G → X → ℤ) (f : G → X → ℂ),
    (∀ h ∈ H, (S h).Nonempty) → (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ Real.exp p) →
    (∀ h ∈ H, Real.exp (-p) ≤
      ‖𝔼 x ∈ S h, f h x * T.eval (Function.update (b h) i (n h x))‖) →
    ∃ (weight : ℤ → ℂ) (Q : Finset G), (∀ z, ‖weight z‖ ≤ 1) ∧ Q ⊆ H ∧ Q.Nonempty ∧
      Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (Q.card : ℝ) ∧
      ∀ h ∈ Q, ∃ v : ℤ → ℂ,
        (∀ z, ‖v z‖ ≤ 1) ∧
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) (s - 1) ((p + C) ^ C)
          (fun x => v (x ()))) ∧
        Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x ∈ S h, f h x * weight (n h x) * v (n h x)‖

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCoordinateSplit.lie NativeCoordinateSplit.algebra
  NativeCoordinateSplit.topology NativeCoordinateSplit.topologicalAdd
  NativeCoordinateSplit.continuousSMul NativeCoordinateSplit.hausdorff

theorem exists_coordinate_error_reduction (σ : Type) [Fintype σ] [DecidableEq σ] [Nonempty σ]
    (s : ℕ) : ∃ C : ℕ, 2 ≤ C ∧ CoordinateErrorReductionStatement σ s C := by
  obtain ⟨a, _, hsplit⟩ := exists_coordinate_niltest_splitting σ s 2
  obtain ⟨b, _, hfreeze⟩ := NativeCoordinateSplit.exists_second_expansion_budget σ s
  obtain ⟨C, hC, hbudget⟩ := exists_coordinate_reduction_budget a b
  refine ⟨C, hC, ?_⟩
  intro i L _ _ _ _ _ _ d D p T hp hT G X H hH S z n f hS hf hcorr
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  let U := T.conjugate.expNormalize p
  let epsilon := Real.exp (-(3 * p + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [hp0, sq_nonneg p]
  obtain ⟨R⟩ := hsplit i U (T.conjugate.expNormalize_complexity hT)
    (T.conjugate.expNormalize_norm hT) epsilon (Real.exp_pos _) hscale
  let sample (h : G) (x : X) := Function.update (z h) i (n h x)
  let f₀ (h : G) (x : X) := (Real.exp (-p) : ℂ) * f h x
  have hf₀ : ∀ h ∈ H, ∀ x ∈ S h, ‖f₀ h x‖ ≤ 1 :=
    fun h hh x hx => exp_scaled_norm_le_one (hf h hh x hx)
  have hc₀ : ∀ h ∈ H, Real.exp (-(3 * p)) ≤
      ‖𝔼 x ∈ S h, f₀ h x * star (U.eval (sample h x))‖ := by
    intro h hh
    have hc := finite_double_normalization (S h) (f h) (fun x => T.eval (sample h x)) p (hcorr h hh)
    simpa only [f₀, U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
      RationalFilteredNilmanifold.Niltest.eval_conjugate, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj, mul_assoc, mul_left_comm, mul_comm] using hc
  have hepsilon : epsilon ≤ Real.exp (-(3 * p)) / 2 := by
    simpa only [epsilon, show -(3 * p + 1) = -(3 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(3 * p))
  obtain ⟨j, Q, hQH, hQ, hsize, hterm⟩ := R.exists_fixed_correlating_term
    H hH S hS sample f₀ (Real.exp_pos _) hepsilon hf₀ hc₀
  let weight (x : ℤ) := star (R.firstFactor j x)
  have hweight (x : ℤ) : ‖weight x‖ ≤ 1 := by
    simpa only [weight, norm_star] using R.firstFactor_norm j x
  have hfirst (h : G) (x : X) : (R.test false j).eval (sample h x) = R.firstFactor j (n h x) := by
    simpa only [sample, Function.update_self] using R.first_eval_firstFactor j (sample h x)
  have hsmall : Real.exp (-(3 * p + (p + a) ^ a + 1)) ≤
      Real.exp (-(3 * p)) / (2 * Real.exp ((p + a) ^ a)) := by
    calc
      _ = Real.exp (-(3 * p + (p + a) ^ a) - 1) := by congr 1; ring
      _ ≤ Real.exp (-(3 * p + (p + a) ^ a)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by
        rw [show -(3 * p + (p + a) ^ a) = -(3 * p) - (p + a) ^ a by ring, Real.exp_sub]
        ring
  refine ⟨weight, Q, hweight, hQH, hQ, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp0).1)) (Nat.cast_nonneg H.card)).trans hsize
  · intro h hh
    let v (x : ℤ) := star ((R.test true j).eval (Function.update (z h) i x))
    obtain ⟨E, _⟩ := hfreeze R j (z h)
    refine ⟨v, ?_, ⟨E.conjugate.mono (hbudget p hp0).2.1⟩, ?_⟩
    · intro x
      simpa only [v, norm_star] using ((R.test true j).norm_eval_le (Function.update (z h) i x)).trans
        (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
    · have hc : Real.exp (-(3 * p)) / (2 * Real.exp ((p + a) ^ a)) ≤
          ‖𝔼 x ∈ S h, ((Real.exp (-p) : ℂ) * f h x) * (weight (n h x) * v (n h x))‖ := by
        simpa only [f₀, hfirst, weight, v, sample, star_mul,
          mul_assoc, mul_left_comm, mul_comm] using hterm h hh
      have hout := finite_remove_normalization (S h) (f h)
        (fun x => weight (n h x) * v (n h x)) hp0 hc
      have hthreshold := (Real.exp_le_exp.mpr (neg_le_neg (hbudget p hp0).2.2)).trans
        (hsmall.trans hout)
      simpa only [mul_assoc] using hthreshold

end Erdos3

end

end OAI

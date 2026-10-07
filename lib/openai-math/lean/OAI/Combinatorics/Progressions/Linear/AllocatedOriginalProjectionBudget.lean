import OAI.Combinatorics.Progressions.Dynamics.AllocatedChosenScaleBudget
import OAI.Combinatorics.Progressions.Sampling.AllocatedUnifiedSamplingBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedOriginalProjectionBudget (m dim A : ℕ) (p E T : ℝ) : ℝ :=
  allocatedUnifiedSamplingBudget m dim A (allocatedChosenScaleBudget m p E T) p E + E + 3

theorem allocatedOriginalProjectionBudget_bounds (m dim A : ℕ) {p E T : ℝ}
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hT : 0 ≤ T) :
    let P := allocatedChosenScaleBudget m p E T
    let Q := allocatedUnifiedSamplingBudget m dim A P p E
    let B := allocatedOriginalProjectionBudget m dim A p E T
    0 ≤ B ∧ Q ≤ B ∧ P ≤ B ∧ E + 3 ≤ B := by
  have hP := (allocatedChosenScaleBudget_bounds m hp hE hT).1
  obtain ⟨_, _, _, hQ, _, _, hPQ, _, _, _⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hE
  dsimp only [allocatedOriginalProjectionBudget]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem exists_allocatedOriginalThreshold_bound (m dim A Kproj Ktuple : ℕ) (hKtuple : 1 ≤ Ktuple) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E T : ℝ}, 0 ≤ p → 0 ≤ E → 0 ≤ T →
      (allocatedOriginalProjectionBudget m dim A p E T + Kproj) ^ Kproj ≤
        (p + E + T + a) ^ a ∧
      (p + E + T + Ktuple) ^ Ktuple ≤ (p + E + T + a) ^ a := by
  obtain ⟨c, _, hshift⟩ := exists_natPolynomial_eval_budget
    ((2 * Polynomial.X + 3 + Polynomial.C Kproj) ^ Kproj)
  obtain ⟨b, _, hbudget⟩ := exists_allocatedUnifiedSamplingThreshold_bound m dim A c
  obtain ⟨a₀, ha₀, hchosen⟩ := exists_allocatedChosenThreshold_bound m A b
  refine ⟨max a₀ Ktuple, ha₀.trans (le_max_left _ _), ?_⟩
  intro p E T hp hE hT
  let P := allocatedChosenScaleBudget m p E T
  let Q := allocatedUnifiedSamplingBudget m dim A P p E
  have hP : 0 ≤ P := (allocatedChosenScaleBudget_bounds m hp hE hT).1
  obtain ⟨_, _, _, hQ, _, _, _, _, hEQ, _⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hE
  have hproj : (allocatedOriginalProjectionBudget m dim A p E T + Kproj) ^ Kproj ≤
      (Q + c) ^ c := by
    calc
      _ ≤ (2 * Q + 3 + Kproj) ^ Kproj := by
        apply pow_le_pow_left₀
          (add_nonneg (allocatedOriginalProjectionBudget_bounds m dim A hp hE hT).1 (Nat.cast_nonneg _))
        dsimp [allocatedOriginalProjectionBudget, Q, P] at *
        linarith
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hshift Q hQ
  have hlarge := hchosen hp hE hT
  have hu : 0 ≤ p + E + T := by positivity
  exact ⟨(hproj.trans (hbudget hP hp hE)).trans
      (hlarge.2.2.trans (shifted_power_self_mono hu (by omega) (le_max_left _ _))),
    shifted_power_self_mono hu hKtuple (le_max_right _ _)⟩

theorem originalTupleProjectionPrecision_bound {E Z : ℝ} (hZ : 1 / 2 ≤ Z) :
    (2 * Real.exp (-(E + 4)) + Real.exp (-(E + 4))) / Z + Real.exp (-(E + 1)) ≤
      Real.exp (-E) := by
  have hZpos : 0 < Z := by linarith
  have hη := (Real.exp_pos (-(E + 4))).le
  have hfirst : (2 * Real.exp (-(E + 4)) + Real.exp (-(E + 4))) / Z ≤
      6 * Real.exp (-(E + 4)) := by
    apply (div_le_iff₀ hZpos).mpr
    nlinarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hsix : (6 : ℝ) ≤ Real.exp 3 := by
    calc
      _ = (2 : ℝ) * 3 := by norm_num
      _ ≤ Real.exp 1 * Real.exp 2 := mul_le_mul htwo hthree (by norm_num) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; norm_num
  have hsmall : 6 * Real.exp (-(E + 4)) ≤ Real.exp (-(E + 1)) := by
    calc
      _ ≤ Real.exp 3 * Real.exp (-(E + 4)) := mul_le_mul_of_nonneg_right hsix hη
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  calc
    _ ≤ 2 * Real.exp (-(E + 1)) := by linarith
    _ ≤ Real.exp 1 * Real.exp (-(E + 1)) := mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Lattices.ScalarLatePrimeCutoffPowerBudget

namespace OAI

section

namespace Erdos3

theorem exists_scalarEndpointScale_power_budget
    (n r E C H early : ℕ) (hE : 2 ≤ E) (hC : 2 ≤ C)
    (hH : max 1 early ≤ H) :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ p : ℝ, 2 ≤ p →
      let b := (p + 2) ^ H
      let scalarInput := (b + 2) ^ E
      let target := 8 * ((r * n : ℕ) + 1 : ℝ) * (scalarInput + 1)
      let t := (target + 2) ^ C
      p ≤ t ∧ (p + 2) ^ early ≤ t ∧
        (r : ℝ) * Real.exp t ≤ Real.exp ((p + 2) ^ L) := by
  let tPoly : Polynomial ℕ :=
    (Polynomial.C (8 * (r * n + 1)) *
      ((((Polynomial.X + 2) ^ H + 2) ^ E) + 1) + 2) ^ C
  obtain ⟨L, hL, hbound⟩ :=
    exists_natPolynomial_fixed_power_budget (tPoly + Polynomial.C r)
  refine ⟨L, hL, ?_⟩
  intro p hp b scalarInput target t
  have hp0 : 0 ≤ p := by linarith
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hscalar0 : 0 ≤ scalarInput := by dsimp only [scalarInput]; positivity
  have htarget0 : 0 ≤ target := by dsimp only [target]; positivity
  have hpB : p ≤ b := le_power_budget hp0 ((le_max_left 1 early).trans hH)
  have hBscalar : b ≤ scalarInput := le_power_budget hb0 (by omega)
  have hcoefficient : (1 : ℝ) ≤ 8 * ((r * n : ℕ) + 1 : ℝ) := by
    have := Nat.cast_nonneg (α := ℝ) (r * n)
    linarith
  have hscalarTarget : scalarInput ≤ target := by
    calc
      _ ≤ scalarInput + 1 := by linarith
      _ ≤ _ := le_mul_of_one_le_left (by linarith) hcoefficient
  have hTargetT : target ≤ t := le_power_budget htarget0 (by omega)
  have hBT : b ≤ t := hBscalar.trans (hscalarTarget.trans hTargetT)
  have hearlyB : (p + 2) ^ early ≤ b :=
    pow_le_pow_right₀ (by linarith) ((le_max_right 1 early).trans hH)
  refine ⟨hpB.trans hBT, hearlyB.trans hBT, ?_⟩
  have hmajor : t + (r : ℝ) ≤ (p + 2) ^ L := by
    simpa [tPoly, b, scalarInput, target, t, Polynomial.eval₂_pow] using hbound p hp0
  have hr : (r : ℝ) ≤ Real.exp (r : ℝ) := by
    linarith [Real.add_one_le_exp (r : ℝ)]
  calc
    _ ≤ Real.exp (r : ℝ) * Real.exp t :=
      mul_le_mul_of_nonneg_right hr (Real.exp_pos _).le
    _ = Real.exp (t + r) := by rw [← Real.exp_add, add_comm]
    _ ≤ _ := Real.exp_le_exp.mpr hmajor

end Erdos3

end

end OAI

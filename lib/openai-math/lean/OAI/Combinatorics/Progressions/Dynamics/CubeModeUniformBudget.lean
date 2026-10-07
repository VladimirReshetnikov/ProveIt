import OAI.Combinatorics.Progressions.Lattices.AnchoredCubeResidueWidths
import OAI.Combinatorics.Progressions.Polynomial.ModeLogPolynomials

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Polynomial

noncomputable def cubeInputLogPolynomial (q : ℕ) : Polynomial ℕ :=
  X + C q.factorial + C (2 + q * (q + 1)) + C (q + 2) * (X + 4)

theorem cubeInputLogPolynomial_ge (q : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ (cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P := by
  have hrest := natPolynomial_eval_nonneg
    (C q.factorial + C (2 + q * (q + 1)) + C (q + 2) * (X + 4)) hP
  simpa [cubeInputLogPolynomial, add_assoc] using le_add_of_nonneg_right hrest (a := P)

theorem cubeModePolynomialBudget_le_exp_input (q : ℕ) {P L : ℝ}
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hLP : L ≤ Real.exp P) :
    cubeModePolynomialBudget q L ≤ Real.exp ((cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P) := by
  have h3 : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have h3L : 3 * L ≤ Real.exp (P + 3) := by
    calc
      _ ≤ Real.exp 3 * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hbase : 1 + 3 * L ≤ Real.exp (P + 4) := by
    convert one_add_le_exp_succ (by positivity) h3L using 1
    congr 1
    ring
  have hf : (q.factorial : ℝ) ≤ Real.exp (q.factorial : ℝ) := by
    linarith [Real.add_one_le_exp (q.factorial : ℝ)]
  have ha : 2 + (q : ℝ) * (q + 1) ≤ Real.exp (2 + (q : ℝ) * (q + 1)) := by
    linarith [Real.add_one_le_exp (2 + (q : ℝ) * (q + 1))]
  unfold cubeModePolynomialBudget
  calc
    _ ≤ Real.exp (q.factorial : ℝ) * Real.exp (2 + (q : ℝ) * (q + 1)) *
        (Real.exp (P + 4)) ^ (q + 2) := by gcongr
    _ = Real.exp ((q.factorial : ℝ) + (2 + (q : ℝ) * (q + 1)) + (q + 2 : ℕ) * (P + 4)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      simp [cubeInputLogPolynomial]
      linarith

theorem exists_cube_mode_threshold_exp_budget (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (n d : ℕ) (P F L S ρ ε : ℝ),
      0 ≤ P → (n : ℝ) ≤ P → (d : ℝ) ≤ P →
      0 ≤ F → F ≤ Real.exp P → 0 ≤ L → L ≤ Real.exp P →
      0 ≤ S → S ≤ Real.exp P → 0 < ρ → 1 / ρ ≤ Real.exp P →
      0 < ε → 1 / ε ≤ Real.exp P →
      modeRemovalSideThreshold m d (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) ∧
      modeRemovalRankThreshold m n d F (cubeModePolynomialBudget q L) S ρ ε ≤ Real.exp ((P + K) ^ K) := by
  obtain ⟨K₀, _, hthreshold⟩ := exists_mode_threshold_exp_budget m
  obtain ⟨K, hK, hpoly⟩ := exists_natPolynomial_eval_budget ((cubeInputLogPolynomial q + C K₀) ^ K₀)
  refine ⟨K, hK, ?_⟩
  intro n d P F L S ρ ε hP hn hd hF hFP hL hLP hS hSP hρ hρP hε hεP
  let P' := (cubeInputLogPolynomial q).eval₂ (Nat.castRingHom ℝ) P
  have hPP : P ≤ P' := cubeInputLogPolynomial_ge q hP
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  obtain ⟨hs, hr⟩ := hthreshold n d P' F (cubeModePolynomialBudget q L) S ρ ε
    (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hF (hFP.trans hEP)
    (cubeModePolynomialBudget_pos q hL).le (cubeModePolynomialBudget_le_exp_input q hP hL hLP)
    hS (hSP.trans hEP) hρ (hρP.trans hEP) hε (hεP.trans hEP)
  have hb : (P' + K₀) ^ K₀ ≤ (P + K) ^ K := by
    simpa [P', Polynomial.eval₂_pow] using hpoly P hP
  exact ⟨hs.trans (Real.exp_le_exp.mpr hb), hr.trans (Real.exp_le_exp.mpr hb)⟩

end Erdos3.BooleanCubeKernel

end

end OAI

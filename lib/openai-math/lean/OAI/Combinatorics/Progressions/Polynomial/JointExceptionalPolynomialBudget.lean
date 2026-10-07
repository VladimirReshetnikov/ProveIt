import OAI.Combinatorics.Progressions.Linear.SpatialMatrixCutoffBudget

namespace OAI

section

namespace Erdos3

theorem exists_spatialMatrixBlock_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P E : ℝ} {n : ℕ}, 0 ≤ P →
      (n : ℝ) ≤ P → 0 ≤ E → E ≤ P →
      smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E + ((n : ℝ)+1)^2+1 ≤
        (P+A)^A ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 E ≤ (P+A)^A := by
  let c : ℕ := ⌈(probabilityProfileLipschitz : ℝ)⌉₊
  have hc : (probabilityProfileLipschitz : ℝ) ≤ (c : ℝ) := Nat.le_ceil _
  let p : Polynomial ℕ :=
    2 * Polynomial.X ^ 3 + 2 +
      2 * Polynomial.X ^ 3 * (11 * Polynomial.X ^ 2 + 11 * Polynomial.X + 5) +
      3 * Polynomial.X ^ 2 + 2 * Polynomial.X + 10 + Polynomial.C c
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget p
  refine ⟨A, hA, ?_⟩
  intro P E n hP hn hE hEP
  have hthreshold : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E ≤
      2*P^3+2+2*P^3*(11*P^2+11*P+5) := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hstep : smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E =
        2*(n : ℝ)^3+2+2*(n : ℝ)^3*(11*(n : ℝ)^2+10*n+E+5) := by
      unfold smoothMatrixBlockThresholdLogBudget smoothMatrixBlockConstantLogBudget
      push_cast
      ring
    rw [hstep]
    calc
      _ ≤ 2*P^3+2+2*P^3*(11*P^2+10*P+P+5) := by gcongr
      _ = _ := by ring
  have hev : Polynomial.eval₂ (Nat.castRingHom ℝ) P p =
      2*P^3+2+2*P^3*(11*P^2+11*P+5)+3*P^2+2*P+10+c := by
    simp [p, Polynomial.eval₂_pow]
  have hbudget := hbound P hP
  rw [hev] at hbudget
  constructor
  · apply le_trans _ hbudget
    have hsq : ((n : ℝ)+1)^2 ≤ (P+1)^2 := by gcongr
    nlinarith [Nat.cast_nonneg (α := ℝ) c, sq_nonneg P]
  · apply le_trans _ hbudget
    have heq : smoothMatrixBlockWidthLogBudget (2*n*n) n 2 E =
        smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 E +
          3*(n : ℝ)^2+2*n+9+probabilityProfileLipschitz := by
      unfold smoothMatrixBlockWidthLogBudget smoothMatrixBlockMeshLogBudget
      push_cast
      ring
    rw [heq]
    have hsq : (n : ℝ)^2 ≤ P^2 := by gcongr
    nlinarith

end Erdos3

end

section

namespace Erdos3

theorem exists_jointExceptional_polynomial_budget :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {P₀ g₀ : ℝ} {n : ℕ}, 0 ≤ P₀ →
      (n : ℝ) ≤ P₀ → 0 ≤ g₀ → g₀ ≤ P₀ →
      smoothMatrixBlockThresholdLogBudget (2*n*n) n 2 (g₀+8) +
          ((n : ℝ)+1)^2+1 ≤ (P₀+A)^A ∧
      smoothMatrixBlockWidthLogBudget (2*n*n) n 2 (g₀+8) ≤ (P₀+A)^A := by
  obtain ⟨a, ha, hbudget⟩ := exists_spatialMatrixBlock_polynomial_budget
  refine ⟨a + 8, by omega, ?_⟩
  intro P₀ g₀ n hP hn hg hgP
  obtain ⟨hthreshold, hwidth⟩ := hbudget (P := P₀ + 8) (E := g₀ + 8)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have hbase : (P₀ + 8 + a : ℝ) = P₀ + (a + 8 : ℕ) := by push_cast; ring
  have hpow : (P₀ + 8 + a : ℝ)^a ≤ (P₀ + (a + 8 : ℕ))^(a + 8) := by
    rw [hbase]
    apply pow_le_pow_right₀
    · push_cast
      linarith
    · omega
  exact ⟨hthreshold.trans hpow, hwidth.trans hpow⟩

end Erdos3

end

end OAI

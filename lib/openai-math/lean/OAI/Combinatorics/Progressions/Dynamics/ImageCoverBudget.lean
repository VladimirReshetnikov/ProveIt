import OAI.Combinatorics.Progressions.Lattices.ImageLatticeSubgroup

namespace OAI

section

namespace Erdos3

def imageLatticeLogBudget (K : ℕ) (p : ℝ) : ℝ :=
  K + (p + 2) ^ 4 + 2 * p + (p + 2) ^ 9

theorem imageLatticeLogBudget_nonneg (K : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ imageLatticeLogBudget K p := by unfold imageLatticeLogBudget; positivity

theorem imageLatticeBound_le_exp (K d n H l m : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) (hm : (m : ℝ) ≤ Real.exp p) :
    ((K * H ^ (n ^ 3) * (m * (l * rationalKernelHeight n H ^ (d * n))) : ℕ) : ℝ) ≤
      Real.exp (imageLatticeLogBudget K p) := by
  have hK : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
  have hpow : ((H ^ (n ^ 3) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 4) := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hH _).trans
    rw [← Real.exp_nat_mul, Nat.cast_pow]
    apply Real.exp_le_exp.mpr
    calc
      (n : ℝ) ^ 3 * p ≤ (p + 2) ^ 3 * (p + 2) := by gcongr <;> linarith
      _ = _ := by ring
  have hkernel := rationalKernelHeight_le_budget n H hp hn hH
  have hpowK : ((rationalKernelHeight n H ^ (d * n) : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hkernel _).trans
    rw [← Real.exp_nat_mul, Nat.cast_mul]
    apply Real.exp_le_exp.mpr
    calc
      (d : ℝ) * n * (p + 2) ^ 7 ≤ (p + 2) * (p + 2) * (p + 2) ^ 7 := by gcongr <;> linarith
      _ = _ := by ring
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
  calc
    _ ≤ Real.exp K * Real.exp ((p + 2) ^ 4) *
        (Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 9))) := by gcongr
    _ = _ := by simp only [← Real.exp_add]; unfold imageLatticeLogBudget; congr 1; ring

theorem exists_image_cover_reconstruction_budget (K C : ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      let q := 2 * p + imageLatticeLogBudget K p
      q ≤ (p + N) ^ N ∧ p * (p + imageLatticeLogBudget K p) ≤ (p + N) ^ N ∧
        (q + C) ^ C ≤ (p + N) ^ N := by
  let L : Polynomial ℕ := Polynomial.C K + (Polynomial.X + 2) ^ 4 +
    2 * Polynomial.X + (Polynomial.X + 2) ^ 9
  let q : Polynomial ℕ := 2 * Polynomial.X + L
  let P : Polynomial ℕ := q + Polynomial.X * (Polynomial.X + L) + (q + Polynomial.C C) ^ C
  obtain ⟨N, hN, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨N, hN, ?_⟩
  intro p hp
  have hlog := imageLatticeLogBudget_nonneg K hp
  have hq : 0 ≤ 2 * p + imageLatticeLogBudget K p := by positivity
  have hidx : 0 ≤ p * (p + imageLatticeLogBudget K p) := by positivity
  have hcost : 0 ≤ (2 * p + imageLatticeLogBudget K p + C) ^ C := by positivity
  have heq : P.eval₂ (Nat.castRingHom ℝ) p = (2 * p + imageLatticeLogBudget K p) +
      p * (p + imageLatticeLogBudget K p) + (2 * p + imageLatticeLogBudget K p + C) ^ C := by
    simp [P, q, L, imageLatticeLogBudget, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hb := hbound p hp
  rw [heq] at hb
  dsimp only
  exact ⟨by linarith, by linarith, by linarith⟩

end Erdos3

end

end OAI

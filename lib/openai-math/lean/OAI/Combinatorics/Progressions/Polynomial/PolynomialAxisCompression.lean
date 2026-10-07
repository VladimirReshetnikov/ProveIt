import OAI.Combinatorics.Progressions.Estimates.AxisCompression

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_polynomial_axis_compression (s : ℕ) (hs : 1 ≤ s)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N n : ℕ} [NeZero N] {p L g : ℝ},
      2 ≤ p → 2 ≤ L → (n : ℝ) ≤ p → 1 ≤ g → g ≤ Real.exp p →
      Odd N → Real.exp ((p + L + 2) ^ C) ≤ N →
      ∀ f : Fin n → ZMod N → ℝ, (∀ i x, 0 ≤ f i x ∧ f i x ≤ Real.exp p) →
      (∀ i, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
        (Real.exp (-((p + L + 2) ^ C))) (f i) (fun _ => g)) →
      ∃ S : Finset (Fin n → ZMod N),
        (S.card : ℝ) ≤ Real.exp (-L) * (N : ℝ) ^ n ∧
        (∀ t y, 0 ≤ normalizedAxisProduct f t ((1 + epsilon) * g) y ∧
          normalizedAxisProduct f t ((1 + epsilon) * g) y ≤ Real.exp (p ^ 2)) ∧
        ∀ t, t ∉ S → CyclicNiltestUpperComparison.{0} (s - 1) N L (Real.exp (-L))
          (normalizedAxisProduct f t ((1 + epsilon) * g)) (fun _ => 1) := by
  obtain ⟨c, _, hcompress⟩ := exists_axis_compression s hs hepsilon hepsilon1
  let Y : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget (((Y + 2) ^ 2 + 2) ^ c)
  refine ⟨C, hC, ?_⟩
  intro N n _ p L g hp hL hn hg hgb hodd hN f hf hcompare
  let r := (p + L + 2) ^ 2
  have hp0 : 0 ≤ p := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hsum : p + L ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + L)]
  have hpr : p ≤ r := by linarith
  have hLr : L ≤ r := by linarith
  have hp2 : p ^ 2 ≤ r := pow_le_pow_left₀ hp0 (by linarith : p ≤ p + L + 2) 2
  have hnp : (n : ℝ) * p ≤ p ^ 2 := by
    simpa only [pow_two] using mul_le_mul_of_nonneg_right hn hp0
  have hcost : (r + 2) ^ c ≤ (p + L + 2) ^ C := by
    simpa [Y, r, Polynomial.eval₂_pow] using hbudget (p + L) (by linarith)
  obtain ⟨S, hS, hcap, hgood⟩ := hcompress hp0 (hp.trans hpr) hpr (hnp.trans hp2) hg
    (hgb.trans (Real.exp_le_exp.mpr hpr)) hodd ((Real.exp_le_exp.mpr hcost).trans hN) f hf
    (fun i => CyclicNiltestUpperComparison.mono_budget (hcompare i) hcost
      (Real.exp_le_exp.mpr (neg_le_neg hcost)))
  have hnexp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have herr : (n : ℝ) * Real.exp (-r) ≤ Real.exp (-L) := by
    calc
      _ ≤ Real.exp p * Real.exp (-r) := mul_le_mul_of_nonneg_right hnexp (Real.exp_nonneg _)
      _ = Real.exp (p - r) := by rw [← Real.exp_add, sub_eq_add_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  refine ⟨S, hS.trans (mul_le_mul_of_nonneg_right herr (pow_nonneg (Nat.cast_nonneg N) n)), ?_, ?_⟩
  · intro t y
    exact ⟨(hcap t y).1, (hcap t y).2.trans (Real.exp_le_exp.mpr hnp)⟩
  · intro t ht
    exact CyclicNiltestUpperComparison.mono_budget (hgood t ht) hLr herr

end Erdos3

end

end OAI

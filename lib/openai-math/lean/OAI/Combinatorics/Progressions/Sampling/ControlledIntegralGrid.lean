import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

open Module

theorem exists_controlled_integral_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L ι : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
      (e : Basis ι ℚ L) (_hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
      (l : ℕ), 0 < l → ∀ (p : ℝ), 0 ≤ p → (Fintype.card ι : ℝ) ≤ p →
      (l : ℝ) ≤ Real.exp p →
      (∀ i j k, rationalLogHeight (lieStructureConstants e i j k) ≤ p) →
      p ≤ (p + C) ^ C ∧ ∃ B : ℕ, 0 < B ∧ l ∣ B ∧ (B : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ x ∈ coordinateGridModule e B, ∀ y ∈ coordinateGridModule e B,
          lieBCH s x y ∈ coordinateGridModule e B := by
  let K := bchIntegralDenominatorBound s
  let Q : Polynomial ℕ := Polynomial.C K + (Polynomial.X + 1) * Polynomial.X ^ 3 + Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + Polynomial.X)
  refine ⟨C, hC, ?_⟩
  intro L ι _ _ _ e hnil l hl p hp hd hlp hc
  let H := ⌈Real.exp p⌉₊
  let E := (K : ℝ) + (p + 1) * p ^ 3 + p
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have htotal : E + p ≤ (p + C) ^ C := by
    simpa [Q, E, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := (le_add_of_nonneg_left hE).trans htotal
  have hEC : E ≤ (p + C) ^ C := (le_add_of_nonneg_right hp).trans htotal
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hn3 : ((Fintype.card ι ^ 3 : ℕ) : ℝ) ≤ p ^ 3 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hd _
  have hHpow : (H : ℝ) ^ (Fintype.card ι ^ 3) ≤ Real.exp ((p + 1) * p ^ 3) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg H) hH _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right hn3 (by linarith)).trans_eq (mul_comm _ _)
  have hK : (K : ℝ) ≤ Real.exp (K : ℝ) :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  obtain ⟨B, hB, hdiv, hbound, hstable⟩ := exists_bch_stable_integral_grid e hnil l hl
    (fun i j k => rationalHeightLE_ceil_exp (hc i j k))
  have hBexp : (B : ℝ) ≤ Real.exp E := by
    calc
      _ ≤ (K : ℝ) * (H : ℝ) ^ (Fintype.card ι ^ 3) * (l : ℝ) := by exact_mod_cast hbound
      _ ≤ Real.exp (K : ℝ) * Real.exp ((p + 1) * p ^ 3) * Real.exp p :=
        mul_le_mul (mul_le_mul hK hHpow (by positivity) (Real.exp_nonneg _)) hlp
          (Nat.cast_nonneg l) (by positivity)
      _ = Real.exp E := by rw [← Real.exp_add, ← Real.exp_add]
  exact ⟨hpC, B, hB, hdiv, hBexp.trans (Real.exp_le_exp.mpr hEC), hstable⟩

end Erdos3

end

end OAI

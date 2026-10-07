import OAI.Combinatorics.Progressions.Geometry.SampledCommonBox

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem natPolynomial_eval_mono_nonneg (P : Polynomial ℕ) {p q : ℝ}
    (hp : 0 ≤ p) (hpq : p ≤ q) :
    P.eval₂ (Nat.castRingHom ℝ) p ≤ P.eval₂ (Nat.castRingHom ℝ) q := by
  simp only [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ hp hpq n) (Nat.cast_nonneg _))

def sampledFullboxDetectionLog (s C n : ℕ) (p q : ℝ) : ℝ :=
  (5 * p + 20) * n + p + q + 2 + (2 ^ (s + 2) : ℕ) *
    denseBoxGowersTransferCost s n (p + 1) ((q + C) ^ C)

theorem exists_sampledFullboxDetection_budget (s C : ℕ) (P : Polynomial ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ (p q : ℝ) (n : ℕ), 0 ≤ p → 0 ≤ q →
      (n : ℝ) ≤ P.eval₂ (Nat.castRingHom ℝ) q →
      sampledFullboxDetectionLog s C n p q ≤ (p + q + K) ^ K := by
  let X : Polynomial ℕ := Polynomial.X
  let H : Polynomial ℕ := (X + Polynomial.C C) ^ C
  let D : Polynomial ℕ := (H + (2 * X + 8) * P + 1) *
    (Polynomial.C (2 ^ (s + 2)) * P + 1) + (P + 3) * P
  let F : Polynomial ℕ := (5 * X + 20) * P + 2 * X + 2 + Polynomial.C (2 ^ (s + 2)) * D
  obtain ⟨K, hK, hbound⟩ := exists_natPolynomial_eval_budget F
  refine ⟨K, hK, ?_⟩
  intro p q n hp hq hn
  have hpq : 0 ≤ p + q := add_nonneg hp hq
  have hq' : q ≤ p + q := le_add_of_nonneg_left hp
  have hp' : p ≤ p + q := le_add_of_nonneg_right hq
  have hn' := hn.trans (natPolynomial_eval_mono_nonneg P hq hq')
  have hR := natPolynomial_eval_nonneg P hpq
  apply le_trans _ (hbound (p + q) hpq)
  dsimp only [sampledFullboxDetectionLog, denseBoxGowersTransferCost, F, D, H, X]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_C, Polynomial.eval₂_X,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.coe_castRingHom, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_one]
  have hbase : (q + C) ^ C ≤ (p + q + C) ^ C :=
    pow_le_pow_left₀ (by positivity) (by linarith) C
  have ha : (5 * p + 20) * n + p + q + 2 ≤
      (5 * (p + q) + 20) * P.eval₂ (Nat.castRingHom ℝ) (p + q) + 2 * (p + q) + 2 := by
    have hprod : (5 * p + 20) * n ≤
        (5 * (p + q) + 20) * P.eval₂ (Nat.castRingHom ℝ) (p + q) := by gcongr
    linarith
  have hb : ((q + C) ^ C + (2 * (p + 1) + 6) * n + 1) *
      ((2 ^ (s + 2) : ℕ) * n + 1) + ((n + 3) * n : ℕ) ≤
      ((p + q + C) ^ C + (2 * (p + q) + 8) * P.eval₂ (Nat.castRingHom ℝ) (p + q) + 1) *
        ((2 ^ (s + 2) : ℕ) * P.eval₂ (Nat.castRingHom ℝ) (p + q) + 1) +
          (P.eval₂ (Nat.castRingHom ℝ) (p + q) + 3) * P.eval₂ (Nat.castRingHom ℝ) (p + q) := by
    push_cast
    rw [show 2 * (p + 1) + 6 = 2 * p + 8 by ring]
    gcongr
  have hb' := hb
  push_cast at hb'
  exact add_le_add ha (mul_le_mul_of_nonneg_left hb' (by positivity))

theorem sampledFullboxDetection_exp_lower (s C n : ℕ) (p q α : ℝ)
    (hα : Real.exp (-q) ≤ α / 4) :
    Real.exp (-sampledFullboxDetectionLog s C n p q) ≤
      (Real.exp (-((5 * p + 20) * n + p + 2)) * (α / 2)) *
        Real.exp (-denseBoxGowersTransferCost s n (p + 1) ((q + C) ^ C)) ^ (2 ^ (s + 2)) := by
  have hhalf : Real.exp (-q) ≤ α / 2 := by linarith [Real.exp_pos (-q)]
  calc
    _ = (Real.exp (-((5 * p + 20) * n + p + 2)) * Real.exp (-q)) *
        Real.exp (-denseBoxGowersTransferCost s n (p + 1) ((q + C) ^ C)) ^ (2 ^ (s + 2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold sampledFullboxDetectionLog
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg _)) (by positivity)

end Erdos3

end

end OAI

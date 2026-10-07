import OAI.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

theorem candidateFrontFactor_block_le_power (s m Ctotal : ℕ)
    {p markInput ci : ℝ} (hp : 0 ≤ p) (hmark : markInput ≤ ci)
    (hci : ci ≤ (p + 2) ^ Ctotal) :
    (s : ℝ) * (markInput * m) ≤ (p + 2) ^ (Ctotal + s * m) := by
  have hbase : 0 ≤ p + 2 := by linarith only [hp]
  have htwo : ((s * m : ℕ) : ℝ) ≤ (2 : ℝ) ^ (s * m) := by
    exact_mod_cast (show s * m < 2 ^ (s * m) from Nat.lt_two_pow_self).le
  have hcoefficient : ((s * m : ℕ) : ℝ) ≤ (p + 2) ^ (s * m) :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith only [hp]) (s * m))
  calc
    _ = ((s * m : ℕ) : ℝ) * markInput := by simp only [Nat.cast_mul]; ring
    _ ≤ ((s * m : ℕ) : ℝ) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_left (hmark.trans hci) (Nat.cast_nonneg _)
    _ ≤ (p + 2) ^ (s * m) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hbase _)
    _ = (p + 2) ^ (Ctotal + s * m) := by rw [← pow_add, Nat.add_comm]

theorem exists_candidateFrontFactor_block_power_budget (s m Ctotal : ℕ) :
    ∃ Cblock : ℕ, Ctotal ≤ Cblock ∧
      ∀ p : ℝ, 0 ≤ p → ∀ markInput ci : ℝ,
        markInput ≤ ci → ci ≤ (p + 2) ^ Ctotal →
        (s : ℝ) * (markInput * m) ≤ (p + 2) ^ Cblock := by
  refine ⟨Ctotal + s * m, Nat.le_add_right _ _, ?_⟩
  intro p hp markInput ci hmark hci
  exact candidateFrontFactor_block_le_power s m Ctotal hp hmark hci

theorem candidateFrontFactor_uniform_block_le_power (s Ctotal : ℕ)
    {m : ℕ} {p markInput ci : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p)
    (hmark : markInput ≤ ci) (hci : ci ≤ (p + 2) ^ Ctotal) :
    (s : ℝ) * (markInput * m) ≤ (p + 2) ^ (Ctotal + s + 1) := by
  have hbase : 0 ≤ p + 2 := by linarith only [hp]
  have htwo : (s : ℝ) ≤ (2 : ℝ) ^ s := by
    exact_mod_cast (show s < 2 ^ s from Nat.lt_two_pow_self).le
  have hs : (s : ℝ) ≤ (p + 2) ^ s :=
    htwo.trans (pow_le_pow_left₀ (by norm_num) (by linarith only [hp]) s)
  have hcoefficient : (s : ℝ) * m ≤ (p + 2) ^ s * (p + 2) :=
    mul_le_mul hs (by linarith only [hm]) (Nat.cast_nonneg _) (pow_nonneg hbase _)
  calc
    _ = ((s : ℝ) * m) * markInput := by ring
    _ ≤ ((s : ℝ) * m) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_left (hmark.trans hci) (by positivity)
    _ ≤ ((p + 2) ^ s * (p + 2)) * (p + 2) ^ Ctotal :=
      mul_le_mul_of_nonneg_right hcoefficient (pow_nonneg hbase _)
    _ = (p + 2) ^ (Ctotal + s + 1) := by
      rw [← pow_succ, ← pow_add]
      congr 1
      omega

theorem candidateFrontFactor_massLog_le
    {v V n p qCommon common mass0 : ℝ}
    (hv0 : 0 ≤ v) (hv : v ≤ V) (hn0 : 0 ≤ n) (hn : n ≤ p)
    (hq0 : 0 ≤ qCommon) (hq : qCommon ≤ common) (hmass : mass0 ≤ p) :
    v * n + ((qCommon + 2) ^ 5 + qCommon) + mass0 ≤
      p + V * p + ((common + 2) ^ 5 + common) := by
  have hproduct : v * n ≤ V * p := mul_le_mul hv hn hn0 (hv0.trans hv)
  have hpower : (qCommon + 2) ^ 5 ≤ (common + 2) ^ 5 :=
    pow_le_pow_left₀ (by linarith only [hq0]) (by linarith only [hq]) 5
  linarith only [hproduct, hpower, hq, hmass]

end Erdos3.VectorPolynomial

end

end OAI

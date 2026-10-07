import OAI.Combinatorics.Progressions.Polynomial.PreparedPolynomialLayer

namespace OAI

section

namespace Erdos3

theorem preparationModulusCap_le_exp {s M R : ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hM : (M : ℝ) ≤ p) (hR : (R : ℝ) ≤ Real.exp p) :
    (preparationModulusCap s M R p : ℝ) ≤
      Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 2)) := by
  let e := budgetDepthExponent 38 s
  let X := (p + 2) ^ e
  have hX : 1 ≤ X := one_le_pow₀ (by linarith)
  have hheight := preparationHeight_le_exp p s
  have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (preparationHeight p s)) hheight M
  rw [← Real.exp_nat_mul] at hpow
  have hb : (M : ℝ) * X + p ≤ (p + 2) ^ (e + 2) := by
    calc
      (M : ℝ) * X + p ≤ p * X + p * X := by gcongr; nlinarith
      _ = (2 * p) * X := by ring
      _ ≤ (p + 2) ^ 2 * X := by gcongr; nlinarith
      _ = (p + 2) ^ (e + 2) := by dsimp [X]; rw [pow_add]; ring
  unfold preparationModulusCap
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp (M * X) := mul_le_mul hR hpow (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (M * X + p) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr hb

theorem preparationShrink_le_exp {s n M R : ℕ} {p δ : ℝ}
    (hp : 0 ≤ p) (hs : (s : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hM : (M : ℝ) ≤ p)
    (hR : (R : ℝ) ≤ Real.exp p) (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    preparationShrink s n M R p δ ≤ Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 6)) := by
  let e := budgetDepthExponent 38 s
  let U := (p + 2) ^ (e + 2)
  have hbase : 1 ≤ p + 2 := by linarith
  have hU : 1 ≤ U := one_le_pow₀ hbase
  have hpU : p ≤ U := le_power_budget hp (by omega)
  have hnp : (n : ℝ) + 1 ≤ Real.exp p := (by linarith : (n : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hsp : (s : ℝ) + 1 ≤ Real.exp p := (by linarith : (s : ℝ) + 1 ≤ p + 1).trans (Real.add_one_le_exp p)
  have hep : Real.exp p ≤ Real.exp U := Real.exp_le_exp.mpr hpU
  have hnU : (n : ℝ) ≤ Real.exp U := (by linarith : (n : ℝ) ≤ (n : ℝ) + 1).trans (hnp.trans hep)
  have hsU : (s : ℝ) ≤ Real.exp U := (by linarith : (s : ℝ) ≤ (s : ℝ) + 1).trans (hsp.trans hep)
  have hp2 : p ^ 2 ≤ U :=
    (pow_le_pow_left₀ hp (by linarith : p ≤ p + 2) 2).trans (pow_le_pow_right₀ hbase (by omega))
  have hnPower : ((n : ℝ) + 1) ^ s ≤ Real.exp U := by
    apply (pow_le_pow_left₀ (by positivity) hnp s).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_right hs hp).trans (by nlinarith [hp2]))
  have hheight : (preparationHeight p s : ℝ) ≤ Real.exp U :=
    (preparationHeight_le_exp p s).trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase (by omega)))
  have hK : (preparationOscillationCap s n R p : ℝ) ≤ Real.exp (6 * U) := by
    have hb : (preparationOscillationCap s n R p : ℝ) ≤
        Real.exp U * Real.exp U * Real.exp U * Real.exp U * Real.exp U * Real.exp U := by
      unfold preparationOscillationCap
      push_cast
      gcongr
      · exact hsp.trans hep
      · exact hR.trans hep
    apply hb.trans_eq
    repeat rw [← Real.exp_add]
    congr 1
    ring
  have htwo : (2 : ℝ) ≤ Real.exp U := by linarith [Real.add_one_le_exp U]
  have hK1 : (preparationOscillationCap s n R p : ℝ) + 1 ≤ Real.exp (7 * U) := by
    have he1 : 1 ≤ Real.exp (6 * U) := Real.one_le_exp (by positivity)
    calc
      _ ≤ 2 * Real.exp (6 * U) := by linarith
      _ ≤ Real.exp U * Real.exp (6 * U) := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hδlower : Real.exp (-U) ≤ δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ (Real.exp_pos U) hδ).mpr (hδinv.trans hep)
  let ρ := min 1 (δ / (preparationOscillationCap s n R p + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρlower : Real.exp (-8 * U) ≤ ρ := by
    apply le_min
    · exact Real.exp_le_one_iff.mpr (by linarith)
    · apply (le_div_iff₀ (by positivity : 0 < (preparationOscillationCap s n R p : ℝ) + 1)).mpr
      calc
        _ ≤ Real.exp (-8 * U) * Real.exp (7 * U) := mul_le_mul_of_nonneg_left hK1 (Real.exp_nonneg _)
        _ = Real.exp (-U) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ δ := hδlower
  have hfour : (4 : ℝ) ≤ Real.exp (2 * U) := by
    calc
      (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ Real.exp U * Real.exp U := mul_le_mul htwo htwo (by norm_num) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hC : preparationShrink s n M R p δ ≤ Real.exp (11 * U) := by
    apply (div_le_iff₀ hρ).mpr
    calc
      _ ≤ Real.exp (2 * U) * Real.exp U :=
        mul_le_mul hfour (preparationModulusCap_le_exp hp hM hR) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (11 * U) * Real.exp (-8 * U) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (11 * U) * ρ := mul_le_mul_of_nonneg_left hρlower (Real.exp_nonneg _)
  apply hC.trans (Real.exp_le_exp.mpr ?_)
  have hb4 : (11 : ℝ) ≤ (p + 2) ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 2 ≤ p + 2) 4
    norm_num at h
    linarith
  calc
    11 * U ≤ (p + 2) ^ 4 * U := mul_le_mul_of_nonneg_right hb4 (by positivity)
    _ = (p + 2) ^ (e + 6) := by dsimp [U]; rw [← pow_add]; congr 1; omega

theorem preparation_total_cost_le_exp {s n M R T : ℕ} {p δ : ℝ}
    (hp : 0 ≤ p) (hs : (s : ℝ) ≤ p) (hn : (n : ℝ) ≤ p) (hM : (M : ℝ) ≤ p)
    (hT : (T : ℝ) + 1 ≤ p) (hR : (R : ℝ) ≤ Real.exp p)
    (hδ : 0 < δ) (hδinv : δ⁻¹ ≤ Real.exp p) :
    ((preparationModulusCap s M R p ^ T : ℕ) : ℝ) ≤
        Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 7)) ∧
      preparationShrink s n M R p δ ^ (T + 1) ≤
        Real.exp ((p + 2) ^ (budgetDepthExponent 38 s + 7)) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hQ := preparationModulusCap_le_exp (s := s) hp hM hR
  have hC := preparationShrink_le_exp hp hs hn hM hR hδ hδinv
  constructor
  · push_cast
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hQ T).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      (T : ℝ) * (p + 2) ^ (budgetDepthExponent 38 s + 2) ≤
          (p + 2) * (p + 2) ^ (budgetDepthExponent 38 s + 2) := by gcongr; linarith
      _ = (p + 2) ^ (budgetDepthExponent 38 s + 3) := by rw [pow_succ]; ring
      _ ≤ _ := pow_le_pow_right₀ hbase (by omega)
  · have hC0 : 0 ≤ preparationShrink s n M R p δ := by
      unfold preparationShrink
      positivity
    apply (pow_le_pow_left₀ hC0 hC (T + 1)).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    calc
      ((T + 1 : ℕ) : ℝ) * (p + 2) ^ (budgetDepthExponent 38 s + 6) ≤
          (p + 2) * (p + 2) ^ (budgetDepthExponent 38 s + 6) := by
            gcongr
            push_cast
            linarith
      _ = _ := by rw [pow_succ]; ring

end Erdos3

end

end OAI

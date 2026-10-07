import OAI.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget

namespace OAI

section

namespace Erdos3

def uniformProductAccuracyLog {A : Type*} [Semiring A] (D T E : A) : A :=
  D + D * (T + 4) + E

theorem uniformProductAccuracyLog_nonneg {D T E : ℝ}
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E) :
    0 ≤ uniformProductAccuracyLog D T E := by unfold uniformProductAccuracyLog; positivity

theorem uniformProductAccuracy_inverse_exp_bound (N : ℕ) {C δ D T E : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hCT : C ≤ Real.exp T) (hδE : δ⁻¹ ≤ Real.exp E) :
    (uniformProductAccuracy N C δ)⁻¹ ≤ Real.exp (uniformProductAccuracyLog D T E) := by
  have hNexp : (N : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hCexp : C + 2 ≤ Real.exp (T + 4) :=
    (by linarith : C + 2 ≤ 2 * C + 3).trans (two_mul_add_three_exp_bound hT hCT)
  have hpow := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ C + 2)
    hCexp (by positivity) N hN
  have hden : ((N : ℝ) + 1) * (C + 2) ^ N ≤ Real.exp (D + D * (T + 4)) :=
    (mul_le_mul hNexp hpow (by positivity) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  unfold uniformProductAccuracy
  apply inv_min_le_of_inv_le
  · rw [inv_one]
    exact Real.one_le_exp_iff.mpr (uniformProductAccuracyLog_nonneg hD hT hE)
  · rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul hden hδE (inv_nonneg.mpr hδ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm

theorem uniformProductHalfAccuracy_inverse_exp_bound (N : ℕ) {C cap δ D T E : ℝ}
    (hC : 0 ≤ C) (hcap : 0 ≤ cap) (hcapC : cap ≤ C) (hδ : 0 < δ)
    (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hCT : C ≤ Real.exp T) (hδE : δ⁻¹ ≤ Real.exp E) :
    ((uniformProductAccuracy N C δ / 2) / (cap + 1))⁻¹ ≤
      Real.exp (uniformProductAccuracyLog D T E + T + 2) := by
  have hu := uniformProductAccuracy_inverse_exp_bound N hC hδ hD hT hE hN hCT hδE
  have hcapexp : cap + 1 ≤ Real.exp (T + 1) := by
    calc
      _ ≤ 1 + C := by linarith
      _ ≤ _ := one_add_le_exp_succ hT hCT
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  calc
    _ = (uniformProductAccuracy N C δ)⁻¹ * (2 * (cap + 1)) := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      ring
    _ ≤ Real.exp (uniformProductAccuracyLog D T E) * (Real.exp 1 * Real.exp (T + 1)) :=
      mul_le_mul hu (mul_le_mul htwo hcapexp (by positivity) (Real.exp_pos _).le)
        (by positivity) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth

namespace OAI

section

namespace Erdos3

theorem amplificationResource_log_at_selected_level {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) :
    Real.log (amplificationResource p D K ⌊levelCoefficient K * Real.log p⌋₊) ≤
      ((D : ℝ) + 2) * p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  have hp1 : 1 ≤ p := by linarith
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (show 1 < K by omega)
  have hlog : 0 ≤ Real.log (2 + p) := Real.log_nonneg (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2p : Real.log 2 ≤ Real.log (2 + p) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hinner : (D : ℝ) * Real.log (2 + p) + 2 * Real.log 2 ≤
      ((D : ℝ) + 2) * Real.log (2 + p) := by nlinarith
  calc
    _ ≤ (K : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ *
        (D * Real.log (2 + p) + 2 * Real.log 2) :=
      log_amplificationResource_le hp hD hK _
    _ ≤ p ^ (1 / 4 : ℝ) * (D * Real.log (2 + p) + 2 * Real.log 2) :=
      mul_le_mul_of_nonneg_right (resource_base_at_selected_level hK1 hp1) (by positivity)
    _ ≤ p ^ (1 / 4 : ℝ) * (((D : ℝ) + 2) * Real.log (2 + p)) :=
      mul_le_mul_of_nonneg_left hinner (Real.rpow_nonneg (by linarith) _)
    _ = _ := by ring

theorem amplificationResource_log_add_two_at_selected_level {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) :
    Real.log (2 + amplificationResource p D K ⌊levelCoefficient K * Real.log p⌋₊) ≤
      ((D : ℝ) + 3) * p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  let j := ⌊levelCoefficient (K : ℝ) * Real.log p⌋₊
  have hr := amplificationResource_ge_two hp hD (by omega : 1 ≤ K) j
  have hlog : 0 ≤ Real.log (2 + p) := Real.log_nonneg (by linarith)
  have hq : 1 ≤ p ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hc : Real.log 2 ≤ p ^ (1 / 4 : ℝ) * Real.log (2 + p) :=
    (Real.log_le_log (by norm_num) (by linarith : 2 ≤ 2 + p)).trans
      (le_mul_of_one_le_left hlog hq)
  have hlift : Real.log (2 + amplificationResource p D K j) ≤
      Real.log (amplificationResource p D K j) + Real.log 2 := by
    calc
      _ ≤ Real.log (amplificationResource p D K j * 2) :=
        Real.log_le_log (by linarith) (by linarith)
      _ = _ := Real.log_mul (by linarith) (by norm_num)
  calc
    _ ≤ Real.log (amplificationResource p D K j) + Real.log 2 := hlift
    _ ≤ ((D : ℝ) + 2) * p ^ (1 / 4 : ℝ) * Real.log (2 + p) +
        p ^ (1 / 4 : ℝ) * Real.log (2 + p) :=
      add_le_add (amplificationResource_log_at_selected_level hp hD hK) hc
    _ = _ := by ring

noncomputable def amplificationSourceLogCoefficient (D E : ℕ) : ℝ :=
  (E : ℝ) * ((D : ℝ) + 3)

theorem amplificationSourceLogCoefficient_pos (D : ℕ) {E : ℕ} (hE : 1 ≤ E) :
    0 < amplificationSourceLogCoefficient D E := by
  unfold amplificationSourceLogCoefficient
  have hE0 : (0 : ℝ) < E := by exact_mod_cast (show 0 < E by omega)
  positivity

theorem amplificationSource_final_cost_log_bound {p : ℝ} {D K : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) (E : ℕ) :
    Real.log ((2 + amplificationResource p D K ⌊levelCoefficient K * Real.log p⌋₊) ^ E) ≤
      amplificationSourceLogCoefficient D E * p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  rw [Real.log_pow]
  calc
    _ ≤ (E : ℝ) * (((D : ℝ) + 3) * p ^ (1 / 4 : ℝ) * Real.log (2 + p)) :=
      mul_le_mul_of_nonneg_left (amplificationResource_log_add_two_at_selected_level hp hD hK)
        (Nat.cast_nonneg E)
    _ = _ := by unfold amplificationSourceLogCoefficient; ring

theorem amplificationSource_final_cost_spec {p : ℝ} {D K E : ℕ}
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hK : 2 ≤ K) (hE : 1 ≤ E) :
    let j := ⌊levelCoefficient (K : ℝ) * Real.log p⌋₊
    let Pj := amplificationResource p D K j
    let U := (2 + Pj) ^ E
    1 ≤ U ∧ Pj ≤ U ∧ 0 < U ∧
      Real.log U ≤ amplificationSourceLogCoefficient D E *
        p ^ (1 / 4 : ℝ) * Real.log (2 + p) := by
  dsimp only
  refine ⟨amplificationFinalCost_one_le hp hD (by omega) E _,
    amplificationFinalCost_resource_le hp hD (by omega) hE _,
    amplificationFinalCost_pos hp hD (by omega) E _,
    amplificationSource_final_cost_log_bound hp hD hK E⟩

end Erdos3

end

end OAI

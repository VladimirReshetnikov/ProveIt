import OAI.Combinatorics.Progressions.Dynamics.PivotNativeIteration

namespace OAI

section

namespace Erdos3

open Filter Topology

theorem exists_counting_kernel_parameters (s : ℕ) {tau : ℝ} (htau : 0 < tau) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ p : ℝ, 2 ≤ p → ∃ n : ℕ, ((2 ^ (n + 1) : ℕ) : ℝ) ≤ C0 * p ∧
        ∀ r : ℕ, r ≤ s →
          pivotIterationBound (2 ^ (n + 1)) r 1 p (1 + delta) < 1 + tau := by
  have hcontinuous : ContinuousAt
      (fun x : ℝ => Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2)) 0 := by fun_prop
  have htend : Tendsto (fun x : ℝ => Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2))
      (𝓝 0) (𝓝 1) := by simpa using hcontinuous.tendsto
  have heventually : ∀ᶠ x : ℝ in 𝓝 0,
      Real.exp ((s : ℝ) * x) * (1 + x) ^ (s + 2) < 1 + tau :=
    htend.eventually_lt_const (by linarith)
  obtain ⟨a, ha, hball⟩ := Metric.eventually_nhds_iff_ball.mp heventually
  let delta := min a 1 / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta1 : delta < 1 := by
    dsimp [delta]
    have h := min_le_right a (1 : ℝ)
    linarith
  have hdeltaa : delta < a := by
    dsimp [delta]
    have h := min_le_left a (1 : ℝ)
    linarith
  have hsmall : Real.exp ((s : ℝ) * delta) * (1 + delta) ^ (s + 2) < 1 + tau :=
    hball delta (by simpa [Real.dist_eq, abs_of_pos hdelta] using hdeltaa)
  refine ⟨delta, hdelta, 2 / delta, ?_, ?_⟩
  · apply (le_div_iff₀ hdelta).2
    linarith
  · intro p hp
    have hp0 : 0 < p := by linarith
    have hnear : 1 ≤ p / delta := by
      apply (le_div_iff₀ hdelta).2
      linarith
    obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near hnear (show (1 : ℝ) < 2 by norm_num)
    have hq0 : 0 < ((2 ^ (n + 1) : ℕ) : ℝ) := by positivity
    have hqcap : ((2 ^ (n + 1) : ℕ) : ℝ) ≤ (2 / delta) * p := by
      rw [Nat.cast_pow, Nat.cast_ofNat, pow_succ]
      calc
        (2 : ℝ) ^ n * 2 ≤ (p / delta) * 2 := mul_le_mul_of_nonneg_right hlo (by norm_num)
        _ = _ := by ring
    have hpq : p / ((2 ^ (n + 1) : ℕ) : ℝ) ≤ delta := by
      apply (div_le_iff₀ hq0).2
      have hhi' : p / delta < ((2 ^ (n + 1) : ℕ) : ℝ) := by
        simpa only [Nat.cast_pow, Nat.cast_ofNat] using hhi
      have h := (div_lt_iff₀ hdelta).mp hhi'
      nlinarith
    refine ⟨n, hqcap, ?_⟩
    intro r hrs
    have hexp : (r : ℝ) * p / ((2 ^ (n + 1) : ℕ) : ℝ) ≤ s * delta := by
      rw [mul_div_assoc]
      exact mul_le_mul (by exact_mod_cast hrs) hpq (le_of_lt (div_pos hp0 hq0))
        (Nat.cast_nonneg s)
    have hpow : (1 + delta) ^ (r + 2) ≤ (1 + delta) ^ (s + 2) :=
      pow_le_pow_right₀ (by linarith) (by omega)
    unfold pivotIterationBound
    simp only [Nat.cast_one, mul_one]
    exact (mul_le_mul (Real.exp_le_exp.mpr hexp) hpow
      (pow_nonneg (by linarith) _) (Real.exp_nonneg _)).trans_lt hsmall

end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.RelativeAmplificationDiscount
import OAI.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem LowDensityRelativeAbsoluteRule.iterate
    {s n₀ E D₀ D : ℕ} [NeZero n₀] {τ p H₀ : ℝ}
    (hrelative : RelativePatchPowerInductionRule s n₀ s τ E)
    (hp : 2 ≤ p) (hD : 1 ≤ D) (hn : (n₀ : ℝ) ≤ (2 + p) ^ D)
    (hκ : 0 < (1 - τ) ^ (s + 1)) (hκ1 : (1 - τ) ^ (s + 1) < 1)
    (hH : 1 < H₀) (hκH : 1 ≤ ((1 - τ) ^ (s + 1)) ^ 2 * H₀)
    (hbase : LowDensityRelativeAbsoluteRule s n₀ p H₀ D₀ ((2 + p) ^ D)) :
    ∀ j : ℕ, LowDensityRelativeAbsoluteRule s n₀ p
      (amplificationGain ((1 - τ) ^ (s + 1)) H₀ j)
      ((s + 1) ^ j * D₀) (amplificationResource p D (E + 1) j) := by
  intro j
  induction j with
  | zero => simpa only [amplificationGain, amplificationResource, pow_zero, one_mul] using hbase
  | succ j ih =>
    obtain ⟨hgain, hdiscount⟩ := amplificationGain_low_density_parameters hκ hκ1 hH hκH j
    have hparam := amplificationResource_parameter_le hp hD (by omega : 1 ≤ E + 1) j
    have hdim := hn.trans (amplificationResource_zero_le hp hD (by omega : 1 ≤ E + 1) j)
    have hstep := LowDensityRelativeAbsoluteRule.amplify_power hrelative ih
      (amplificationResource_ge_two hp hD (by omega) j) hdim hparam hgain hdiscount
    simpa only [amplificationGain, amplificationResource, pow_succ, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hstep

theorem exists_recursive_low_density_absolute_rules (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k)
    (hlifting : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 →
      ∃ E : ℕ, 2 ≤ E ∧ RelativePatchPowerInductionRule (k - 2) n₀ (k - 2) τ E) :
    ∃ (C E : ℕ) (τ H₀ : ℝ), 2 ≤ C ∧ 2 ≤ E ∧ 0 < τ ∧ τ ≤ 1 / 2 ∧ 1 < H₀ ∧
      let κ := (1 - τ) ^ (k - 2 + 1)
      0 < κ ∧ κ < 1 ∧ 1 < κ * H₀ ∧ 1 ≤ κ ^ 2 * H₀ ∧
      ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
        LowDensityRelativeAbsoluteRule (k - 2) n₀ p (amplificationGain κ H₀ j)
          (((k - 2) + 1) ^ j * ⌊(p + 2) ^ C⌋₊)
          (amplificationResource p (C + 1) (E + 1) j) := by
  obtain ⟨C, hC, xi, hxi, hinitial⟩ := exists_initial_relative_absolute_rule n₀ k hk
  have hH : 1 < 1 + xi := by linarith
  obtain ⟨τ, hτ, hτhalf, hκ, hκ1, hκgain, hκH⟩ :=
    exists_relative_amplification_discount (k - 2) hH
  obtain ⟨E, hE, hrelative⟩ := hlifting τ hτ hτhalf
  refine ⟨C, E, τ, 1 + xi, hC, hE, hτ, hτhalf, hH, hκ, hκ1, hκgain, hκH, ?_⟩
  intro p hp hn j
  apply LowDensityRelativeAbsoluteRule.iterate hrelative hp (by omega)
    (hn.trans (amplificationResource_parameter_le_zero (K := E + 1) hp (by omega)))
    hκ hκ1 hH hκH _ j
  intro a ha _hlow
  simpa only [add_comm (2 : ℝ) p] using hinitial hp ha

theorem lowDensityRelativeAbsoluteRule_eventually_selected
    {s n₀ : ℕ} {κ H₀ K : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 1 ≤ H₀) (hK : 2 ≤ K)
    (rank : ℝ → ℕ → ℕ) (resource : ℝ → ℕ → ℝ)
    (hfamily : ∀ p : ℝ, 2 ≤ p → (n₀ : ℝ) ≤ p → ∀ j : ℕ,
      LowDensityRelativeAbsoluteRule s n₀ p (amplificationGain κ H₀ j)
        (rank p j) (resource p j)) :
    ∀ᶠ p : ℝ in Filter.atTop,
      let j := ⌊levelCoefficient K * Real.log p⌋₊
      RelativePatchAbsoluteRule s n₀ (resource p j) (Real.exp (-p))
        (amplificationGain κ H₀ j * Real.exp (-p)) (rank p j) := by
  filter_upwards [eventually_low_density_at_selected_level hκ hκ1 hH hK,
    Filter.eventually_ge_atTop (2 : ℝ), Filter.eventually_ge_atTop (n₀ : ℝ)]
    with p hlow hp hn
  exact hfamily p hp hn _ _ le_rfl hlow

end Erdos3

end

end OAI

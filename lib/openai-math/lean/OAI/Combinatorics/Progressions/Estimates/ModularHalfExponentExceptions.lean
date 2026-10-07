import OAI.Combinatorics.Progressions.Linear.PreparedSpatialKernelBlocks

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem modularRank_half_exceptional_probability
    {Ω Row : Type*} [Fintype Ω] [Fintype Row]
    (w : FiniteProbabilityWeights Ω) (ρ : Row → Ω → ℝ)
    (hρ : ∀ r x, 0 ≤ ρ r x) {J : ℕ} {q C D : ℝ}
    (hq : 1 ≤ q) (hJ : 2 * (C + D + 10) ≤ (J : ℝ))
    (hrows : (Fintype.card Row : ℝ) ≤ q ^ D)
    (hmean : ∀ r, w.mean (ρ r) ≤ (q ^ (-(1 : ℝ) / 2)) ^ J) :
    w.eventProbability (fun x => ∃ r, q ^ (-C) < ρ r x) ≤ q ^ (-(10 : ℝ)) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hunion := w.eventProbability_union_bound
    (fun x => ∃ r, q ^ (-C) < ρ r x) (fun r x => q ^ (-C) < ρ r x)
    (fun _ h => h)
  have hrow (r : Row) : w.eventProbability (fun x => q ^ (-C) < ρ r x) ≤
      q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J :=
    (finiteProbability_rank_markov w (ρ r) (hρ r) hq0).trans
      (mul_le_mul_of_nonneg_left (hmean r) (Real.rpow_nonneg hq0.le C))
  calc
    _ ≤ ∑ _r : Row, q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J :=
      hunion.trans (Finset.sum_le_sum (fun r _ => hrow r))
    _ = (Fintype.card Row : ℝ) * (q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J) := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ ≤ q ^ D * (q ^ C * (q ^ (-(1 : ℝ) / 2)) ^ J) :=
      mul_le_mul_of_nonneg_right hrows (by positivity)
    _ = q ^ (D + C + (-(1 : ℝ) / 2) * J) := by
      rw [← Real.rpow_mul_natCast hq0.le, ← Real.rpow_add hq0,
        ← Real.rpow_add hq0]
      congr 1
      ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith only [hJ])

end Erdos3

end

end OAI

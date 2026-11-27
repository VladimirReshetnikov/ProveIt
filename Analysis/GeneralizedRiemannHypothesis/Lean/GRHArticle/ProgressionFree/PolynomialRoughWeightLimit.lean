import GRHArticle.ProgressionFree.PolynomialSmoothApproximation
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Passing rough-factor counts through the smooth optimization series
-/

namespace GRHArticle.ProgressionFree

open Filter Topology
open scoped BigOperators

/-- A normalized rough count with a limit can be summed against the smooth
optimization weights. Each rough count in `[0,1]` is dominated by the
summable smooth weights, including the cutoff where no rough class exists. -/
theorem tendsto_polynomialSmoothMaximum_weighted_convolution
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (T : ℕ)
    {r : ℕ → ℝ} {c : ℝ} (hr : ∀ n, r n ∈ Set.Icc 0 1)
    (hR : Tendsto r atTop (𝓝 c)) :
    Tendsto (fun N ↦ ∑ t ∈ Finset.range (N+1),
      r (N-t) * ((polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t)) atTop
      (𝓝 (c * ∑' t : ℕ, (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t)) := by
  let w (t : ℕ) := (polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹ ^ t
  let a (N t : ℕ) := if t ≤ N then r (N-t) * w t else 0
  have hw (t : ℕ) : 0 ≤ w t := by dsimp [w]; positivity
  have hpoint (t : ℕ) : Tendsto (a · t) atTop (𝓝 (c * w t)) := by
    refine ((hR.comp (tendsto_sub_atTop_nat t)).mul tendsto_const_nhds).congr' ?_
    filter_upwards [eventually_ge_atTop t] with N hN
    exact (if_pos hN).symm
  have hbound (N t : ℕ) : ‖a N t‖ ≤ w t := by
    by_cases h : t ≤ N
    · simp only [a, if_pos h, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hr _).1 (hw t))]
      exact mul_le_of_le_one_left (hw t) (hr _).2
    · simpa only [a, if_neg h, norm_zero] using hw t
  have hlimit := tendsto_tsum_of_dominated_convergence
    (summable_polynomialSmoothMaximum_weight (F := F) T) hpoint
    (Eventually.of_forall hbound)
  have hfinite (N : ℕ) : (∑' t, a N t) = ∑ t ∈ Finset.range (N+1), r (N-t) * w t := by
    rw [tsum_eq_sum (s := Finset.range (N+1))]
    · apply Finset.sum_congr rfl
      intro t ht
      exact if_pos (Nat.le_of_lt_succ (Finset.mem_range.mp ht))
    · intro t ht
      exact if_neg fun ht' ↦ ht (Finset.mem_range.mpr (Nat.lt_succ_of_le ht'))
  simpa only [hfinite, tsum_mul_left] using hlimit

/-- Divide the scalar/rough class count by the full degree-ball cardinal. -/
theorem polynomialSmoothMaximum_weighted_convolution_scale
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] (T N : ℕ) (r : ℕ → ℕ) :
    ((((Fintype.card F - 1) * ∑ t ∈ Finset.range (N+1),
        r (N-t) * polynomialSmoothMaximum F T t : ℕ) : ℝ) / (Fintype.card F : ℝ)^(N+1)) =
      (1 - (Fintype.card F : ℝ)⁻¹) * ∑ t ∈ Finset.range (N+1),
        ((r (N-t) : ℝ) / (Fintype.card F : ℝ)^(N-t)) *
          ((polynomialSmoothMaximum F T t : ℝ) * (Fintype.card F : ℝ)⁻¹^t) := by
  have hqₙ : 0 < Fintype.card F := Fintype.card_pos
  let q := (Fintype.card F : ℝ)
  have hq : 0 < q := by change 0 < (Fintype.card F : ℝ); exact_mod_cast hqₙ
  simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_sub hqₙ, Nat.cast_one, Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  have hNt := Nat.le_of_lt_succ (Finset.mem_range.mp ht)
  have hsplit : q^(N+1) = q^(N-t)*q^t*q := by
    rw [← pow_add, Nat.sub_add_cancel hNt, pow_succ]
  change (q-1) * ((r (N-t) : ℝ) * (polynomialSmoothMaximum F T t : ℝ)) * (q^(N+1))⁻¹ = _
  rw [hsplit, inv_pow]
  field_simp [hq.ne']
  dsimp only [q]
  ring

end GRHArticle.ProgressionFree

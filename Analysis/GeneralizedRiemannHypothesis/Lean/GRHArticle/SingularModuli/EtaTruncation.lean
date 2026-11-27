import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# The omitted part of the Euler product in the eta expansion

The class-polynomial certificate applies this error to the unpowered
product before raising its enclosure to the twenty-fourth power.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators

private theorem summable_norm_q_pow {q : ℂ} (hq : ‖q‖ < 1) (M : ℕ) :
    Summable (fun n : ℕ => ‖q ^ (n + M)‖) := by
  simp only [pow_add, norm_mul, norm_pow]
  exact (summable_geometric_of_lt_one (norm_nonneg _) hq).mul_right _

private theorem tsum_norm_q_pow_lt {q : ℂ} (hq : ‖q‖ ≤ 1 / 200) (M : ℕ) :
    (∑' n : ℕ, ‖q ^ (n + M)‖) < 2 * (1 / 200 : ℝ) ^ M := by
  have hq1 : ‖q‖ < 1 := hq.trans_lt (by norm_num)
  have hrecip : (1 - ‖q‖)⁻¹ < 2 := by
    rw [← one_div, div_lt_iff₀ (by linarith : 0 < 1 - ‖q‖)]
    linarith
  simp only [pow_add, norm_mul, norm_pow, tsum_mul_right, tsum_geometric_of_lt_one (norm_nonneg _) hq1]
  calc
    _ ≤ (1 - ‖q‖)⁻¹ * (1 / 200 : ℝ) ^ M :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hq _) (by positivity)
    _ < _ := mul_lt_mul_of_pos_right hrecip (by positivity)

private theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hsmall : x ≤ 1 / 2) :
    Real.exp x - 1 ≤ 2 * x := by
  have h₁ : 0 < 1 - x := by linarith
  have hrecip : 1 / (1 - x) ≤ 1 + 2 * x := by
    rw [div_le_iff₀ h₁]
    nlinarith only [mul_nonneg hx (show 0 ≤ 1 - 2 * x by linarith)]
  have hexp := (Real.exp_bound_div_one_sub_of_interval hx (by linarith)).trans hrecip
  linarith

private theorem norm_finsetProd_one_add_sub_one_le (s : Finset ℕ)
    (f : ℕ → ℂ) (hf : Summable (fun n => ‖f n‖)) :
    ‖(∏ n ∈ s, (1 + f n)) - 1‖ ≤ Real.exp (∑' n, ‖f n‖) - 1 :=
  (s.norm_prod_one_add_sub_one_le f).trans
    (sub_le_sub_right (Real.exp_le_exp.mpr (hf.sum_le_tsum _ (fun _ _ => norm_nonneg _))) _)

private theorem norm_tprod_one_add_sub_one_le (f : ℕ → ℂ)
    (hf : Summable (fun n => ‖f n‖)) :
    ‖(∏' n, (1 + f n)) - 1‖ ≤ Real.exp (∑' n, ‖f n‖) - 1 := by
  have hp := multipliable_one_add_of_summable hf
  exact le_of_tendsto' (hp.hasProd.tendsto_prod_nat.sub tendsto_const_nhds).norm
    (fun n => norm_finsetProd_one_add_sub_one_le (Finset.range n) f hf)

private theorem tsum_norm_q_pow_le_half {q : ℂ} (hq : ‖q‖ ≤ 1 / 200)
    {M : ℕ} (hM : 1 ≤ M) : (∑' n : ℕ, ‖q ^ (n + M)‖) ≤ 1 / 2 := by
  refine (tsum_norm_q_pow_lt hq M).le.trans ?_
  refine (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)).trans
    (show (2 : ℝ) * (1 / 200) ^ 1 ≤ 1 / 2 by norm_num)
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hM

private theorem summable_neg_q_pow {q : ℂ} (hq : ‖q‖ < 1) (M : ℕ) :
    Summable (fun n : ℕ => ‖-(q ^ (n + M))‖) := by
  simpa only [norm_neg] using summable_norm_q_pow hq M

private theorem exp_tsum_norm_q_pow_sub_one_le {q : ℂ} (hq : ‖q‖ ≤ 1 / 200)
    {M : ℕ} (hM : 1 ≤ M) :
    Real.exp (∑' n : ℕ, ‖q ^ (n + M)‖) - 1 ≤ 2 * (∑' n : ℕ, ‖q ^ (n + M)‖) :=
  exp_sub_one_le_two_mul (tsum_nonneg (fun _ => norm_nonneg _)) (tsum_norm_q_pow_le_half hq hM)

private theorem norm_eulerProduct_prefix_le_two {q : ℂ} (hq : ‖q‖ ≤ 1 / 200) (N : ℕ) :
    ‖∏ n ∈ Finset.range N, (1 - q ^ (n + 1))‖ ≤ 2 := by
  let P : ℂ := ∏ n ∈ Finset.range N, (1 - q ^ (n + 1))
  let S : ℝ := ∑' n : ℕ, ‖q ^ (n + 1)‖
  have hpClose : ‖P - 1‖ ≤ Real.exp S - 1 := by
    simpa only [P, S, sub_eq_add_neg, norm_neg] using
      norm_finsetProd_one_add_sub_one_le (Finset.range N) (fun n => -(q ^ (n + 1)))
        (summable_neg_q_pow (hq.trans_lt (by norm_num)) 1)
  change ‖P‖ ≤ 2
  calc
    _ ≤ ‖P - 1‖ + 1 := by simpa only [norm_one] using norm_le_norm_sub_add P (1 : ℂ)
    _ ≤ (Real.exp S - 1) + 1 := add_le_add_left hpClose 1
    _ ≤ 2 * S + 1 := add_le_add_left (exp_tsum_norm_q_pow_sub_one_le hq le_rfl) 1
    _ ≤ 2 := by
      have hs : S ≤ 1 / 2 := tsum_norm_q_pow_le_half hq le_rfl
      linarith only [hs]

private theorem norm_eulerProduct_tail_sub_one_lt {q : ℂ} (hq : ‖q‖ ≤ 1 / 200)
    {M : ℕ} (hM : 1 ≤ M) :
    ‖(∏' n : ℕ, (1 - q ^ (n + M))) - 1‖ < 4 * (1 / 200 : ℝ) ^ M := by
  let S : ℝ := ∑' n : ℕ, ‖q ^ (n + M)‖
  calc
    _ ≤ Real.exp S - 1 := by
      simpa only [S, sub_eq_add_neg, norm_neg] using
        norm_tprod_one_add_sub_one_le (fun n => -(q ^ (n + M)))
          (summable_neg_q_pow (hq.trans_lt (by norm_num)) M)
    _ ≤ 2 * S := exp_tsum_norm_q_pow_sub_one_le hq hM
    _ < 2 * (2 * (1 / 200 : ℝ) ^ M) :=
      mul_lt_mul_of_pos_left (tsum_norm_q_pow_lt hq M) (by norm_num)
    _ = _ := by ring

/-- The absolute error in the unpowered Euler product after N factors. -/
theorem norm_eulerProduct_sub_trunc_lt {q : ℂ} (hq : ‖q‖ ≤ 1 / 200) (N : ℕ) :
    ‖(∏' n : ℕ, (1 - q ^ (n + 1))) - (∏ n ∈ Finset.range N, (1 - q ^ (n + 1)))‖ <
      8 / 200 ^ (N + 1) := by
  let f (n : ℕ) : ℂ := 1 - q ^ (n + 1)
  have hf : Multipliable (fun n : ℕ => f (n + N)) := by
    simpa only [f, sub_eq_add_neg, Nat.add_assoc] using
      multipliable_one_add_of_summable (summable_neg_q_pow (hq.trans_lt (by norm_num)) (N + 1))
  have hp : ‖∏ n ∈ Finset.range N, f n‖ ≤ 2 := norm_eulerProduct_prefix_le_two hq N
  have ht : ‖(∏' n : ℕ, f (n + N)) - 1‖ < 4 * (1 / 200 : ℝ) ^ (N + 1) := by
    simpa only [f, Nat.add_assoc] using
      norm_eulerProduct_tail_sub_one_lt hq (Nat.succ_le_succ (Nat.zero_le N))
  let P : ℂ := ∏ n ∈ Finset.range N, f n
  let T : ℂ := ∏' n : ℕ, f (n + N)
  have hprod : P * T = ∏' n, f n :=
    Multipliable.prod_mul_tprod_nat_mul' (f := f) (k := N) hf
  have hdiff : (∏' n, f n) - P = P * (T - 1) :=
    (congrArg (· - P) hprod.symm).trans (mul_sub_one P T).symm
  change ‖(∏' n, f n) - P‖ < _
  calc
    _ = ‖P‖ * ‖T - 1‖ := (congrArg norm hdiff).trans (norm_mul P (T - 1))
    _ ≤ 2 * ‖T - 1‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ < 2 * (4 * (1 / 200 : ℝ) ^ (N + 1)) := mul_lt_mul_of_pos_left ht (by norm_num)
    _ = 8 / 200 ^ (N + 1) := by rw [div_pow, one_pow]; ring

/-- The 164-factor product enclosure from the class-polynomial verifier. -/
theorem norm_eulerProduct_sub_trunc164_lt {q : ℂ} (hq : ‖q‖ ≤ 1 / 200) :
    ‖(∏' n : ℕ, (1 - q ^ (n + 1))) - (∏ n ∈ Finset.range 164, (1 - q ^ (n + 1)))‖ <
      8 / 200 ^ 165 :=
  norm_eulerProduct_sub_trunc_lt hq 164

end GRHArticle.SingularModuli

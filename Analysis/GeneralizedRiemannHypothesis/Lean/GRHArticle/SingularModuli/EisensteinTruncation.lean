import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

/-!
# A certified error for the weight-four Eisenstein series

The divisor bound and geometric tail give the explicit 164-term
truncation error used in the class polynomial certificates.
-/

namespace GRHArticle.SingularModuli

open scoped BigOperators

private theorem sum_recip_cube_Icc_le (n : ℕ) :
    (∑ d ∈ Finset.Icc 1 n, ((d : ℝ) ^ 3)⁻¹) ≤ 2 - (n : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      norm_num
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hs : ((n + 1 : ℕ) : ℝ) ^ 3 > 0 := by positivity
    have hstep : (((n + 1 : ℕ) : ℝ) ^ 3)⁻¹ ≤ (n : ℝ)⁻¹ - ((n + 1 : ℕ) : ℝ)⁻¹ := by
      push_cast
      field_simp
      nlinarith [sq_nonneg (n : ℝ), mul_nonneg hn0.le (sq_nonneg (n : ℝ))]
    linarith

/-- The sum of the cubes of the divisors is bounded by twice the cube of
the integer, by summing the reciprocals of the complementary divisors. -/
theorem sigma_three_le (n : ℕ) : ArithmeticFunction.sigma 3 n ≤ 2 * n ^ 3 := by
  by_cases hn : n = 0
  · simp [hn]
  suffices h : (ArithmeticFunction.sigma 3 n : ℝ) ≤ 2 * (n : ℝ) ^ 3 by exact_mod_cast h
  rw [ArithmeticFunction.sigma_apply, ← Nat.sum_div_divisors n (fun d : ℕ => d ^ 3)]
  push_cast
  have he (d : ℕ) (hd : d ∈ n.divisors) : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
    have hd₀ : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
    apply (eq_div_iff hd₀.ne').mpr
    exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)⟩
  calc
    _ = (n : ℝ) ^ 3 * ∑ d ∈ n.divisors, ((d : ℝ) ^ 3)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [he d hd, div_pow, div_eq_mul_inv]
    _ ≤ (n : ℝ) ^ 3 * (2 - (n : ℝ)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
        (sum_recip_cube_Icc_le n)
    _ ≤ 2 * (n : ℝ) ^ 3 := by
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) (by positivity)

private theorem add_le_mul_two_pow (M n : ℕ) (hM : 0 < M) : n + M ≤ M * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    calc
      n + 1 + M ≤ 2 * (n + M) := by omega
      _ ≤ 2 * (M * 2 ^ n) := Nat.mul_le_mul_left 2 ih
      _ = _ := by ac_rfl

private theorem norm_eisensteinTerm_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 200) (M n : ℕ)
    (hM : 0 < M) :
    ‖(ArithmeticFunction.sigma 3 (n + M) : ℂ) * q ^ (n + M)‖ ≤
      (2 * (M : ℝ) ^ 3 * (1 / 200) ^ M) * (1 / 2) ^ n := by
  have hσ : (ArithmeticFunction.sigma 3 (n + M) : ℝ) ≤ 2 * ((n + M : ℕ) : ℝ) ^ 3 := by
    exact_mod_cast sigma_three_le (n + M)
  have hn : ((n + M : ℕ) : ℝ) ≤ (M : ℝ) * 2 ^ n := by
    exact_mod_cast add_le_mul_two_pow M n hM
  have hpow : ((2 : ℝ) ^ n) ^ 3 = (2 ^ 3 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 3, pow_mul]
  calc
    _ = (ArithmeticFunction.sigma 3 (n + M) : ℝ) * ‖q‖ ^ (n + M) := by
      rw [norm_mul, norm_pow, Complex.norm_natCast]
    _ ≤ (2 * ((n + M : ℕ) : ℝ) ^ 3) * (1 / 200 : ℝ) ^ (n + M) := by
      exact mul_le_mul hσ (pow_le_pow_left₀ (norm_nonneg _) hq _)
        (by positivity) (by positivity)
    _ ≤ (2 * ((M : ℝ) * 2 ^ n) ^ 3) * (1 / 200 : ℝ) ^ (n + M) := by
      gcongr
    _ = (2 * (M : ℝ) ^ 3 * (1 / 200) ^ M) * (2 ^ 3 * (1 / 200)) ^ n := by
      simp only [pow_add, mul_pow, hpow]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by norm_num) _

private theorem summable_eisensteinTail (q : ℂ) (hq : ‖q‖ ≤ 1 / 200) (M : ℕ)
    (hM : 0 < M) :
    Summable (fun n : ℕ => ‖(ArithmeticFunction.sigma 3 (n + M) : ℂ) * q ^ (n + M)‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => norm_eisensteinTerm_le q hq M n hM)
    ((summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left _)

/-- The exact class-polynomial certificate bound for the weight-four
Eisenstein series after summing the terms of degrees 1 through 164. -/
theorem norm_eisensteinFour_sub_trunc164_le (q : ℂ) (hq : ‖q‖ ≤ 1 / 200) :
    ‖(1 + 240 * ∑' n : ℕ+, (ArithmeticFunction.sigma 3 n : ℂ) * q ^ (n : ℕ)) -
      (1 + 240 * ∑ n ∈ Finset.range 164,
        (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * q ^ (n + 1))‖ ≤
      960 * 165 ^ 3 / 200 ^ 165 := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => (ArithmeticFunction.sigma 3 n : ℂ) * q ^ n)]
  let f (n : ℕ) : ℂ := (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * q ^ (n + 1)
  have hfs : Summable f := (summable_eisensteinTail q hq 1 (by decide)).of_norm
  have hs : (∑ n ∈ Finset.range 164, f n) + (∑' n, f (n + 164)) = ∑' n, f n :=
    hfs.sum_add_tsum_nat_add 164
  have he : (1 + 240 * (∑' n, f n)) - (1 + 240 * ∑ n ∈ Finset.range 164, f n) =
      240 * ∑' n, f (n + 164) := by
    rw [← hs]
    ring
  change ‖(1 + 240 * (∑' n, f n)) - (1 + 240 * ∑ n ∈ Finset.range 164, f n)‖ ≤ _
  rw [he, norm_mul, show ‖(240 : ℂ)‖ = 240 by norm_num]
  apply (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 240)).trans
    (show (240 : ℝ) * (2 * 165 ^ 3 * (1 / 200) ^ 165 * 2) ≤
      960 * 165 ^ 3 / 200 ^ 165 by
        apply le_of_eq
        rw [div_pow, one_pow]
        ring)
  have ht : Summable (fun n => ‖f (n + 164)‖) := summable_eisensteinTail q hq 165 (by decide)
  let C : ℝ := 2 * 165 ^ 3 * (1 / 200) ^ 165
  have hg : Summable (fun n : ℕ => C * (1 / 2) ^ n) :=
    (summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left C
  refine (norm_tsum_le_tsum_norm ht).trans ((ht.tsum_le_tsum ?_ hg).trans_eq ?_)
  · exact fun n => norm_eisensteinTerm_le q hq 165 n (by decide)
  · rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num only [one_div, inv_inv]

end GRHArticle.SingularModuli

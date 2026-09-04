import FabiusFunction.AndrewsGordon

/-!
# The Andrews–Gordon identities, the case `i = 1`

With `K = k - 1` steps of the finite limiting lemma relative to `q` applied to the unit pair,
and the infinite limiting lemma relative to `q`,

  `∑_n q^{n(n+1)} β^{(K)}_n = (q, q^{M-1}, q^M; q^M)_∞ / (q;q)_∞`,  `M = 2K + 3`

(`hasSum_andrewsGordon_one`).  For `K = 1` this is the second Rogers–Ramanujan identity.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- **Andrews–Gordon, `i = 1`** (qg:thm-andrews-gordon, nested form). -/
theorem hasSum_andrewsGordon_one {q : 𝕜} (hq : ‖q‖ < 1) (K : ℕ) :
    HasSum (fun n : ℕ => q ^ (n * (n + 1)) * baileyChainBeta q q unitBaileyBeta K n)
      (qPochhammerInfIn q (q ^ (2 * K + 3)) * qPochhammerInfIn (q ^ (2 * K + 2)) (q ^ (2 * K + 3)) *
        qPochhammerInfIn (q ^ (2 * K + 3)) (q ^ (2 * K + 3)) / qPochhammerInfIn q q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have h : HasSum (fun n : ℕ => (0 : 𝕜) ^ (n * (n + 1)) * baileyChainBeta 0 0 unitBaileyBeta K n)
        ((0 : 𝕜) ^ (0 * (0 + 1)) * baileyChainBeta 0 0 unitBaileyBeta K 0) :=
      hasSum_single 0 fun n hn => by rw [zero_pow (mul_ne_zero hn n.succ_ne_zero), zero_mul]
    rw [baileyChainBeta_apply_zero] at h
    simpa [unitBaileyBeta, qPochhammerInfIn] using h
  have hq' : ∀ n, finiteQPochhammerIn q q n ≠ 0 := finiteQPochhammerIn_self_ne_zero hq
  have hQ : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  have hqq : ‖q * q‖ < 1 := by
    rw [norm_mul]
    calc ‖q‖ * ‖q‖ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right hq.le (norm_nonneg q)
      _ < 1 := by rw [one_mul]; exact hq
  have hQQ : qPochhammerInfIn (q * q) q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hqq
  have hq2 : ∀ n, finiteQPochhammerIn (q * q) q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (q * q) hq hQQ
  have P := (isBaileyPair_unit_q hq').chain hq' hq2 K
  set C₁ : ℝ := qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ with hC₁def
  have hC : ∀ n, ‖finiteQPochhammerIn q q n‖⁻¹ ≤ C₁ := fun n =>
    inv_norm_finiteQPochhammerIn_le q hq hQ n
  have hC0 : 0 ≤ C₁ := (inv_nonneg.mpr (norm_nonneg _)).trans (hC 0)
  have hgeom := summable_geometric_of_lt_one (norm_nonneg q) hq
  have hqn : ∀ n : ℕ, ‖q‖ ^ (n * n) ≤ ‖q‖ ^ n := fun n =>
    pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_mul_self n)
  have hqle : ∀ n : ℕ, ‖q‖ ^ n ≤ 1 := fun n => pow_le_one₀ (norm_nonneg q) hq.le
  have hqInt : ∀ n : ℕ, ‖qInt q n‖ ≤ n := by
    intro n
    unfold qInt
    calc ‖∑ i ∈ range n, q ^ i‖ ≤ ∑ i ∈ range n, ‖q ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ range n, (1 : ℝ) := sum_le_sum fun i _ => by rw [norm_pow]; exact hqle i
      _ = n := by simp
  have hα1 : ∀ n : ℕ, ‖unitBaileyAlphaQ q n‖ ≤ 2 * n + 1 := by
    intro n
    unfold unitBaileyAlphaQ
    rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
    calc ‖q‖ ^ n.choose 2 * ‖qInt q (2 * n + 1)‖ ≤ 1 * ((2 * n + 1 : ℕ) : ℝ) :=
          mul_le_mul (hqle _) (hqInt _) (norm_nonneg _) zero_le_one
      _ = 2 * n + 1 := by push_cast; ring
  have hgeom' : Summable fun n : ℕ => (2 * (n : ℝ) + 1) * ‖q‖ ^ n := by
    have h1 : Summable fun n : ℕ => (n : ℝ) * ‖q‖ ^ n := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖)
        (by rw [norm_norm]; exact hq)
    have h2 := (h1.mul_left 2).add hgeom
    refine h2.congr fun n => ?_
    ring
  have hα : Summable fun n : ℕ =>
      ‖q ^ n * q ^ (n * n) * baileyChainAlpha q q (unitBaileyAlphaQ q) K n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom'
    simp only [baileyChainAlpha]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, norm_pow]
    calc ‖q‖ ^ n * ‖q‖ ^ (n * n) * (‖q‖ ^ (K * n) * ‖q‖ ^ (K * (n * n)) * ‖unitBaileyAlphaQ q n‖)
        ≤ ‖q‖ ^ n * 1 * (1 * 1 * (2 * n + 1)) := by
          gcongr
          · exact hqle _
          · exact hqle _
          · exact hqle _
          · exact hα1 n
      _ = (2 * (n : ℝ) + 1) * ‖q‖ ^ n := by ring
  have hβin : ∀ j, ‖baileyChainBeta q q unitBaileyBeta K j‖ ≤ C₁ ^ K * ((j : ℝ) + 1) ^ K := by
    intro j
    have := norm_baileyChainBeta_le (a := q) hq.le hq.le hC (β := unitBaileyBeta) (B := 1) (s := 0)
      (fun j => by
        unfold unitBaileyBeta
        split_ifs <;> simp) K j
    simpa using this
  have hβ : Summable fun n : ℕ =>
      ‖q ^ n * q ^ (n * n) * baileyChainBeta q q unitBaileyBeta K n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_succ_pow_mul_geometric (norm_nonneg q) hq K).mul_left (C₁ ^ K))
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖q‖ ^ n * ‖q‖ ^ (n * n) * ‖baileyChainBeta q q unitBaileyBeta K n‖
        ≤ ‖q‖ ^ n * 1 * (C₁ ^ K * ((n : ℝ) + 1) ^ K) := by
          gcongr
          · exact hqle _
          · exact hβin n
      _ = C₁ ^ K * (((n : ℝ) + 1) ^ K * ‖q‖ ^ n) := by ring
  have hmain := IsBaileyPair.hasSum_limit hq hQQ P hα hβ
  -- the theta series, by Jacobi's triple product with base `q^M` and `z = q^{M-1}`
  have hM1 : ‖q ^ (2 * K + 3)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hz : (q ^ (2 * K + 2) : 𝕜) ≠ 0 := pow_ne_zero _ hq0
  have hJ := (hasSum_jacobi_triple_product hM1 hz).nat_add_neg_add_one
  have h1q : (1 : 𝕜) - q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  have hterm : ∀ n : ℕ,
      (1 - q) * (q ^ n * q ^ (n * n) * baileyChainAlpha q q (unitBaileyAlphaQ q) K n) =
      (-1 : 𝕜) ^ (n : ℤ) * (q ^ (2 * K + 3)) ^ thetaExponent (n : ℤ) * (q ^ (2 * K + 2)) ^ (n : ℤ) +
        (-1 : 𝕜) ^ (-((n : ℤ) + 1)) * (q ^ (2 * K + 3)) ^ thetaExponent (-((n : ℤ) + 1)) *
          (q ^ (2 * K + 2)) ^ (-((n : ℤ) + 1)) := by
    intro n
    have hcast : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast]
    simp only [zpow_neg, zpow_natCast, thetaExponent_natCast, thetaExponent_neg_natCast,
      baileyChainAlpha, unitBaileyAlphaQ]
    have h1 : ((-1 : 𝕜) ^ (n + 1))⁻¹ = -(-1) ^ n := by
      rw [← inv_pow, inv_neg, inv_one, pow_succ]
      ring
    rw [h1]
    simp only [← pow_mul]
    have hE1 : n + n * n + K * n + K * (n * n) + n.choose 2 =
        (2 * K + 3) * n.choose 2 + (2 * K + 2) * n := by
      have h1 := two_mul_choose_two_int n
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
      zify
      linear_combination (1 - (2 * (K : ℤ) + 3)) * h1
    have hE2 : n + n * n + K * n + K * (n * n) + n.choose 2 + (2 * n + 1) + (2 * K + 2) * (n + 1) =
        (2 * K + 3) * (n + 1 + 1).choose 2 := by
      have h1 := two_mul_choose_two_int n
      have h2 := two_mul_choose_two_int (n + 1 + 1)
      push_cast at h1 h2
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
      zify
      linear_combination h1 - (2 * (K : ℤ) + 3) * h2
    have e1 : q ^ ((2 * K + 3) * n.choose 2) * q ^ ((2 * K + 2) * n) =
        q ^ n * q ^ (n * n) * q ^ (K * n) * q ^ (K * (n * n)) * q ^ n.choose 2 := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, hE1]
    have e2 : q ^ ((2 * K + 3) * (n + 1 + 1).choose 2) =
        q ^ n * q ^ (n * n) * q ^ (K * n) * q ^ (K * (n * n)) * q ^ n.choose 2 * q ^ (2 * n + 1) *
          q ^ ((2 * K + 2) * (n + 1)) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, hE2]
    have hinv : q ^ ((2 * K + 2) * (n + 1)) * (q ^ ((2 * K + 2) * (n + 1)))⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hq0)
    have hqI : (1 - q) * qInt q (2 * n + 1) = 1 - q ^ (2 * n + 1) := one_sub_mul_qInt q _
    linear_combination
      (q ^ n * q ^ (n * n) * (q ^ (K * n) * q ^ (K * (n * n))) * ((-1 : 𝕜) ^ n * q ^ n.choose 2)) * hqI +
      (-((-1 : 𝕜) ^ n)) * e1 +
      ((-1 : 𝕜) ^ n * (q ^ ((2 * K + 2) * (n + 1)))⁻¹) * e2 +
      ((-1 : 𝕜) ^ n * q ^ n * q ^ (n * n) * q ^ (K * n) * q ^ (K * (n * n)) * q ^ n.choose 2 *
        q ^ (2 * n + 1)) * hinv
  have hsum : HasSum (fun n : ℕ => q ^ n * q ^ (n * n) * baileyChainAlpha q q (unitBaileyAlphaQ q) K n)
      ((1 - q)⁻¹ * (qPochhammerInfIn (q ^ (2 * K + 2)) (q ^ (2 * K + 3)) *
        qPochhammerInfIn (q ^ (2 * K + 3) / q ^ (2 * K + 2)) (q ^ (2 * K + 3)) *
        qPochhammerInfIn (q ^ (2 * K + 3)) (q ^ (2 * K + 3)))) := by
    have h := (hJ.congr_fun hterm).mul_left (1 - q)⁻¹
    refine h.congr_fun fun n => ?_
    field_simp
  rw [hsum.tsum_eq] at hmain
  have hshift : qPochhammerInfIn q q = (1 - q) * qPochhammerInfIn (q * q) q := by
    rw [qPochhammerInfIn_eq_finite_mul_shift q hq 1, finiteQPochhammerIn, prod_range_one, pow_zero,
      mul_one, pow_one]
  have hval : (qPochhammerInfIn (q * q) q)⁻¹ * ((1 - q)⁻¹ *
      (qPochhammerInfIn (q ^ (2 * K + 2)) (q ^ (2 * K + 3)) *
        qPochhammerInfIn (q ^ (2 * K + 3) / q ^ (2 * K + 2)) (q ^ (2 * K + 3)) *
        qPochhammerInfIn (q ^ (2 * K + 3)) (q ^ (2 * K + 3)))) =
      qPochhammerInfIn q (q ^ (2 * K + 3)) * qPochhammerInfIn (q ^ (2 * K + 2)) (q ^ (2 * K + 3)) *
        qPochhammerInfIn (q ^ (2 * K + 3)) (q ^ (2 * K + 3)) / qPochhammerInfIn q q := by
    rw [show q ^ (2 * K + 3) / q ^ (2 * K + 2) = q by rw [div_eq_iff hz]; ring, hshift,
      div_eq_inv_mul, mul_inv]
    ring
  rw [hval] at hmain
  refine hmain.congr_fun fun n => ?_
  rw [← pow_add, show n + n * n = n * (n + 1) by ring]

end Fabius

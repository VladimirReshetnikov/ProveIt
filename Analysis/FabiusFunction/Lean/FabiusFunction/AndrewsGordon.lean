import FabiusFunction.BaileyChainBounds
import FabiusFunction.BaileyLowering
import FabiusFunction.BaileyLimitInfinite
import FabiusFunction.RogersRamanujan
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith

/-!
# The Andrews–Gordon identities (nested form)

For `‖q‖ < 1`, `k ≥ 2` and `1 ≤ i ≤ k`, with `M = 2k+1`,

  `∑_{n_1,…,n_{k-1} ≥ 0} q^{N_1²+⋯+N_{k-1}²+N_i+⋯+N_{k-1}} / ((q;q)_{n_1} ⋯ (q;q)_{n_{k-1}})
    = (q^i, q^{M-i}, q^M; q^M)_∞ / (q;q)_∞`,  `N_j = n_j + ⋯ + n_{k-1}`.

Following the monograph's proof, the left side is written with the decreasing variables
`r_j = N_j` as the outer sum `∑_n q^{n²+[i=1]n} β_n` of a Bailey chain: for `i = 1`, `K = k-1`
steps of the finite limiting lemma relative to `a = q` applied to the unit pair
(`hasSum_andrewsGordon_one`); for `2 ≤ i ≤ k`, with `t = k-i+1` and `u = i-2`, `t` steps
relative to `q`, the parameter-lowering shift to `a = 1`, and `u` steps relative to `1`
(`hasSum_andrewsGordon_of_two_le`).  In both cases the infinite limiting lemma, the closed form
of the transformed `α` (`baileyLowered_chain_unit_succ`) and Jacobi's triple product with base
`q^M` finish the proof.  The nested chain sums `baileyChainBeta` are the multiple sums
`qg:eq:andrews-gordon-decreasing` of the text.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

/-- `∑ (n+1)^K r^n` converges for `0 ≤ r < 1`. -/
theorem summable_succ_pow_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (K : ℕ) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ K * r ^ n := by
  have hr' : ‖r‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr
  have hs : Summable fun n : ℕ =>
      ∑ j ∈ range (K + 1), (K.choose j : ℝ) * ((n : ℝ) ^ j * r ^ n) :=
    summable_sum (f := fun j (n : ℕ) => (K.choose j : ℝ) * ((n : ℝ) ^ j * r ^ n))
      (s := range (K + 1)) fun j _ =>
        (summable_pow_mul_geometric_of_norm_lt_one j hr').mul_left (K.choose j : ℝ)
  refine hs.congr fun n => ?_
  rw [add_pow, sum_mul]
  refine sum_congr rfl fun j _ => ?_
  ring

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

omit [CompleteSpace 𝕜] in
theorem baileyChainBeta_apply_zero (a q : 𝕜) (β : ℕ → 𝕜) (t : ℕ) :
    baileyChainBeta a q β t 0 = β 0 := by
  induction t with
  | zero => rw [baileyChainBeta_zero]
  | succ t ih =>
      have h0 : finiteQPochhammerIn q q 0 = 1 := by simp [finiteQPochhammerIn]
      rw [baileyChainBeta_succ, sum_range_one, ih, pow_zero, Nat.mul_zero, pow_zero, Nat.sub_zero, h0,
        div_one, one_mul, one_mul]

omit [CompleteSpace 𝕜] in
/-- The closed form of the lowered `t`-fold chain of the unit pair relative to `q`:
`δ_0 = 1` and `δ_{n+1} = (-1)^{n+1} (q^{t(n+1)(n+2) + C(n+1,2)} + q^{2n+1 + tn(n+1) + C(n,2)})`. -/
theorem baileyLowered_chain_unit_succ {q : 𝕜} (hq : ‖q‖ < 1) (t n : ℕ) :
    baileyLowered q q (baileyChainAlpha q q (unitBaileyAlphaQ q) t) (n + 1) =
      (-1) ^ (n + 1) * (q ^ (t * ((n + 1) * (n + 2)) + (n + 1).choose 2) +
        q ^ (2 * n + 1 + t * (n * (n + 1)) + n.choose 2)) := by
  have hodd : ∀ m : ℕ, (1 : 𝕜) - q * q ^ (2 * m) ≠ 0 := fun m => by
    rw [← pow_succ']
    exact one_sub_ne_zero_of_norm_lt_one
      (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega))
  simp only [baileyLowered, baileyChainAlpha, unitBaileyAlphaQ]
  have e1 : (1 - q) * qInt q (2 * (n + 1) + 1) = 1 - q ^ (2 * (n + 1) + 1) := one_sub_mul_qInt q _
  have e2 : (1 - q) * qInt q (2 * n + 1) = 1 - q ^ (2 * n + 1) := one_sub_mul_qInt q _
  have hA : (1 - q) * (q ^ (t * (n + 1)) * q ^ (t * ((n + 1) * (n + 1))) *
        ((-1) ^ (n + 1) * q ^ (n + 1).choose 2 * qInt q (2 * (n + 1) + 1)) /
        (1 - q * q ^ (2 * (n + 1)))) =
      (-1) ^ (n + 1) * (q ^ (t * (n + 1)) * q ^ (t * ((n + 1) * (n + 1))) * q ^ (n + 1).choose 2) := by
    rw [mul_div_assoc', div_eq_iff (hodd (n + 1)), ← pow_succ']
    linear_combination (q ^ (t * (n + 1)) * q ^ (t * ((n + 1) * (n + 1))) * (-1) ^ (n + 1) *
      q ^ (n + 1).choose 2) * e1
  have hB : (1 - q) * (q * q ^ (2 * n) * (q ^ (t * n) * q ^ (t * (n * n)) *
        ((-1) ^ n * q ^ n.choose 2 * qInt q (2 * n + 1))) / (1 - q * q ^ (2 * n))) =
      (-1) ^ n * (q * q ^ (2 * n) * (q ^ (t * n) * q ^ (t * (n * n)) * q ^ n.choose 2)) := by
    rw [mul_div_assoc', div_eq_iff (hodd n), ← pow_succ']
    linear_combination (q * q ^ (2 * n) * (q ^ (t * n) * q ^ (t * (n * n))) * (-1) ^ n *
      q ^ n.choose 2) * e2
  rw [mul_sub, hA, hB]
  ring

omit [CompleteSpace 𝕜] in
theorem norm_baileyLowered_chain_unit_le {q : 𝕜} (hq : ‖q‖ < 1) (t n : ℕ) :
    ‖baileyLowered q q (baileyChainAlpha q q (unitBaileyAlphaQ q) t) n‖ ≤ 2 := by
  cases n with
  | zero => simp [baileyLowered, baileyChainAlpha, unitBaileyAlphaQ]
  | succ m =>
      rw [baileyLowered_chain_unit_succ hq, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc ‖q ^ (t * ((m + 1) * (m + 2)) + (m + 1).choose 2) +
            q ^ (2 * m + 1 + t * (m * (m + 1)) + m.choose 2)‖
          ≤ ‖q ^ (t * ((m + 1) * (m + 2)) + (m + 1).choose 2)‖ +
            ‖q ^ (2 * m + 1 + t * (m * (m + 1)) + m.choose 2)‖ := norm_add_le _ _
        _ ≤ 1 + 1 := by
            rw [norm_pow, norm_pow]
            exact add_le_add (pow_le_one₀ (norm_nonneg q) hq.le) (pow_le_one₀ (norm_nonneg q) hq.le)
        _ = 2 := by norm_num

/-- **Andrews–Gordon, `2 ≤ i ≤ k`** (qg:thm-andrews-gordon, nested form): with `t = k-i+1`,
`u = i-2`, `M = 2k+1 = 2(t+u)+3` and `i = u+2`,
`∑_n q^{n²} β_n = (q^i, q^{M-i}, q^M; q^M)_∞ / (q;q)_∞`, where `β` is the unit sequence after
`t` chain steps relative to `q`, the lowering shift, and `u` chain steps relative to `1`. -/
theorem hasSum_andrewsGordon_of_two_le {q : 𝕜} (hq : ‖q‖ < 1) (t u : ℕ) :
    HasSum (fun n : ℕ => q ^ (n * n) *
        baileyChainBeta 1 q (baileyChainBeta q q unitBaileyBeta t) u n)
      (qPochhammerInfIn (q ^ (u + 2)) (q ^ (2 * (t + u) + 3)) *
        qPochhammerInfIn (q ^ (2 * t + u + 1)) (q ^ (2 * (t + u) + 3)) *
        qPochhammerInfIn (q ^ (2 * (t + u) + 3)) (q ^ (2 * (t + u) + 3)) /
        qPochhammerInfIn q q) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have h : HasSum (fun n : ℕ => (0 : 𝕜) ^ (n * n) *
          baileyChainBeta 1 0 (baileyChainBeta 0 0 unitBaileyBeta t) u n)
        ((0 : 𝕜) ^ (0 * 0) * baileyChainBeta 1 0 (baileyChainBeta 0 0 unitBaileyBeta t) u 0) :=
      hasSum_single 0 fun n hn => by rw [zero_pow (mul_ne_zero hn hn), zero_mul]
    rw [baileyChainBeta_apply_zero, baileyChainBeta_apply_zero] at h
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
  have hq1 : ∀ n, finiteQPochhammerIn (1 * q) q n ≠ 0 := fun n => by
    rw [one_mul]
    exact hq' n
  -- the Bailey pair: `t` steps relative to `q`, the lowering shift, `u` steps relative to `1`
  have P1 := (isBaileyPair_unit_q hq').chain hq' hq2 t
  have P2 := isBaileyPair_baileyLowered P1 hq0 hq' hq'
  rw [div_self hq0] at P2
  have P3 := P2.chain hq' hq1 u
  set δ := baileyLowered q q (baileyChainAlpha q q (unitBaileyAlphaQ q) t) with hδdef
  have hδ0 : δ 0 = 1 := by simp [hδdef, baileyLowered, baileyChainAlpha, unitBaileyAlphaQ]
  have hδ2 : ∀ n, ‖δ n‖ ≤ 2 := norm_baileyLowered_chain_unit_le hq t
  -- summability of both sides
  set C₁ : ℝ := qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ with hC₁def
  have hC : ∀ n, ‖finiteQPochhammerIn q q n‖⁻¹ ≤ C₁ := fun n =>
    inv_norm_finiteQPochhammerIn_le q hq hQ n
  have hC0 : 0 ≤ C₁ := (inv_nonneg.mpr (norm_nonneg _)).trans (hC 0)
  have hgeom := summable_geometric_of_lt_one (norm_nonneg q) hq
  have hqn : ∀ n : ℕ, ‖q‖ ^ (n * n) ≤ ‖q‖ ^ n := fun n =>
    pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_mul_self n)
  have hα : Summable fun n : ℕ =>
      ‖(1 : 𝕜) ^ n * q ^ (n * n) * baileyChainAlpha 1 q δ u n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeom.mul_left 2)
    simp only [baileyChainAlpha, one_pow, one_mul]
    rw [norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖q‖ ^ (n * n) * (‖q‖ ^ (u * (n * n)) * ‖δ n‖) ≤ ‖q‖ ^ n * (1 * 2) :=
          mul_le_mul (hqn n)
            (mul_le_mul (pow_le_one₀ (norm_nonneg q) hq.le) (hδ2 n) (norm_nonneg _) zero_le_one)
            (by positivity) (by positivity)
      _ = 2 * ‖q‖ ^ n := by ring
  have hβin : ∀ j, ‖baileyChainBeta q q unitBaileyBeta t j‖ ≤ C₁ ^ t * ((j : ℝ) + 1) ^ t := by
    intro j
    have := norm_baileyChainBeta_le (a := q) hq.le hq.le hC (β := unitBaileyBeta) (B := 1) (s := 0)
      (fun j => by
        unfold unitBaileyBeta
        split_ifs <;> simp) t j
    simpa using this
  have hβout : ∀ n, ‖baileyChainBeta 1 q (baileyChainBeta q q unitBaileyBeta t) u n‖ ≤
      C₁ ^ t * C₁ ^ u * ((n : ℝ) + 1) ^ (t + u) := fun n =>
    norm_baileyChainBeta_le (a := (1 : 𝕜)) (by rw [norm_one]) hq.le hC hβin u n
  have hβ : Summable fun n : ℕ =>
      ‖(1 : 𝕜) ^ n * q ^ (n * n) * baileyChainBeta 1 q (baileyChainBeta q q unitBaileyBeta t) u n‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((summable_succ_pow_mul_geometric (norm_nonneg q) hq (t + u)).mul_left (C₁ ^ t * C₁ ^ u))
    rw [one_pow, one_mul, norm_mul, norm_pow]
    calc ‖q‖ ^ (n * n) * ‖baileyChainBeta 1 q (baileyChainBeta q q unitBaileyBeta t) u n‖
        ≤ ‖q‖ ^ n * (C₁ ^ t * C₁ ^ u * ((n : ℝ) + 1) ^ (t + u)) :=
          mul_le_mul (hqn n) (hβout n) (norm_nonneg _) (by positivity)
      _ = C₁ ^ t * C₁ ^ u * (((n : ℝ) + 1) ^ (t + u) * ‖q‖ ^ n) := by ring
  have hmain := IsBaileyPair.hasSum_limit hq (by rw [one_mul]; exact hQ) P3 hα hβ
  simp only [one_pow, one_mul] at hmain
  -- the theta series: Jacobi's triple product with base `q^M`, `z = q^i`
  have hM1 : ‖q ^ (2 * (t + u) + 3)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) hq (by omega)
  have hz : (q ^ (u + 2) : 𝕜) ≠ 0 := pow_ne_zero _ hq0
  have hJ := (hasSum_jacobi_triple_product hM1 hz).nat_add_neg
  have hF0 : (-1 : 𝕜) ^ (0 : ℤ) * (q ^ (2 * (t + u) + 3)) ^ thetaExponent 0 *
      (q ^ (u + 2)) ^ (0 : ℤ) = 1 := by
    simp [thetaExponent]
  have hterm : ∀ n : ℕ, q ^ (n * n) * baileyChainAlpha 1 q δ u n =
      ((-1 : 𝕜) ^ (n : ℤ) * (q ^ (2 * (t + u) + 3)) ^ thetaExponent (n : ℤ) *
          (q ^ (u + 2)) ^ (n : ℤ) +
        (-1 : 𝕜) ^ (-(n : ℤ)) * (q ^ (2 * (t + u) + 3)) ^ thetaExponent (-(n : ℤ)) *
          (q ^ (u + 2)) ^ (-(n : ℤ))) - (if n = 0 then 1 else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [baileyChainAlpha, hδ0, thetaExponent]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [if_neg (Nat.succ_ne_zero m), sub_zero]
      simp only [zpow_neg, zpow_natCast, thetaExponent_natCast, thetaExponent_neg_natCast,
        baileyChainAlpha, one_pow, one_mul]
      rw [hδdef, baileyLowered_chain_unit_succ hq]
      have h1 : ((-1 : 𝕜) ^ (m + 1))⁻¹ = (-1) ^ (m + 1) := by
        rw [← inv_pow, inv_neg, inv_one]
      rw [h1]
      simp only [← pow_mul]
      -- the two exponent identities
      have hE1 : (m + 1) * (m + 1) + u * ((m + 1) * (m + 1)) +
          (2 * m + 1 + t * (m * (m + 1)) + m.choose 2) =
          (2 * (t + u) + 3) * (m + 1).choose 2 + (u + 2) * (m + 1) := by
        have h1 := two_mul_choose_two_int m
        have h2 := two_mul_choose_two_int (m + 1)
        push_cast at h1 h2
        apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
        zify
        linear_combination h1 - (2 * ((t : ℤ) + u) + 3) * h2
      have hE2 : (m + 1) * (m + 1) + u * ((m + 1) * (m + 1)) +
          (t * ((m + 1) * (m + 2)) + (m + 1).choose 2) + (u + 2) * (m + 1) =
          (2 * (t + u) + 3) * (m + 1 + 1).choose 2 := by
        have h1 := two_mul_choose_two_int (m + 1)
        have h2 := two_mul_choose_two_int (m + 1 + 1)
        push_cast at h1 h2
        apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
        zify
        linear_combination h1 - (2 * ((t : ℤ) + u) + 3) * h2
      have e1 : q ^ ((2 * (t + u) + 3) * (m + 1).choose 2) * q ^ ((u + 2) * (m + 1)) =
          q ^ ((m + 1) * (m + 1)) * q ^ (u * ((m + 1) * (m + 1))) *
            q ^ (2 * m + 1 + t * (m * (m + 1)) + m.choose 2) := by
        rw [← pow_add, ← pow_add, ← pow_add, hE1]
      have e2 : q ^ ((2 * (t + u) + 3) * (m + 1 + 1).choose 2) =
          q ^ ((m + 1) * (m + 1)) * q ^ (u * ((m + 1) * (m + 1))) *
            q ^ (t * ((m + 1) * (m + 2)) + (m + 1).choose 2) * q ^ ((u + 2) * (m + 1)) := by
        rw [← pow_add, ← pow_add, ← pow_add, hE2]
      have hinv : q ^ ((u + 2) * (m + 1)) * (q ^ ((u + 2) * (m + 1)))⁻¹ = 1 :=
        mul_inv_cancel₀ (pow_ne_zero _ hq0)
      linear_combination (-((-1 : 𝕜) ^ (m + 1))) * e1 +
        (-((-1 : 𝕜) ^ (m + 1) * (q ^ ((u + 2) * (m + 1)))⁻¹)) * e2 +
        (-((-1 : 𝕜) ^ (m + 1) * q ^ ((m + 1) * (m + 1)) * q ^ (u * ((m + 1) * (m + 1))) *
          q ^ (t * ((m + 1) * (m + 2)) + (m + 1).choose 2))) * hinv
  have hsum : HasSum (fun n : ℕ => q ^ (n * n) * baileyChainAlpha 1 q δ u n)
      (qPochhammerInfIn (q ^ (u + 2)) (q ^ (2 * (t + u) + 3)) *
        qPochhammerInfIn (q ^ (2 * (t + u) + 3) / q ^ (u + 2)) (q ^ (2 * (t + u) + 3)) *
        qPochhammerInfIn (q ^ (2 * (t + u) + 3)) (q ^ (2 * (t + u) + 3))) := by
    have h := hJ.sub (hasSum_ite_eq 0 (1 : 𝕜))
    rw [hF0, add_sub_cancel_right] at h
    exact h.congr_fun hterm
  rw [hsum.tsum_eq, show q ^ (2 * (t + u) + 3) / q ^ (u + 2) = q ^ (2 * t + u + 1) by
    rw [div_eq_iff hz, ← pow_add]; congr 1; omega] at hmain
  rw [div_eq_inv_mul]
  exact hmain

end Fabius

import FabiusFunction.BaileyUnitPairs
import FabiusFunction.BaileyLimitInfinite
import Mathlib.Tactic.Linarith

/-!
# The Rogers–Ramanujan identities

For `‖q‖ < 1` in a complete normed field,

  `∑_{n ≥ 0} q^{n²}/(q;q)_n = 1/((q;q⁵)_∞ (q⁴;q⁵)_∞)`   (`hasSum_rogersRamanujan_first`),
  `∑_{n ≥ 0} q^{n(n+1)}/(q;q)_n = 1/((q²;q⁵)_∞ (q³;q⁵)_∞)`   (`hasSum_rogersRamanujan_second`).

The proof is the Bailey-pair proof of the monograph: one step of the finite limiting Bailey lemma
applied to the unit pair relative to `a = 1` (respectively `a = q`) produces the pair
`(a^n q^{n²} α_n, 1/(q;q)_n)`; the infinite limiting lemma turns it into
`∑ a^n q^{n²}/(q;q)_n = (aq;q)_∞⁻¹ ∑ a^n q^{n²} · a^n q^{n²} α_n`, and the right side is a
bilateral theta series, evaluated by Jacobi's triple product with base `q⁵` and `z = q²`
(respectively `z = q⁴`); the fivefold dissection of `(q;q)_∞` finishes.
-/

set_option autoImplicit false

open Filter Topology Finset

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- The fivefold dissection `(q;q)_∞ = (q;q⁵)_∞ (q²;q⁵)_∞ (q³;q⁵)_∞ (q⁴;q⁵)_∞ (q⁵;q⁵)_∞`. -/
theorem qPochhammerInfIn_self_dissection_five {q : 𝕜} (hq : ‖q‖ < 1) :
    qPochhammerInfIn q q = qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 2) (q ^ 5) *
      qPochhammerInfIn (q ^ 3) (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5) *
      qPochhammerInfIn (q ^ 5) (q ^ 5) := by
  have h := qPochhammerInfIn_dissection q hq (r := 5) (by norm_num)
  simp only [prod_range_succ, prod_range_zero, one_mul] at h
  rw [h, show q * q ^ 0 = q by ring, show q * q ^ 1 = q ^ 2 by ring, show q * q ^ 2 = q ^ 3 by ring,
    show q * q ^ 3 = q ^ 4 by ring, show q * q ^ 4 = q ^ 5 by ring]

omit [CompleteSpace 𝕜] in
/-- If `‖q‖ < 1`, then the fifth power also has norm less than one. -/
theorem norm_pow_five_lt_one {q : 𝕜} (hq : ‖q‖ < 1) : ‖q ^ 5‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg q) hq (by norm_num)

/-- For `k ≥ 1` and `‖q‖ < 1`, the infinite product `(q^k;q^5)_∞` is nonzero. -/
theorem qPochhammerInfIn_pow_pow_five_ne_zero {q : 𝕜} (hq : ‖q‖ < 1) {k : ℕ} (hk : 1 ≤ k) :
    qPochhammerInfIn (q ^ k) (q ^ 5) ≠ 0 :=
  qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_five_lt_one hq)
    (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq (by omega))

omit [CompleteSpace 𝕜] in
/-- The transformed `β` of a unit pair is `1/(q;q)_n`. -/
theorem sum_unitBaileyBeta_transformed (a q : 𝕜) (n : ℕ) :
    ∑ j ∈ range (n + 1), a ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
      unitBaileyBeta j = (finiteQPochhammerIn q q n)⁻¹ := by
  rw [sum_eq_single_of_mem 0 (mem_range.mpr (Nat.succ_pos n)) (fun j _ hj => by
    simp [unitBaileyBeta, hj])]
  simp [unitBaileyBeta]

omit [CompleteSpace 𝕜] in
/-- The transformed `β` of the unit pair relative to `a = 1`, simp-normalised. -/
theorem sum_unitBaileyBeta_transformed_one (q : 𝕜) (n : ℕ) :
    ∑ j ∈ range (n + 1), q ^ (j * j) / finiteQPochhammerIn q q (n - j) *
      unitBaileyBeta j = (finiteQPochhammerIn q q n)⁻¹ := by
  rw [sum_eq_single_of_mem 0 (mem_range.mpr (Nat.succ_pos n)) (fun j _ hj => by
    simp [unitBaileyBeta, hj])]
  simp [unitBaileyBeta]

/-- **The first Rogers–Ramanujan identity** (thm:rogers-ramanujan, eq:RR1). -/
theorem hasSum_rogersRamanujan_first {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ (n * n) / finiteQPochhammerIn q q n)
      ((qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have h : HasSum (fun n : ℕ => (0 : 𝕜) ^ (n * n) / finiteQPochhammerIn 0 0 n)
        ((0 : 𝕜) ^ (0 * 0) / finiteQPochhammerIn 0 0 0) :=
      hasSum_single 0 fun n hn => by rw [zero_pow (mul_ne_zero hn hn), zero_div]
    simpa [finiteQPochhammerIn, qPochhammerInfIn] using h
  have hq' : ∀ n, finiteQPochhammerIn q q n ≠ 0 := finiteQPochhammerIn_self_ne_zero hq
  have hQ : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  have hq1 : ∀ n, finiteQPochhammerIn (1 * q) q n ≠ 0 := fun n => by
    rw [one_mul]
    exact hq' n
  have P1 := (isBaileyPair_unit_one hq').limit_step hq' hq1
  set C₁ : ℝ := qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ with hC₁def
  have hC : ∀ n, ‖finiteQPochhammerIn q q n‖⁻¹ ≤ C₁ := fun n =>
    inv_norm_finiteQPochhammerIn_le q hq hQ n
  have hC0 : 0 ≤ C₁ := (inv_nonneg.mpr (norm_nonneg _)).trans (hC 0)
  have hgeom := summable_geometric_of_lt_one (norm_nonneg q) hq
  have hqn : ∀ n : ℕ, ‖q‖ ^ (n * n) ≤ ‖q‖ ^ n := fun n =>
    pow_le_pow_of_le_one (norm_nonneg q) hq.le (Nat.le_mul_self n)
  have hα1 : ∀ n, ‖unitBaileyAlphaOne q n‖ ≤ 2 := by
    intro n
    unfold unitBaileyAlphaOne
    split_ifs
    · rw [norm_one]
      norm_num
    · rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
      have h1 : ‖q‖ ^ n.choose 2 ≤ 1 := pow_le_one₀ (norm_nonneg q) hq.le
      have h2 : ‖1 + q ^ n‖ ≤ 2 := by
        calc ‖1 + q ^ n‖ ≤ ‖(1 : 𝕜)‖ + ‖q ^ n‖ := norm_add_le _ _
          _ ≤ 1 + 1 := by
            rw [norm_one, norm_pow]
            exact add_le_add le_rfl (pow_le_one₀ (norm_nonneg q) hq.le)
          _ = 2 := by norm_num
      calc ‖q‖ ^ n.choose 2 * ‖1 + q ^ n‖ ≤ 1 * 2 :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = 2 := by norm_num
  have hα : Summable fun n : ℕ =>
      ‖(1 : 𝕜) ^ n * q ^ (n * n) * ((1 : 𝕜) ^ n * q ^ (n * n) * unitBaileyAlphaOne q n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeom.mul_left 2)
    simp only [one_pow, one_mul]
    rw [norm_mul, norm_mul, norm_pow]
    calc ‖q‖ ^ (n * n) * (‖q‖ ^ (n * n) * ‖unitBaileyAlphaOne q n‖) ≤ ‖q‖ ^ n * (1 * 2) :=
          mul_le_mul (hqn n)
            (mul_le_mul (pow_le_one₀ (norm_nonneg q) hq.le) (hα1 n) (norm_nonneg _) zero_le_one)
            (by positivity) (by positivity)
      _ = 2 * ‖q‖ ^ n := by ring
  have hβ : Summable fun n : ℕ =>
      ‖(1 : 𝕜) ^ n * q ^ (n * n) * (∑ j ∈ range (n + 1),
        (1 : 𝕜) ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * unitBaileyBeta j)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeom.mul_left C₁)
    rw [sum_unitBaileyBeta_transformed, one_pow, one_mul, norm_mul, norm_inv, norm_pow]
    calc ‖q‖ ^ (n * n) * ‖finiteQPochhammerIn q q n‖⁻¹ ≤ ‖q‖ ^ n * C₁ :=
          mul_le_mul (hqn n) (hC n) (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
      _ = C₁ * ‖q‖ ^ n := mul_comm _ _
  have hmain := IsBaileyPair.hasSum_limit hq (by rw [one_mul]; exact hQ) P1 hα hβ
  simp only [one_pow, one_mul] at hmain
  -- the theta series, by Jacobi's triple product with base `q⁵` and `z = q²`
  have hz : (q ^ 2 : 𝕜) ≠ 0 := pow_ne_zero 2 hq0
  have hJ := (hasSum_jacobi_triple_product (norm_pow_five_lt_one hq) hz).nat_add_neg
  have hF0 : (-1 : 𝕜) ^ (0 : ℤ) * (q ^ 5) ^ thetaExponent 0 * (q ^ 2) ^ (0 : ℤ) = 1 := by
    simp [thetaExponent]
  have hterm : ∀ n : ℕ, q ^ (n * n) * (q ^ (n * n) * unitBaileyAlphaOne q n) =
      ((-1 : 𝕜) ^ (n : ℤ) * (q ^ 5) ^ thetaExponent (n : ℤ) * (q ^ 2) ^ (n : ℤ) +
        (-1 : 𝕜) ^ (-(n : ℤ)) * (q ^ 5) ^ thetaExponent (-(n : ℤ)) * (q ^ 2) ^ (-(n : ℤ))) -
        (if n = 0 then 1 else 0) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [unitBaileyAlphaOne, thetaExponent]
    · rw [if_neg hn.ne', sub_zero]
      simp only [zpow_neg, zpow_natCast, thetaExponent_natCast, thetaExponent_neg_natCast]
      unfold unitBaileyAlphaOne
      rw [if_neg hn.ne']
      have h1 : ((-1 : 𝕜) ^ n)⁻¹ = (-1) ^ n := by
        rw [← inv_pow, inv_neg, inv_one]
      rw [h1]
      simp only [← pow_mul]
      have hE1 : q ^ (5 * n.choose 2) * q ^ (2 * n) = q ^ (n * n) * q ^ (n * n) * q ^ n.choose 2 := by
        rw [← pow_add, ← pow_add, ← pow_add]
        congr 1
        nlinarith [two_mul_choose_two_add n]
      have hE2 : q ^ (5 * (n + 1).choose 2) =
          q ^ (n * n) * q ^ (n * n) * q ^ n.choose 2 * q ^ n * q ^ (2 * n) := by
        rw [← pow_add, ← pow_add, ← pow_add, ← pow_add]
        congr 1
        nlinarith [two_mul_choose_two_add n, two_mul_choose_two_add (n + 1)]
      have hinv : q ^ (2 * n) * (q ^ (2 * n))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq0)
      linear_combination (-((-1 : 𝕜) ^ n)) * hE1 + (-((-1 : 𝕜) ^ n * (q ^ (2 * n))⁻¹)) * hE2 +
        (-((-1 : 𝕜) ^ n * q ^ (n * n) * q ^ (n * n) * q ^ n.choose 2 * q ^ n)) * hinv
  have hsum : HasSum (fun n : ℕ => q ^ (n * n) * (q ^ (n * n) * unitBaileyAlphaOne q n))
      (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 5 / q ^ 2) (q ^ 5) *
        qPochhammerInfIn (q ^ 5) (q ^ 5)) := by
    have h := hJ.sub (hasSum_ite_eq 0 (1 : 𝕜))
    rw [hF0, add_sub_cancel_right] at h
    exact h.congr_fun hterm
  rw [hsum.tsum_eq] at hmain
  have hval : (qPochhammerInfIn q q)⁻¹ *
      (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 5 / q ^ 2) (q ^ 5) *
        qPochhammerInfIn (q ^ 5) (q ^ 5)) =
      (qPochhammerInfIn q (q ^ 5) * qPochhammerInfIn (q ^ 4) (q ^ 5))⁻¹ := by
    rw [show q ^ 5 / q ^ 2 = q ^ 3 by rw [div_eq_iff hz]; ring,
      qPochhammerInfIn_self_dissection_five hq]
    have h1 := qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_five_lt_one hq) hq
    have h2 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 2) (by norm_num)
    have h3 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 3) (by norm_num)
    have h4 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 4) (by norm_num)
    have h5 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 5) (by norm_num)
    field_simp
  rw [hval] at hmain
  exact hmain.congr_fun fun n => by rw [sum_unitBaileyBeta_transformed_one, div_eq_mul_inv]

/-- **The second Rogers–Ramanujan identity** (thm:rogers-ramanujan, eq:RR2). -/
theorem hasSum_rogersRamanujan_second {q : 𝕜} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => q ^ (n * (n + 1)) / finiteQPochhammerIn q q n)
      ((qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹) := by
  rcases eq_or_ne q 0 with rfl | hq0
  · have h : HasSum (fun n : ℕ => (0 : 𝕜) ^ (n * (n + 1)) / finiteQPochhammerIn 0 0 n)
        ((0 : 𝕜) ^ (0 * (0 + 1)) / finiteQPochhammerIn 0 0 0) :=
      hasSum_single 0 fun n hn => by rw [zero_pow (mul_ne_zero hn n.succ_ne_zero), zero_div]
    simpa [finiteQPochhammerIn, qPochhammerInfIn] using h
  have hq' : ∀ n, finiteQPochhammerIn q q n ≠ 0 := finiteQPochhammerIn_self_ne_zero hq
  have hQ : qPochhammerInfIn q q ≠ 0 := qPochhammerInfIn_self_ne_zero hq
  have hqq : ‖q * q‖ < 1 := by
    rw [norm_mul]
    calc ‖q‖ * ‖q‖ ≤ 1 * ‖q‖ := mul_le_mul_of_nonneg_right hq.le (norm_nonneg q)
      _ < 1 := by rw [one_mul]; exact hq
  have hQQ : qPochhammerInfIn (q * q) q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hqq
  have hq2 : ∀ n, finiteQPochhammerIn (q * q) q n ≠ 0 :=
    finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero (q * q) hq hQQ
  have P1 := (isBaileyPair_unit_q hq').limit_step hq' hq2
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
  -- `‖q‖^{n²} (2n+1) ≤ 3 ‖q‖^{n}`-type bound: use `n ≤ n²` and `(2n+1) ‖q‖^{n²} ≤ 3 ‖q‖^n`
  -- is false in general; instead bound `‖q‖^{n²}` by `‖q‖^n` and `(2n+1) ‖q‖^n` by geometric decay
  have hgeom' : Summable fun n : ℕ => (2 * (n : ℝ) + 1) * ‖q‖ ^ n := by
    have h1 : Summable fun n : ℕ => (n : ℝ) * ‖q‖ ^ n := by
      simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (r := ‖q‖)
        (by rw [norm_norm]; exact hq)
    have h2 := (h1.mul_left 2).add hgeom
    refine h2.congr fun n => ?_
    ring
  have hα : Summable fun n : ℕ =>
      ‖q ^ n * q ^ (n * n) * (q ^ n * q ^ (n * n) * unitBaileyAlphaQ q n)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hgeom'
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow]
    calc ‖q‖ ^ n * ‖q‖ ^ (n * n) * (‖q‖ ^ n * ‖q‖ ^ (n * n) * ‖unitBaileyAlphaQ q n‖)
        ≤ ‖q‖ ^ n * 1 * (1 * 1 * (2 * n + 1)) := by
          gcongr
          · exact hqle _
          · exact hqle _
          · exact hqle _
          · exact hα1 n
      _ = (2 * (n : ℝ) + 1) * ‖q‖ ^ n := by ring
  have hβ : Summable fun n : ℕ =>
      ‖q ^ n * q ^ (n * n) * (∑ j ∈ range (n + 1),
        q ^ j * q ^ (j * j) / finiteQPochhammerIn q q (n - j) * unitBaileyBeta j)‖ := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) (hgeom.mul_left C₁)
    rw [sum_unitBaileyBeta_transformed, norm_mul, norm_mul, norm_inv, norm_pow, norm_pow]
    calc ‖q‖ ^ n * ‖q‖ ^ (n * n) * ‖finiteQPochhammerIn q q n‖⁻¹ ≤ ‖q‖ ^ n * 1 * C₁ := by
          gcongr
          · exact hqle _
          · exact hC n
      _ = C₁ * ‖q‖ ^ n := by ring
  have hmain := IsBaileyPair.hasSum_limit hq hQQ P1 hα hβ
  simp only [sum_unitBaileyBeta_transformed] at hmain
  -- the theta series, by Jacobi's triple product with base `q⁵` and `z = q⁴`
  have hz : (q ^ 4 : 𝕜) ≠ 0 := pow_ne_zero 4 hq0
  have hJ := (hasSum_jacobi_triple_product (norm_pow_five_lt_one hq) hz).nat_add_neg_add_one
  have h1q : (1 : 𝕜) - q ≠ 0 := one_sub_ne_zero_of_norm_lt_one hq
  have hterm : ∀ n : ℕ,
      (1 - q) * (q ^ n * q ^ (n * n) * (q ^ n * q ^ (n * n) * unitBaileyAlphaQ q n)) =
      (-1 : 𝕜) ^ (n : ℤ) * (q ^ 5) ^ thetaExponent (n : ℤ) * (q ^ 4) ^ (n : ℤ) +
        (-1 : 𝕜) ^ (-((n : ℤ) + 1)) * (q ^ 5) ^ thetaExponent (-((n : ℤ) + 1)) *
          (q ^ 4) ^ (-((n : ℤ) + 1)) := by
    intro n
    have hcast : -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hcast]
    simp only [zpow_neg, zpow_natCast, thetaExponent_natCast, thetaExponent_neg_natCast]
    unfold unitBaileyAlphaQ
    have h1 : ((-1 : 𝕜) ^ (n + 1))⁻¹ = -(-1) ^ n := by
      rw [← inv_pow, inv_neg, inv_one, pow_succ]
      ring
    rw [h1]
    simp only [← pow_mul]
    have hE1 : q ^ (5 * n.choose 2) * q ^ (4 * n) =
        q ^ n * q ^ (n * n) * q ^ n * q ^ (n * n) * q ^ n.choose 2 := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      nlinarith [two_mul_choose_two_add n]
    have hE2 : q ^ (5 * (n + 1 + 1).choose 2) =
        q ^ n * q ^ (n * n) * q ^ n * q ^ (n * n) * q ^ n.choose 2 * q ^ (2 * n + 1) *
          q ^ (4 * (n + 1)) := by
      rw [← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      nlinarith [two_mul_choose_two_add n, two_mul_choose_two_add (n + 1 + 1)]
    have hinv : q ^ (4 * (n + 1)) * (q ^ (4 * (n + 1)))⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hq0)
    have hqI : (1 - q) * qInt q (2 * n + 1) = 1 - q ^ (2 * n + 1) := one_sub_mul_qInt q _
    linear_combination
      (q ^ n * q ^ (n * n) * (q ^ n * q ^ (n * n)) * ((-1 : 𝕜) ^ n * q ^ n.choose 2)) * hqI +
      (-((-1 : 𝕜) ^ n)) * hE1 +
      ((-1 : 𝕜) ^ n * (q ^ (4 * (n + 1)))⁻¹) * hE2 +
      ((-1 : 𝕜) ^ n * q ^ n * q ^ (n * n) * q ^ n * q ^ (n * n) * q ^ n.choose 2 *
        q ^ (2 * n + 1)) * hinv
  have hsum : HasSum (fun n : ℕ => q ^ n * q ^ (n * n) * (q ^ n * q ^ (n * n) * unitBaileyAlphaQ q n))
      ((1 - q)⁻¹ * (qPochhammerInfIn (q ^ 4) (q ^ 5) * qPochhammerInfIn (q ^ 5 / q ^ 4) (q ^ 5) *
        qPochhammerInfIn (q ^ 5) (q ^ 5))) := by
    have h := (hJ.congr_fun hterm).mul_left (1 - q)⁻¹
    refine h.congr_fun fun n => ?_
    field_simp
  rw [hsum.tsum_eq] at hmain
  have hval : (qPochhammerInfIn (q * q) q)⁻¹ * ((1 - q)⁻¹ *
      (qPochhammerInfIn (q ^ 4) (q ^ 5) * qPochhammerInfIn (q ^ 5 / q ^ 4) (q ^ 5) *
        qPochhammerInfIn (q ^ 5) (q ^ 5))) =
      (qPochhammerInfIn (q ^ 2) (q ^ 5) * qPochhammerInfIn (q ^ 3) (q ^ 5))⁻¹ := by
    have hshift : qPochhammerInfIn q q = (1 - q) * qPochhammerInfIn (q * q) q := by
      rw [qPochhammerInfIn_eq_finite_mul_shift q hq 1, finiteQPochhammerIn, prod_range_one, pow_zero,
        mul_one, pow_one]
    rw [show q ^ 5 / q ^ 4 = q by rw [div_eq_iff hz]; ring]
    have hd := qPochhammerInfIn_self_dissection_five hq
    rw [hshift] at hd
    have h1 := qPochhammerInfIn_ne_zero_of_norm_lt_one (norm_pow_five_lt_one hq) hq
    have h2 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 2) (by norm_num)
    have h3 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 3) (by norm_num)
    have h4 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 4) (by norm_num)
    have h5 := qPochhammerInfIn_pow_pow_five_ne_zero hq (k := 5) (by norm_num)
    set A := qPochhammerInfIn (q * q) q with hA
    set P1 := qPochhammerInfIn q (q ^ 5) with hP1
    set P2 := qPochhammerInfIn (q ^ 2) (q ^ 5) with hP2
    set P3 := qPochhammerInfIn (q ^ 3) (q ^ 5) with hP3
    set P4 := qPochhammerInfIn (q ^ 4) (q ^ 5) with hP4
    set P5 := qPochhammerInfIn (q ^ 5) (q ^ 5) with hP5
    have hX : P4 * P1 * P5 ≠ 0 := mul_ne_zero (mul_ne_zero h4 h1) h5
    calc A⁻¹ * ((1 - q)⁻¹ * (P4 * P1 * P5)) = (P4 * P1 * P5) / ((1 - q) * A) := by
          rw [div_eq_mul_inv, mul_inv]
          ring
      _ = (P4 * P1 * P5) / (P1 * P2 * P3 * P4 * P5) := by rw [hd]
      _ = (P2 * P3)⁻¹ := by
          rw [eq_comm, inv_eq_iff_eq_inv, inv_div, eq_div_iff hX]
          ring
  rw [hval] at hmain
  refine hmain.congr_fun fun n => ?_
  rw [div_eq_mul_inv, ← pow_add, show n + n * n = n * (n + 1) by ring]

end Fabius

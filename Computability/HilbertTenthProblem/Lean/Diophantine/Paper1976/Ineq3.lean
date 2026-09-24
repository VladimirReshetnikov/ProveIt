import Diophantine.Paper1976.Ineq
import Diophantine.Paper1976.Lemma23
import Diophantine.Paper1984.Identities
import Mathlib.Tactic

/-!
# JSWW 1976, §3: the elementary estimates (Lemmas 3.1–3.6) and Definition 3.7

> **Lemma 3.1.** For an integer `q ≥ 1` and real `β > 2q`, `(β/(β−1))^q ≤ 1 + 2q/β`.
> **Lemma 3.2.** For `0 < n < M` and `x ≥ 0`, `1 − n/M < (1 − 1/(2M(x+1)))^n`.
> **Lemma 3.3.** If `x > 8·2^n` and `n > k`, then (i) the fractional part of
> `(x+1)^n/x^k` is `< 1/8`, (ii) `⌊(x+1)^n/x^k⌋ ≡ C(n,k) (mod x)`, (iii) `C(n,k) < (x+1)^n/x^k`.
> **Lemma 3.4.** For `k ≥ 1` and `n > 2(k−1)²`, `n^k/C(n,k) ≤ k!(1 + 2(k−1)²/n)`.
> **Lemma 3.5.** For `a ≥ 1`, `a(1 + 1/(10a))^4 < a + 1/2`.
> **Lemma 3.6.** For `a ≥ 1`, `a(1 − 1/(4a))^2 > a − 1/2`.
> **Definition 3.7.** `U(x,y) = (x+2)³(x+4)(y+1)² + 1`; if `U(x,y) = □` then `x^x < y`.
-/

namespace JSWW1976

open Finset

/-- Lemma 3.1. -/
theorem lemma_3_1 {q : ℕ} (hq : 1 ≤ q) {β : ℝ} (hβ : 2 * q < β) :
    (β / (β - 1)) ^ q ≤ 1 + 2 * q / β := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hβ0 : 0 < β := by linarith
  have hβ1 : 0 < β - 1 := by linarith
  have h1 : β / (β - 1) = 1 / (1 - 1 / β) := by
    field_simp
  have hα : 1 / β ≤ 1 := by rw [div_le_one hβ0]; linarith
  have hbern : 1 - q * (1 / β) ≤ (1 - 1 / β) ^ q := lemma_2_7 hα q
  have hpos : (0 : ℝ) < 1 - q * (1 / β) := by
    rw [mul_one_div, sub_pos, div_lt_one hβ0]; linarith
  have hhalf : q * (1 / β) ≤ 1 / 2 := by
    rw [mul_one_div, div_le_iff₀ hβ0]; linarith
  calc (β / (β - 1)) ^ q = 1 / (1 - 1 / β) ^ q := by rw [h1, one_div_pow]
    _ ≤ 1 / (1 - q * (1 / β)) := one_div_le_one_div_of_le hpos hbern
    _ = (1 - q * (1 / β))⁻¹ := one_div _
    _ ≤ 1 + 2 * (q * (1 / β)) := lemma_2_8 (by positivity) hhalf
    _ = 1 + 2 * q / β := by ring

/-- Lemma 3.2. -/
theorem lemma_3_2 {n M : ℕ} (hn : 0 < n) (hnM : n < M) (x : ℝ) (hx : 0 ≤ x) :
    1 - (n : ℝ) / M < (1 - 1 / (2 * M * (x + 1))) ^ n := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnM' : (n : ℝ) < M := by exact_mod_cast hnM
  have hden : (0 : ℝ) < 2 * M * (x + 1) := by positivity
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hα : 1 / (2 * M * (x + 1)) ≤ 1 := by
    rw [div_le_one hden]; nlinarith
  have hbern := lemma_2_7 hα n
  have hlt : (n : ℝ) * (1 / (2 * M * (x + 1))) < n / M := by
    have h1 : 1 / (2 * M * (x + 1)) < 1 / M := one_div_lt_one_div_of_lt hM (by nlinarith)
    calc (n : ℝ) * (1 / (2 * M * (x + 1))) < n * (1 / M) := mul_lt_mul_of_pos_left h1 hn'
      _ = n / M := by ring
  linarith

/-- The Weierstrass product inequality `1 − Σ aᵢ ≤ Π (1 − aᵢ)` for `0 ≤ aᵢ ≤ 1`. -/
theorem one_sub_sum_le_prod_one_sub' {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [sum_insert hj, prod_insert hj]
    have ih' := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have hj0 := h0 j (mem_insert_self j s)
    have hj1 := h1 j (mem_insert_self j s)
    have hprod : ∏ i ∈ s, (1 - a i) ≤ 1 :=
      prod_le_one (fun i hi => by linarith [h1 i (mem_insert_of_mem hi)])
        (fun i hi => by linarith [h0 i (mem_insert_of_mem hi)])
    nlinarith

/-- Lemma 3.5. -/
theorem lemma_3_5 {a : ℝ} (ha : 1 ≤ a) : a * (1 + 1 / (10 * a)) ^ 4 < a + 1 / 2 := by
  have ha0 : 0 < a := by linarith
  have hu : 1 / (10 * a) ≤ 1 / 10 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hu0 : 0 < 1 / (10 * a) := by positivity
  set u := 1 / (10 * a) with hu_def
  have hau : a * u = 1 / 10 := by rw [hu_def]; field_simp
  have : a * (1 + u) ^ 4 = a + a * (4 * u + 6 * u ^ 2 + 4 * u ^ 3 + u ^ 4) := by ring
  rw [this]
  have : a * (4 * u + 6 * u ^ 2 + 4 * u ^ 3 + u ^ 4) = (a * u) * (4 + 6 * u + 4 * u ^ 2 + u ^ 3) := by ring
  rw [this, hau]
  nlinarith

/-- Lemma 3.6. -/
theorem lemma_3_6 {a : ℝ} (ha : 1 ≤ a) : a - 1 / 2 < a * (1 - 1 / (4 * a)) ^ 2 := by
  have ha0 : 0 < a := by linarith
  have : a * (1 - 1 / (4 * a)) ^ 2 = a - 1 / 2 + 1 / (16 * a) := by
    field_simp; ring
  rw [this]
  have : 0 < 1 / (16 * a) := by positivity
  linarith

/-- Definition 3.7. -/
def U (x y : ℕ) : ℕ := (x + 2) ^ 3 * (x + 4) * (y + 1) ^ 2 + 1

/-- If `U(x,y) = □` then `x^x < y` (from Lemma 2.3 with `e = x + 2`). -/
theorem lt_of_U_square {x y : ℕ} (h : IsSquare (U x y)) : x ^ x < y := by
  obtain ⟨z, hz⟩ := h
  have := lemma_2_3 (e := x + 2) (n := y) (x := z) (by omega)
    (by rw [show x + 2 + 2 = x + 4 by ring]; exact hz)
  have h2 : x ^ x ≤ (x + 2) ^ (x + 2 - 2) := by
    rw [Nat.add_sub_cancel]; exact Nat.pow_le_pow_left (by omega) x
  omega

/-- For every `x`, arbitrarily large `y` with `U(x,y) = □` exist (Lemma 2.3, converse). -/
theorem exists_U_square (x t : ℕ) : ∃ y, t ≤ y ∧ IsSquare (U x y) := by
  obtain ⟨n, z, hz, hdvd⟩ := lemma_2_3_converse (e := x + 2) (t := t + 1) (by omega) (by omega)
  refine ⟨n, ?_, ⟨z, ?_⟩⟩
  · have := Nat.le_of_dvd (by omega) hdvd; omega
  · unfold U; rw [show x + 4 = x + 2 + 2 by ring]; exact hz

/-- The binomial expansion split at `k` (`k < n`, `1 ≤ x`):
`(x+1)^n = w x^(k+1) + C(n,k) x^k + v` with `w ≥ 1` and `v·x ≤ 2^n x^k`. -/
theorem binomial_split {n k x : ℕ} (hk : k < n) (hx : 1 ≤ x) :
    ∃ w v, (x + 1) ^ n = w * x ^ (k + 1) + n.choose k * x ^ k + v ∧ v * x ≤ 2 ^ n * x ^ k ∧
      1 ≤ w := by
  have h := add_pow x 1 n
  simp only [one_pow, mul_one, Nat.cast_id] at h
  have hsplit : ∑ m ∈ range (n + 1), x ^ m * n.choose m =
      ∑ m ∈ range k, x ^ m * n.choose m + x ^ k * n.choose k
        + ∑ m ∈ Ico (k + 1) (n + 1), x ^ m * n.choose m := by
    rw [Finset.range_eq_Ico, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le k) (by omega : k ≤ n + 1),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : k < n + 1)]
    ring
  have hdvd : x ^ (k + 1) ∣ ∑ m ∈ Ico (k + 1) (n + 1), x ^ m * n.choose m := by
    apply Finset.dvd_sum
    intro m hm
    simp only [Finset.mem_Ico] at hm
    exact Dvd.dvd.mul_right (pow_dvd_pow x hm.1) _
  obtain ⟨w, hw⟩ := hdvd
  refine ⟨w, ∑ m ∈ range k, x ^ m * n.choose m, ?_, ?_, ?_⟩
  · rw [h, hsplit, hw]; ring
  · -- Σ_{m<k} C(n,m) x^m ≤ 2^n x^(k-1)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hle : ∑ m ∈ range k, x ^ m * n.choose m ≤ x ^ (k - 1) * 2 ^ n :=
      calc ∑ m ∈ range k, x ^ m * n.choose m
          ≤ ∑ m ∈ range k, x ^ (k - 1) * n.choose m := by
            apply Finset.sum_le_sum
            intro m hm
            simp only [Finset.mem_range] at hm
            have hmk : m ≤ k - 1 := by omega
            exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hx hmk)
        _ = x ^ (k - 1) * ∑ m ∈ range k, n.choose m := by rw [Finset.mul_sum]
        _ ≤ x ^ (k - 1) * ∑ m ∈ range (n + 1), n.choose m := by
            apply Nat.mul_le_mul_left
            exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega : k ≤ n + 1))
              (fun _ _ _ => Nat.zero_le _)
        _ = x ^ (k - 1) * 2 ^ n := by rw [Nat.sum_range_choose]
    calc (∑ m ∈ range k, x ^ m * n.choose m) * x ≤ x ^ (k - 1) * 2 ^ n * x :=
          Nat.mul_le_mul_right _ hle
      _ = 2 ^ n * x ^ k := by
          rw [mul_comm (x ^ (k - 1)), mul_assoc, ← pow_succ, Nat.sub_add_cancel hk0]
  · -- the top term C(n,n) x^n = x^n ≥ x^(k+1) is part of w x^(k+1)
    have htop : x ^ n * n.choose n ≤ ∑ m ∈ Ico (k + 1) (n + 1), x ^ m * n.choose m :=
      Finset.single_le_sum (f := fun m => x ^ m * n.choose m) (fun _ _ => Nat.zero_le _)
        (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
    rw [Nat.choose_self, mul_one, hw] at htop
    have hpow : x ^ (k + 1) ≤ x ^ n := Nat.pow_le_pow_right hx (by omega)
    have hpos : 0 < x ^ (k + 1) := by positivity
    by_contra hw0
    push_neg at hw0
    have : w = 0 := by omega
    subst this
    simp at htop
    omega

/-- Lemma 3.3, packaged: for `k < n` and `x > 8·2^n`, `⌊(x+1)^n/x^k⌋ = C(n,k) + w x` with
`w ≥ 1` (so (ii) and (iii) hold), and the fractional part is `< 1/8` (i). -/
theorem lemma_3_3 {n k x : ℕ} (hk : k < n) (hx : 8 * 2 ^ n < x) :
    ∃ w : ℕ, 1 ≤ w ∧
      ⌊((x : ℝ) + 1) ^ n / (x : ℝ) ^ k⌋ = ((n.choose k + w * x : ℕ) : ℤ) ∧
      ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k - ((n.choose k + w * x : ℕ) : ℝ) < 1 / 8 := by
  have hx1 : 1 ≤ x := by omega
  obtain ⟨w, v, hsplit, hv, hw⟩ := binomial_split hk hx1
  refine ⟨w, hw, ?_, ?_⟩
  all_goals
    have hxR : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hxk : (0 : ℝ) < (x : ℝ) ^ k := by positivity
    have hsplitR : ((x : ℝ) + 1) ^ n = ((n.choose k + w * x : ℕ) : ℝ) * (x : ℝ) ^ k + v := by
      have := congrArg (fun m : ℕ => (m : ℝ)) hsplit
      push_cast at this ⊢
      rw [this]; ring
    have hvR : (v : ℝ) * x ≤ 2 ^ n * (x : ℝ) ^ k := by exact_mod_cast hv
    have h8 : (8 : ℝ) * 2 ^ n < x := by exact_mod_cast hx
    -- v / x^k < 1/8
    have hfrac : (v : ℝ) / (x : ℝ) ^ k < 1 / 8 := by
      rw [div_lt_iff₀ hxk]
      have : (v : ℝ) * x * 8 ≤ 2 ^ n * (x : ℝ) ^ k * 8 := by linarith
      nlinarith
    have hratio : ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k = ((n.choose k + w * x : ℕ) : ℝ) + v / (x : ℝ) ^ k := by
      rw [hsplitR]; field_simp
  · rw [hratio]
    have hv0 : (0 : ℝ) ≤ v / (x : ℝ) ^ k := by positivity
    rw [Int.floor_eq_iff]
    push_cast
    constructor <;> linarith
  · rw [hratio]
    linarith

/-- Lemma 3.4. -/
theorem lemma_3_4 {k n : ℕ} (hk : 1 ≤ k) (hn : 2 * (k - 1) ^ 2 < n) :
    (n : ℝ) ^ k / (n.choose k : ℝ) ≤ (k.factorial : ℝ) * (1 + 2 * ((k : ℝ) - 1) ^ 2 / n) := by
  have hkn : k ≤ n := by
    have h1 : k - 1 ≤ (k - 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : 2 * ((k : ℝ) - 1) ^ 2 < n := by
    have h' : ((2 * (k - 1) ^ 2 : ℕ) : ℝ) < n := by exact_mod_cast hn
    push_cast [Nat.cast_sub hk] at h'
    linarith
  -- k(k-1) ≤ 2(k-1)²  (k = 1 or k ≥ 2)
  have hkk2 : (k : ℝ) * (k - 1) ≤ 2 * ((k : ℝ) - 1) ^ 2 := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · norm_num
    · have : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      nlinarith
  set P : ℝ := ∏ i ∈ range k, (1 - (i : ℝ) / n) with hP
  -- k! C(n,k) = ∏ (n - i)
  have hdesc : (k.factorial : ℝ) * n.choose k = ∏ i ∈ range k, ((n : ℝ) - i) := by
    have h1 := Nat.descFactorial_eq_factorial_mul_choose n k
    have h2 := Nat.descFactorial_eq_prod_range n k
    rw [h2] at h1
    have := congrArg (fun m : ℕ => (m : ℝ)) h1
    push_cast at this
    rw [← this]
    apply Finset.prod_congr rfl
    intro i hi
    have : i ≤ n := by have := Finset.mem_range.1 hi; omega
    push_cast [Nat.cast_sub this]
    ring
  -- ∏ (n - i) = n^k P
  have hprod : ∏ i ∈ range k, ((n : ℝ) - i) = (n : ℝ) ^ k * P := by
    calc ∏ i ∈ range k, ((n : ℝ) - i) = ∏ i ∈ range k, ((n : ℝ) * (1 - (i : ℝ) / n)) := by
          apply Finset.prod_congr rfl
          intro i _
          field_simp
      _ = (∏ _i ∈ range k, (n : ℝ)) * ∏ i ∈ range k, (1 - (i : ℝ) / n) := Finset.prod_mul_distrib
      _ = (n : ℝ) ^ k * P := by rw [Finset.prod_const, Finset.card_range]
  -- Weierstrass: P ≥ 1 - Σ i/n = 1 - t
  have hW : 1 - ∑ i ∈ range k, (i : ℝ) / n ≤ P :=
    one_sub_sum_le_prod_one_sub' _ _ (fun i _ => by positivity)
      (fun i hi => by
        rw [div_le_one hn0]
        exact_mod_cast (show i ≤ n by have := Finset.mem_range.1 hi; omega))
  have hsum : ∑ i ∈ range k, (i : ℝ) / n = (k : ℝ) * (k - 1) / (2 * n) := by
    rw [← Finset.sum_div]
    have h := Finset.sum_range_id_mul_two k
    have hcast : (∑ i ∈ range k, (i : ℝ)) = ((∑ i ∈ range k, i : ℕ) : ℝ) := by push_cast; rfl
    have h' : ((∑ i ∈ range k, i : ℕ) : ℝ) * 2 = k * (k - 1) := by
      have := congrArg (fun m : ℕ => (m : ℝ)) h
      push_cast [Nat.cast_sub hk] at this
      linarith
    rw [hcast]
    field_simp
    linarith
  set t : ℝ := (k : ℝ) * (k - 1) / (2 * n) with ht
  have ht0 : 0 ≤ t := by
    rw [ht]; apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  have ht12 : t ≤ 1 / 2 := by
    rw [ht, div_le_iff₀ (by positivity)]
    nlinarith
  have hP_ge : 1 - t ≤ P := by rw [← hsum]; exact hW
  have hP_pos : 0 < P := by linarith
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hnk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  have hC : (n.choose k : ℝ) = (n : ℝ) ^ k * P / k.factorial := by
    rw [eq_div_iff hfac.ne', mul_comm, hdesc, hprod]
  have hratio : (n : ℝ) ^ k / (n.choose k : ℝ) = k.factorial / P := by
    rw [hC]; field_simp
  rw [hratio]
  have h2t : 2 * t = (k : ℝ) * (k - 1) / n := by rw [ht]; field_simp
  calc (k.factorial : ℝ) / P ≤ k.factorial / (1 - t) :=
        div_le_div_of_nonneg_left hfac.le (by linarith) hP_ge
    _ = k.factorial * (1 - t)⁻¹ := div_eq_mul_inv _ _
    _ ≤ k.factorial * (1 + 2 * t) := mul_le_mul_of_nonneg_left (lemma_2_8 ht0 ht12) hfac.le
    _ ≤ k.factorial * (1 + 2 * ((k : ℝ) - 1) ^ 2 / n) := by
        apply mul_le_mul_of_nonneg_left _ hfac.le
        rw [h2t]
        have := div_le_div_of_nonneg_right hkk2 hn0.le
        linarith

end JSWW1976

import IntegerPoints.Lemma9Core
import IntegerPoints.BombieriIwaniec

/-!
# Zhai–Cao, Lemma 9: the sum over close pairs

After the Cauchy–Schwarz step we have to bound
`∑_{(p₁,p₂) : |λ| ≤ w} ‖∑_{u ∼ U} e(√x λ/u)‖`, `w = 2√N/(VQ)`.  With `δ = U/√x`:

* `|λ| ≤ δ`: the trivial bound `2U`, for `≤ C₆(NV log 2NV + 4δV N²V²/√N)` pairs;
* `δ < |λ| ≤ w`: Lemma 1 gives `≪ U²/(√x|λ|) + x^{1/4}|λ|^{1/2}U^{-1/2}`; the first
  term is summed over dyadic shells `2^j δ ≤ |λ| < 2^{j+1} δ`, `j ≤ J`, each shell
  contributing `≤ (U/2^j) · #{|λ| ≤ 2^{j+1}δ}`; the second is `≤ x^{1/4} w^{1/2} U^{-1/2}`
  times the number of close pairs.

Under `U V² √N ≤ √x` the `δ`-terms of the counts are `≤ NV`, and we obtain
`‖S‖² ≤ K (J+1) log(2NV) (U² Q N V + x^{1/4} U^{1/2} N^{9/4} V^{3/2} Q^{-1/2})`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace L9

theorem card_dyadic_le {U : ℝ} (hU : 0 ≤ U) : ((dyadic U).card : ℝ) ≤ 2 * U := by
  rw [dyadic, intRange, Nat.card_Ioc]
  calc (((⌊2 * U⌋₊ - ⌊U⌋₊ : ℕ) : ℝ)) ≤ (⌊2 * U⌋₊ : ℝ) := by exact_mod_cast Nat.sub_le _ _
    _ ≤ 2 * U := Nat.floor_le (by linarith)

/-- The trivial bound for the inner sum. -/
theorem inner_sum_trivial {x U : ℝ} (hU : 0 ≤ U) (lam : ℝ) :
    ‖∑ u ∈ dyadic U, e (Real.sqrt x * lam / u)‖ ≤ 2 * U := by
  calc ‖∑ u ∈ dyadic U, e (Real.sqrt x * lam / u)‖
      ≤ ∑ u ∈ dyadic U, ‖e (Real.sqrt x * lam / u)‖ := norm_sum_le _ _
    _ = (dyadic U).card := by simp [norm_e]
    _ ≤ 2 * U := card_dyadic_le hU

/-- The pointwise bound on `g(p) = ‖∑_u e(√x λ/u)‖` for `|λ| ≤ w`. -/
theorem g_bound {C1 x U w : ℝ} (hC1 : 0 ≤ C1) (hU : 1 ≤ U) (hx : 0 < x) (hw : 0 < w)
    (hin : ∀ lam : ℝ, lam ≠ 0 → ‖∑ u ∈ dyadic U, e (Real.sqrt x * lam / u)‖ ≤
      C1 * (U ^ 2 / (Real.sqrt x * |lam|) +
        x ^ ((1 : ℝ) / 4) * |lam| ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)))
    (lam : ℝ) (hlam : |lam| ≤ w) :
    ‖∑ u ∈ dyadic U, e (Real.sqrt x * lam / u)‖ ≤
      (if |lam| ≤ U / Real.sqrt x then 2 * U else C1 * (U ^ 2 / (Real.sqrt x * |lam|))) +
        C1 * (x ^ ((1 : ℝ) / 4) * w ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)) := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hU0 : 0 < U := by linarith
  have hT : 0 ≤ C1 * (x ^ ((1 : ℝ) / 4) * w ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)) := by positivity
  split_ifs with h
  · linarith [inner_sum_trivial hU0.le (x := x) lam]
  · push Not at h
    have hlam0 : lam ≠ 0 := by
      intro h0
      rw [h0, abs_zero] at h
      have : 0 < U / Real.sqrt x := by positivity
      linarith
    have h1 : |lam| ^ ((1 : ℝ) / 2) ≤ w ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow (abs_nonneg _) hlam (by norm_num)
    calc _ ≤ C1 * (U ^ 2 / (Real.sqrt x * |lam|) +
          x ^ ((1 : ℝ) / 4) * |lam| ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)) := hin lam hlam0
      _ ≤ C1 * (U ^ 2 / (Real.sqrt x * |lam|) +
          x ^ ((1 : ℝ) / 4) * w ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)) := by
          apply mul_le_mul_of_nonneg_left _ hC1
          have : 0 ≤ x ^ ((1 : ℝ) / 4) * U ^ (-(1 : ℝ) / 2) := by positivity
          nlinarith
      _ = _ := by ring

/-- The shell index of a pair: `⌊log₂ (|λ|/δ)⌋`. -/
noncomputable def shell (δ : ℝ) (p : (ℕ × ℕ) × (ℕ × ℕ)) : ℕ := Nat.log 2 ⌊|lamOf p| / δ⌋₊

theorem shell_bounds {δ : ℝ} (hδ : 0 < δ) {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : δ < |lamOf p|) :
    (2 : ℝ) ^ shell δ p * δ ≤ |lamOf p| ∧ |lamOf p| < 2 ^ (shell δ p + 1) * δ := by
  set m : ℕ := ⌊|lamOf p| / δ⌋₊ with hm
  have hr : 1 < |lamOf p| / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hm1 : 1 ≤ m := by
    rw [hm, Nat.one_le_floor_iff]
    exact hr.le
  have hm0 : m ≠ 0 := by omega
  have h1 : (2 : ℝ) ^ shell δ p ≤ m := by
    have := Nat.pow_log_le_self 2 hm0
    exact_mod_cast this
  have h2 : (m : ℝ) < 2 ^ (shell δ p + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    exact_mod_cast this
  have hfl : (m : ℝ) ≤ |lamOf p| / δ := Nat.floor_le (by positivity)
  have hfl' : |lamOf p| / δ < m + 1 := Nat.lt_floor_add_one _
  constructor
  · calc (2 : ℝ) ^ shell δ p * δ ≤ m * δ := mul_le_mul_of_nonneg_right h1 hδ.le
      _ ≤ |lamOf p| := by rw [← le_div_iff₀ hδ]; exact hfl
  · have hm2 : (m : ℝ) + 1 ≤ 2 ^ (shell δ p + 1) := by
      have : m + 1 ≤ 2 ^ (shell δ p + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
      exact_mod_cast this
    calc |lamOf p| < (m + 1) * δ := by rw [← div_lt_iff₀ hδ]; exact hfl'
      _ ≤ 2 ^ (shell δ p + 1) * δ := mul_le_mul_of_nonneg_right hm2 hδ.le

theorem shell_le {δ w : ℝ} (hδ : 0 < δ) {p : (ℕ × ℕ) × (ℕ × ℕ)} (hp : |lamOf p| ≤ w) :
    shell δ p ≤ Nat.log 2 ⌊w / δ⌋₊ := by
  unfold shell
  apply Nat.log_mono_right
  apply Nat.floor_le_floor
  exact div_le_div_of_nonneg_right hp hδ.le

/-- The sum over close pairs of the `ite`-bound, decomposed into dyadic shells. -/
theorem sum_ite_le {C1 x U V N w : ℝ} (hC1 : 0 ≤ C1) (hU : 1 ≤ U) (hx : 0 < x) (hw : 0 < w) :
    ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ w),
        (if |lamOf p| ≤ U / Real.sqrt x then 2 * U
          else C1 * (U ^ 2 / (Real.sqrt x * |lamOf p|))) ≤
      2 * U * (((pairSet V N).filter (fun p => |lamOf p| ≤ U / Real.sqrt x)).card : ℝ) +
        C1 * ∑ j ∈ Finset.range (Nat.log 2 ⌊w / (U / Real.sqrt x)⌋₊ + 1),
          U / 2 ^ j * (((pairSet V N).filter
            (fun p => |lamOf p| ≤ 2 ^ (j + 1) * (U / Real.sqrt x))).card : ℝ) := by
  classical
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hU0 : 0 < U := by linarith
  set δ : ℝ := U / Real.sqrt x with hδ
  have hδ0 : 0 < δ := by positivity
  set J : ℕ := Nat.log 2 ⌊w / δ⌋₊ with hJ
  rw [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, Finset.filter_filter, Finset.filter_filter]
  -- the first part
  have h1 : ((Finset.filter (fun p => |lamOf p| ≤ w ∧ |lamOf p| ≤ δ) (pairSet V N)).card : ℝ) ≤
      ((pairSet V N).filter (fun p => |lamOf p| ≤ δ)).card := by
    apply Nat.cast_le.2
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.2⟩
  -- the second part, fiberwise over shells
  set S := Finset.filter (fun p => |lamOf p| ≤ w ∧ ¬ |lamOf p| ≤ δ) (pairSet V N) with hS
  have hmaps : ∀ p ∈ S, shell δ p ∈ Finset.range (J + 1) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    rw [Finset.mem_range, Nat.lt_succ_iff, hJ]
    exact shell_le hδ0 hp.2.1
  have h2 : ∑ p ∈ S, C1 * (U ^ 2 / (Real.sqrt x * |lamOf p|)) ≤
      C1 * ∑ j ∈ Finset.range (J + 1),
        U / 2 ^ j * (((pairSet V N).filter (fun p => |lamOf p| ≤ 2 ^ (j + 1) * δ)).card : ℝ) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ hC1
    calc ∑ p ∈ S.filter (fun p => shell δ p = j), U ^ 2 / (Real.sqrt x * |lamOf p|)
        ≤ ∑ p ∈ S.filter (fun p => shell δ p = j), U / 2 ^ j := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Finset.mem_filter, hS, Finset.mem_filter] at hp
          obtain ⟨⟨-, -, hgt⟩, hsh⟩ := hp
          push Not at hgt
          have hb := (shell_bounds hδ0 hgt).1
          rw [hsh] at hb
          have hl0 : 0 < |lamOf p| := lt_trans hδ0 hgt
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          -- U² 2^j ≤ U √x |λ| ⟸ 2^j δ ≤ |λ|, δ = U/√x
          have : U ^ 2 * 2 ^ j = U * Real.sqrt x * (2 ^ j * δ) := by
            rw [hδ]
            first | (field_simp; done) | (field_simp; ring)
          rw [this]
          calc U * Real.sqrt x * (2 ^ j * δ) ≤ U * Real.sqrt x * |lamOf p| :=
                mul_le_mul_of_nonneg_left hb (by positivity)
            _ = U * (Real.sqrt x * |lamOf p|) := by ring
      _ = U / 2 ^ j * ((S.filter (fun p => shell δ p = j)).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ U / 2 ^ j * (((pairSet V N).filter (fun p => |lamOf p| ≤ 2 ^ (j + 1) * δ)).card : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Nat.cast_le.2
          apply Finset.card_le_card
          intro p hp
          rw [Finset.mem_filter, hS, Finset.mem_filter] at hp
          obtain ⟨⟨hP, -, hgt⟩, hsh⟩ := hp
          push Not at hgt
          rw [Finset.mem_filter]
          refine ⟨hP, ?_⟩
          have hb := (shell_bounds hδ0 hgt).2
          rw [hsh] at hb
          exact hb.le
  calc _ ≤ 2 * U * (((pairSet V N).filter (fun p => |lamOf p| ≤ δ)).card : ℝ) +
        ∑ p ∈ S, C1 * (U ^ 2 / (Real.sqrt x * |lamOf p|)) := by
        rw [mul_comm (2 * U)]
        gcongr
  _ ≤ _ := by linarith

/-! ### Assembly -/

/-- `∑_{j < J+1} 1/2^j ≤ 2`. -/
theorem sum_inv_two_pow_le (J : ℕ) : ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j) ≤ 2 := by
  have h : ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j) =
      ∑ j ∈ Finset.range (J + 1), ((1 / 2 : ℝ)) ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_div_pow]
  rw [h, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  have h0 : 0 ≤ ((1 / 2 : ℝ)) ^ (J + 1) := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

set_option maxHeartbeats 1000000 in
/-- **The core estimate.**  For `1 ≤ U, V, N`, `x > 0`, `1 ≤ Q ≤ 2VN` and `U V² √N ≤ √x`:
`‖S‖² ≤ K (J+1) log(2NV) (U² Q N V + x^{1/4} U^{1/2} N^{9/4} V^{3/2} Q^{-1/2})`, where
`J = log₂ ⌊2√N √x/(VQU)⌋` and `K = 4C₆(18 + 18C₁) + 144 C₁C₆`. -/
theorem core_bound {C1 C6 : ℝ} (hC1 : 0 ≤ C1) (hC6 : 0 ≤ C6)
    (hin : ∀ (x U lam : ℝ), 1 ≤ U → 0 < x → lam ≠ 0 →
      ‖∑ u ∈ dyadic U, e (Real.sqrt x * lam / u)‖ ≤
        C1 * (U ^ 2 / (Real.sqrt x * |lam|) +
          x ^ ((1 : ℝ) / 4) * |lam| ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2)))
    (hcount : ∀ M N Δ : ℝ, 1 ≤ M → 1 ≤ N → 0 < Δ →
      (quadrupleCount (1 / 2) 1 M N Δ : ℝ) ≤
        C6 * (M * N * Real.log (2 * M * N) + Δ * M ^ 2 * N ^ 2))
    {x U V N : ℝ} (Q : ℕ) (hU : 1 ≤ U) (hV : 1 ≤ V) (hN : 1 ≤ N) (hx : 0 < x) (hQ : 1 ≤ Q)
    (hQ2 : (Q : ℝ) ≤ 2 * V * N) (hH : U * V ^ 2 * Real.sqrt N ≤ Real.sqrt x)
    (a b c : ℕ → ℂ) (ha : UnitBounded a) (hb : UnitBounded b) (hc : UnitBounded c) :
    ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
      (4 * C6 * (18 + 18 * C1) + 144 * C1 * C6) *
        ((Nat.log 2 ⌊2 * Real.sqrt N / (V * Q) / (U / Real.sqrt x)⌋₊ : ℝ) + 1) *
        Real.log (2 * N * V) *
        (U ^ 2 * Q * N * V +
          x ^ ((1 : ℝ) / 4) * U ^ ((1 : ℝ) / 2) * N ^ ((9 : ℝ) / 4) * V ^ ((3 : ℝ) / 2) *
            (Q : ℝ) ^ (-(1 : ℝ) / 2)) := by
  classical
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hN0 : 0 < N := by linarith
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  set w : ℝ := 2 * Real.sqrt N / (V * Q) with hw
  have hw0 : 0 < w := by positivity
  set δ : ℝ := U / Real.sqrt x with hδ
  have hδ0 : 0 < δ := by positivity
  set J : ℕ := Nat.log 2 ⌊w / δ⌋₊ with hJ
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  set L₀ : ℝ := Real.log (2 * N * V) with hL₀
  have hL₀ : 1 / 2 ≤ L₀ := by
    have := BI.log_two_gt
    have h2 : Real.log 2 ≤ L₀ := Real.log_le_log (by norm_num) (by nlinarith)
    linarith
  have hL₀0 : 0 ≤ L₀ := by linarith
  -- the count function
  set cnt : ℝ → ℝ := fun t => (((pairSet V N).filter (fun p => |lamOf p| ≤ t)).card : ℝ)
    with hcnt
  have hcnt_le : ∀ t, 0 < t →
      cnt t ≤ C6 * (N * V * L₀ + (4 * t * V / Real.sqrt N) * N ^ 2 * V ^ 2) :=
    fun t ht => count_close hN hV ht hcount
  -- `(4δV/√N) N² V² ≤ 4 N V`
  have hA : (4 * δ * V / Real.sqrt N) * N ^ 2 * V ^ 2 ≤ 4 * (N * V) := by
    have hNN : N ^ 2 = N * (Real.sqrt N * Real.sqrt N) := by
      rw [Real.mul_self_sqrt hN0.le]
      ring
    have e : (4 * δ * V / Real.sqrt N) * N ^ 2 * V ^ 2 =
        4 * (N * V) * (U * V ^ 2 * Real.sqrt N / Real.sqrt x) := by
      rw [hδ, hNN]
      first | (field_simp; done) | (field_simp; ring)
    rw [e]
    have : U * V ^ 2 * Real.sqrt N / Real.sqrt x ≤ 1 := by
      rw [div_le_one hsx]
      exact hH
    have h0 : 0 ≤ 4 * (N * V) := by positivity
    nlinarith
  -- Cauchy–Schwarz
  have hCS := cauchy_step (x := x) (U := U) Q hQ hV hN a b c ha hb hc
  rw [← hw] at hCS
  -- the pointwise bound summed
  have hpt : ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ w),
      ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf p / u)‖ ≤
      ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ w),
        ((if |lamOf p| ≤ δ then 2 * U else C1 * (U ^ 2 / (Real.sqrt x * |lamOf p|))) +
          C1 * (x ^ ((1 : ℝ) / 4) * w ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2))) := by
    refine Finset.sum_le_sum fun p hp => ?_
    rw [Finset.mem_filter] at hp
    exact g_bound hC1 hU hx hw0 (fun lam hl => hin x U lam hU hx hl) (lamOf p) hp.2
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hpt
  have hite := sum_ite_le (V := V) (N := N) hC1 hU hx hw0
  rw [← hδ, ← hJ] at hite
  -- bound the shell sum
  have hshell : ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ) ≤
      C6 * (2 * U * (N * V * L₀) + 8 * ((J : ℝ) + 1) * U * (N * V)) := by
    calc ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ)
        ≤ ∑ j ∈ Finset.range (J + 1), U / 2 ^ j *
            (C6 * (N * V * L₀ + (4 * (2 ^ (j + 1) * δ) * V / Real.sqrt N) * N ^ 2 * V ^ 2)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hcnt_le _ (by positivity)) (by positivity)
      _ = ∑ j ∈ Finset.range (J + 1),
            (C6 * U * (N * V * L₀) * (1 / 2 ^ j) +
              C6 * U * (2 * ((4 * δ * V / Real.sqrt N) * N ^ 2 * V ^ 2))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have h2j : (0 : ℝ) < 2 ^ j := by positivity
          rw [pow_succ]
          first | (field_simp; done) | (field_simp; ring)
      _ = C6 * U * (N * V * L₀) * ∑ j ∈ Finset.range (J + 1), (1 / (2 : ℝ) ^ j) +
            ((J : ℝ) + 1) * (C6 * U * (2 * ((4 * δ * V / Real.sqrt N) * N ^ 2 * V ^ 2))) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
            ← Finset.mul_sum]
          push_cast
          ring
      _ ≤ C6 * U * (N * V * L₀) * 2 + ((J : ℝ) + 1) * (C6 * U * (2 * (4 * (N * V)))) := by
          gcongr
          exact sum_inv_two_pow_le J
      _ = _ := by ring
  -- the two other counts
  have hcδ : cnt δ ≤ C6 * (N * V * L₀ + 4 * (N * V)) :=
    (hcnt_le δ hδ0).trans (mul_le_mul_of_nonneg_left (by linarith) hC6)
  have hcw : cnt w ≤ C6 * (N * V * L₀ + 8 * N ^ 2 * V ^ 2 / Q) := by
    refine (hcnt_le w hw0).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hC6)
    rw [hw]
    field_simp
    ring
  -- substitutions: `U = u²`, `V = v²`, `Q = q²`, `N = n₄⁴`, `y = x^{1/4}`
  set u := Real.sqrt U with hu
  set v := Real.sqrt V with hv
  set q := Real.sqrt Q with hq
  set n4 := N ^ ((1 : ℝ) / 4) with hn4
  set y := x ^ ((1 : ℝ) / 4) with hy
  have hu0 : 0 < u := Real.sqrt_pos.2 hU0
  have hv0 : 0 < v := Real.sqrt_pos.2 hV0
  have hq0' : 0 < q := Real.sqrt_pos.2 hQ0
  have hn40 : 0 < n4 := Real.rpow_pos_of_pos hN0 _
  have hy0 : 0 ≤ y := by positivity
  have hUu : U = u ^ 2 := (Real.sq_sqrt hU0.le).symm
  have hVv : V = v ^ 2 := (Real.sq_sqrt hV0.le).symm
  have hQq : (Q : ℝ) = q ^ 2 := (Real.sq_sqrt hQ0.le).symm
  have hNn : N = n4 ^ 4 := by
    rw [hn4, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hU12 : U ^ ((1 : ℝ) / 2) = u := (Real.sqrt_eq_rpow U).symm
  have hUm12 : U ^ (-(1 : ℝ) / 2) = 1 / u := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hU0.le, hU12, one_div]
  have hVm12 : V ^ (-(1 : ℝ) / 2) = 1 / v := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hV0.le, ← Real.sqrt_eq_rpow, one_div]
  have hQm12 : (Q : ℝ) ^ (-(1 : ℝ) / 2) = 1 / q := by
    rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow, one_div]
  have hV32 : V ^ ((3 : ℝ) / 2) = v ^ 3 := by
    rw [hVv, ← Real.rpow_natCast v 2, ← Real.rpow_mul hv0.le]
    norm_num
  have hN94 : N ^ ((9 : ℝ) / 4) = n4 ^ 9 := by
    rw [hNn, ← Real.rpow_natCast n4 4, ← Real.rpow_mul hn40.le]
    norm_num
  have hsqrtN : Real.sqrt N = n4 ^ 2 := by
    rw [Real.sqrt_eq_rpow, hNn, ← Real.rpow_natCast n4 4, ← Real.rpow_mul hn40.le]
    norm_num
  -- `w^{1/2} ≤ 2 n₄/(v q)`
  have hw12 : w ^ ((1 : ℝ) / 2) ≤ 2 * n4 / (v * q) := by
    have hw4 : w ≤ (2 * n4 / (v * q)) ^ 2 := by
      have e1 : w = 2 * n4 ^ 2 / (v ^ 2 * q ^ 2) := by rw [hw, hsqrtN, hVv, hQq]
      have e2 : (2 * n4 / (v * q)) ^ 2 = 4 * n4 ^ 2 / (v ^ 2 * q ^ 2) := by
        rw [div_pow, mul_pow, mul_pow]
        norm_num
      rw [e1, e2]
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith [pow_pos hn40 2]
    calc w ^ ((1 : ℝ) / 2) ≤ ((2 * n4 / (v * q)) ^ 2) ^ ((1 : ℝ) / 2) :=
          Real.rpow_le_rpow hw0.le hw4 (by norm_num)
      _ = 2 * n4 / (v * q) := by
          rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  -- put everything together
  set Y : ℝ := x ^ ((1 : ℝ) / 4) * w ^ ((1 : ℝ) / 2) * U ^ (-(1 : ℝ) / 2) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hYle : Y ≤ y * (2 * n4 / (v * q)) * (1 / u) := by
    rw [hY, hUm12, ← hy]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw12 hy0) (by positivity)
  set T₂ : ℝ := x ^ ((1 : ℝ) / 4) * U ^ ((1 : ℝ) / 2) * N ^ ((9 : ℝ) / 4) * V ^ ((3 : ℝ) / 2) *
    (Q : ℝ) ^ (-(1 : ℝ) / 2) with hT₂
  have hT₂eq : T₂ = y * u * n4 ^ 9 * v ^ 3 / q := by
    rw [hT₂, hU12, hN94, hV32, hQm12, ← hy]
    ring
  have hT₂0 : 0 ≤ T₂ := by rw [hT₂eq]; positivity
  -- `U Q Y (N V L₀) ≤ 4 T₂ L₀` and `U Q Y (8 N² V²/Q) ≤ 16 T₂`
  have hNV : N * V = n4 ^ 4 * v ^ 2 := by rw [hNn, hVv]
  have hY1 : U * Q * Y * (N * V * L₀) ≤ 4 * T₂ * L₀ := by
    have h1 : U * Q * Y * (N * V * L₀) ≤ U * Q * (y * (2 * n4 / (v * q)) * (1 / u)) * (N * V * L₀) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hYle (by positivity)
    refine h1.trans ?_
    rw [hT₂eq, hUu, hQq, hNV]
    have hq2 : q ^ 2 ≤ 2 * v ^ 2 * n4 ^ 4 := by rw [← hQq, ← hVv, ← hNn]; exact hQ2
    rw [show u ^ 2 * q ^ 2 * (y * (2 * n4 / (v * q)) * (1 / u)) * (n4 ^ 4 * v ^ 2 * L₀) =
      (2 * y * u * n4 ^ 5 * v * L₀) * q ^ 2 / q by
        first | (field_simp; done) | (field_simp; ring),
      show 4 * (y * u * n4 ^ 9 * v ^ 3 / q) * L₀ = (2 * y * u * n4 ^ 5 * v * L₀) * (2 * v ^ 2 * n4 ^ 4) / q by
        first | (field_simp; done) | (field_simp; ring)]
    apply div_le_div_of_nonneg_right _ hq0'.le
    exact mul_le_mul_of_nonneg_left hq2 (by positivity)
  have hY2 : U * Q * Y * (8 * N ^ 2 * V ^ 2 / Q) ≤ 16 * T₂ := by
    have h1 : U * Q * Y * (8 * N ^ 2 * V ^ 2 / Q) ≤
        U * Q * (y * (2 * n4 / (v * q)) * (1 / u)) * (8 * N ^ 2 * V ^ 2 / Q) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hYle (by positivity)
    refine h1.trans (le_of_eq ?_)
    rw [hT₂eq, hUu, hQq, hNn, hVv]
    first | (field_simp; done) | (field_simp; ring)
  -- the card and `Q + 1`
  have hcard : (((dyadic U).card * (Q + 1) : ℕ) : ℝ) ≤ 2 * U * (2 * Q) := by
    push_cast
    have h1 := card_dyadic_le hU0.le
    have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have h2 : (Q : ℝ) + 1 ≤ 2 * Q := by linarith
    exact mul_le_mul h1 h2 (by positivity) (by positivity)
  -- the two pieces
  clear hin hcount hcnt_le hA
  set T₁ : ℝ := U ^ 2 * Q * N * V with hT₁
  have hT₁0 : 0 ≤ T₁ := by positivity
  have hNV0 : (0 : ℝ) ≤ N * V := by positivity
  have hNVL : N * V ≤ 2 * (N * V * L₀) := by
    have := mul_le_mul_of_nonneg_left hL₀ hNV0
    linarith
  have hpiece1 : 2 * U * (2 * Q) *
      (2 * U * cnt δ + C1 * ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ)) ≤
      4 * C6 * (18 + 18 * C1) * ((J : ℝ) + 1) * L₀ * T₁ := by
    have h1 : 2 * U * cnt δ ≤ 2 * U * (C6 * (N * V * L₀ + 4 * (N * V))) :=
      mul_le_mul_of_nonneg_left hcδ (by positivity)
    have h2 : C1 * ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ) ≤
        C1 * (C6 * (2 * U * (N * V * L₀) + 8 * ((J : ℝ) + 1) * U * (N * V))) :=
      mul_le_mul_of_nonneg_left hshell hC1
    have h3 : 2 * U * (C6 * (N * V * L₀ + 4 * (N * V))) +
        C1 * (C6 * (2 * U * (N * V * L₀) + 8 * ((J : ℝ) + 1) * U * (N * V))) ≤
        C6 * (18 + 18 * C1) * ((J : ℝ) + 1) * (U * (N * V * L₀)) := by
      have hJ1 : 1 ≤ (J : ℝ) + 1 := by linarith
      have hUNVL : 0 ≤ U * (N * V * L₀) := by positivity
      have hp1 : 2 * U * (C6 * (N * V * L₀ + 4 * (N * V))) ≤ 18 * C6 * (U * (N * V * L₀)) := by
        have h9 : N * V * L₀ + 4 * (N * V) ≤ 9 * (N * V * L₀) := by linarith
        have := mul_le_mul_of_nonneg_left h9 (by positivity : (0 : ℝ) ≤ 2 * U * C6)
        linarith
      have hp2 : C1 * (C6 * (2 * U * (N * V * L₀) + 8 * ((J : ℝ) + 1) * U * (N * V))) ≤
          18 * C1 * C6 * ((J : ℝ) + 1) * (U * (N * V * L₀)) := by
        have hc0 : 0 ≤ C1 * C6 := mul_nonneg hC1 hC6
        have hx1 : 2 * U * (N * V * L₀) ≤ 2 * ((J : ℝ) + 1) * (U * (N * V * L₀)) := by
          have := mul_le_mul_of_nonneg_right hJ1 hUNVL
          linarith
        have hx2 : 8 * ((J : ℝ) + 1) * U * (N * V) ≤ 16 * ((J : ℝ) + 1) * (U * (N * V * L₀)) := by
          have := mul_le_mul_of_nonneg_left hNVL (by positivity : (0 : ℝ) ≤ 8 * ((J : ℝ) + 1) * U)
          linarith
        have := mul_le_mul_of_nonneg_left (add_le_add hx1 hx2) hc0
        linarith
      have hp3 : 18 * C6 * (U * (N * V * L₀)) ≤ 18 * C6 * ((J : ℝ) + 1) * (U * (N * V * L₀)) := by
        have := mul_le_mul_of_nonneg_right hJ1 (by positivity : 0 ≤ 18 * C6 * (U * (N * V * L₀)))
        linarith
      linarith
    calc 2 * U * (2 * Q) *
        (2 * U * cnt δ + C1 * ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ))
        ≤ 2 * U * (2 * Q) * (C6 * (18 + 18 * C1) * ((J : ℝ) + 1) * (U * (N * V * L₀))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ = 4 * C6 * (18 + 18 * C1) * ((J : ℝ) + 1) * L₀ * T₁ := by rw [hT₁]; ring
  have hpiece2 : 2 * U * (2 * Q) * (cnt w * (C1 * Y)) ≤ 144 * C1 * C6 * ((J : ℝ) + 1) * L₀ * T₂ := by
    have h1 : cnt w * (C1 * Y) ≤ C6 * (N * V * L₀ + 8 * N ^ 2 * V ^ 2 / Q) * (C1 * Y) :=
      mul_le_mul_of_nonneg_right hcw (by positivity)
    calc 2 * U * (2 * Q) * (cnt w * (C1 * Y))
        ≤ 2 * U * (2 * Q) * (C6 * (N * V * L₀ + 8 * N ^ 2 * V ^ 2 / Q) * (C1 * Y)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 * C1 * C6 * (U * Q * Y * (N * V * L₀) + U * Q * Y * (8 * N ^ 2 * V ^ 2 / Q)) := by ring
      _ ≤ 4 * C1 * C6 * (4 * T₂ * L₀ + 16 * T₂) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith
      _ ≤ 4 * C1 * C6 * (4 * T₂ * L₀ + 32 * T₂ * L₀) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := mul_le_mul_of_nonneg_left hL₀ (by positivity : (0 : ℝ) ≤ 32 * T₂)
          linarith
      _ = 144 * C1 * C6 * L₀ * T₂ := by ring
      _ ≤ 144 * C1 * C6 * ((J : ℝ) + 1) * L₀ * T₂ := by
          have h0 : 0 ≤ 144 * C1 * C6 * L₀ * T₂ := by positivity
          have hJ1 : 1 ≤ (J : ℝ) + 1 := by linarith
          have := mul_le_mul_of_nonneg_right hJ1 h0
          linarith
  -- conclude
  have hsum0 : 0 ≤ ∑ p ∈ (pairSet V N).filter (fun p => |lamOf p| ≤ w),
      ‖∑ u ∈ dyadic U, e (Real.sqrt x * lamOf p / u)‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hS : ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
      2 * U * (2 * Q) * ((2 * U * cnt δ +
        C1 * ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ)) + cnt w * (C1 * Y)) := by
    refine hCS.trans ?_
    refine mul_le_mul hcard ?_ hsum0 (by positivity)
    refine hpt.trans ?_
    have := hite
    linarith
  have hK : 0 ≤ 4 * C6 * (18 + 18 * C1) + 144 * C1 * C6 := by positivity
  calc ‖tripleSumZC x N U V a b c‖ ^ 2 ≤ _ := hS
    _ = 2 * U * (2 * Q) * (2 * U * cnt δ +
          C1 * ∑ j ∈ Finset.range (J + 1), U / 2 ^ j * cnt (2 ^ (j + 1) * δ)) +
        2 * U * (2 * Q) * (cnt w * (C1 * Y)) := by ring
    _ ≤ 4 * C6 * (18 + 18 * C1) * ((J : ℝ) + 1) * L₀ * T₁ +
        144 * C1 * C6 * ((J : ℝ) + 1) * L₀ * T₂ := add_le_add hpiece1 hpiece2
    _ ≤ (4 * C6 * (18 + 18 * C1) + 144 * C1 * C6) * ((J : ℝ) + 1) * L₀ * (T₁ + T₂) := by
        have h1 : 0 ≤ 4 * C6 * (18 + 18 * C1) * ((J : ℝ) + 1) * L₀ * T₂ := by positivity
        have h2 : 0 ≤ 144 * C1 * C6 * ((J : ℝ) + 1) * L₀ * T₁ := by positivity
        linarith


end L9

end LeanProofs.IntegerPoints

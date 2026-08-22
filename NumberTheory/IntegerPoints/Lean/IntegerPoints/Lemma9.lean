import IntegerPoints.Lemma9Sum

/-!
# Zhai–Cao, Lemma 9

`∑_{n ∼ N} a_n ∑_{u ∼ U} b_u ∑_{v ∼ M/U} c_v e(√(nx)/(uv))
  ≪ (x^{1/12} M^{7/12} N^{11/12} + M^{11/12} N^{1/2}) log x`
for `1 ≤ N ≤ M^{1/4}`, `M ≤ x^{4/15}`, `M^{1/6} ≤ U ≤ M^{5/6}`.

From the core estimate (`L9.core_bound`)
`‖S‖² ≤ K (J+1) log(2NV) (U² Q N V + x^{1/4} U^{1/2} N^{9/4} V^{3/2} Q^{-1/2})`
with `J + 1 ≤ 4 log x`, `log(2NV) ≤ 2 log x`, and the choice
`Q₀ = x^{1/6} U^{-1} N^{5/6} V^{1/3}`: if `Q₀ ≤ 1` take `Q = 1` (giving
`U V^{1/2} N^{1/2} ≤ M^{11/12} N^{1/2}`), if `1 < Q₀ ≤ VN` take `Q = ⌈Q₀⌉`
(giving `x^{1/12} U^{1/2} V^{2/3} N^{11/12} ≤ x^{1/12} M^{7/12} N^{11/12}`), and if
`Q₀ > VN` then `x > M⁵ N` and the trivial bound `8MN` suffices.  We assume
`M^{1/2} ≤ U ≤ M^{5/6}`; the other case follows by exchanging `u` and `v`.

All exponents are multiples of `1/12`, so the final bookkeeping is done with the
twelfth roots `X = x^{1/12}`, `Mₘ = M^{1/12}`, … as polynomial inequalities.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace L9

/-! ### Generalities -/

theorem tripleSumZC_swap (x N U V : ℝ) (a b c : ℕ → ℂ) :
    tripleSumZC x N U V a b c = tripleSumZC x N V U a c b := by
  unfold tripleSumZC
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
  rw [mul_comm (u : ℝ) v]
  ring

/-- The trivial bound `‖S‖ ≤ 8 N U V`. -/
theorem tripleSum_trivial {x N U V : ℝ} (hN : 0 ≤ N) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (a b c : ℕ → ℂ) (ha : UnitBounded a) (hb : UnitBounded b) (hc : UnitBounded c) :
    ‖tripleSumZC x N U V a b c‖ ≤ 8 * (N * U * V) := by
  unfold tripleSumZC
  have h1 : ∀ n u v : ℕ, ‖a n * b u * c v * e (Real.sqrt (n * x) / (u * v))‖ ≤ 1 := by
    intro n u v
    rw [norm_mul, norm_mul, norm_mul, norm_e, mul_one]
    exact mul_le_one₀ (mul_le_one₀ (ha n) (norm_nonneg _) (hb u)) (norm_nonneg _) (hc v)
  calc ‖∑ n ∈ dyadic N, ∑ u ∈ dyadic U, ∑ v ∈ dyadic V,
        a n * b u * c v * e (Real.sqrt (n * x) / (u * v))‖
      ≤ ∑ n ∈ dyadic N, ∑ u ∈ dyadic U, ∑ v ∈ dyadic V, (1 : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ => h1 n u v)
    _ = ((dyadic N).card : ℝ) * (dyadic U).card * (dyadic V).card := by
        simp [Finset.sum_const, mul_assoc]
    _ ≤ (2 * N) * (2 * U) * (2 * V) := by
        have h1 := card_dyadic_le hN
        have h2 := card_dyadic_le hU
        have h3 := card_dyadic_le hV
        exact mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity)
          (by positivity)
    _ = 8 * (N * U * V) := by ring

/-- `J + 1 ≤ 4 log x` for `J = log₂ ⌊r⌋`, `0 ≤ r ≤ 2x`, `x ≥ 8`. -/
theorem J_bound {r x : ℝ} (hx : 8 ≤ x) (hr0 : 0 ≤ r) (hr : r ≤ 2 * x) :
    ((Nat.log 2 ⌊r⌋₊ : ℝ) + 1) ≤ 4 * Real.log x := by
  have hl2 := BI.log_two_gt
  have hlx : 1 ≤ Real.log x := by
    have : Real.log 8 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  rcases Nat.eq_zero_or_pos ⌊r⌋₊ with h0 | hpos
  · rw [h0, Nat.log_zero_right]
    simp only [Nat.cast_zero, zero_add]
    linarith
  · set J := Nat.log 2 ⌊r⌋₊ with hJ
    have h1 : (2 : ℝ) ^ J ≤ 2 * x := by
      have := Nat.pow_log_le_self 2 (by omega : ⌊r⌋₊ ≠ 0)
      have h' : ((2 ^ J : ℕ) : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast this
      push_cast at h'
      exact h'.trans ((Nat.floor_le hr0).trans hr)
    have h2 : (J : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log x := by
      have := Real.log_le_log (by positivity) h1
      rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at this
      exact this
    have h3 : (J : ℝ) ≤ 1 + 7 / 4 * Real.log x := by
      have hl2' : 0 < Real.log 2 := by linarith
      have : (J : ℝ) ≤ (Real.log 2 + Real.log x) / Real.log 2 := by
        rw [le_div_iff₀ hl2']
        exact h2
      rw [add_div, div_self hl2'.ne'] at this
      have h4 : Real.log x / Real.log 2 ≤ 7 / 4 * Real.log x := by
        rw [div_le_iff₀ hl2']
        nlinarith
      linarith
    linarith

/-- Twelfth roots: `t^(k/12) = (t^(1/12))^k`. -/
theorem rpow_eq_pow_root12 {t : ℝ} (ht : 0 ≤ t) (k : ℕ) (e : ℝ) (he : e = k / 12) :
    t ^ e = (t ^ ((1 : ℝ) / 12)) ^ k := by
  subst he
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  congr 1
  ring

theorem root12_pow_twelve {t : ℝ} (ht : 0 ≤ t) : (t ^ ((1 : ℝ) / 12)) ^ 12 = t := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul ht]
  norm_num

theorem sqrt_eq_root12 {t : ℝ} (ht : 0 ≤ t) : Real.sqrt t = (t ^ ((1 : ℝ) / 12)) ^ 6 := by
  rw [Real.sqrt_eq_rpow]
  exact rpow_eq_pow_root12 ht 6 ((1 : ℝ) / 2) (by norm_num)

theorem one_le_root12 {t : ℝ} (ht : 1 ≤ t) : 1 ≤ t ^ ((1 : ℝ) / 12) :=
  Real.one_le_rpow ht (by norm_num)

/-! ### The main estimate for `M^{1/2} ≤ U ≤ M^{5/6}` -/

set_option maxHeartbeats 4000000 in
theorem lemma9_main {K : ℝ} (hK : 0 ≤ K)
    (hcore : ∀ {x U V N : ℝ} (Q : ℕ), 1 ≤ U → 1 ≤ V → 1 ≤ N → 0 < x → 1 ≤ Q →
      (Q : ℝ) ≤ 2 * V * N → U * V ^ 2 * Real.sqrt N ≤ Real.sqrt x →
      ∀ (a b c : ℕ → ℂ), UnitBounded a → UnitBounded b → UnitBounded c →
      ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
        K * ((Nat.log 2 ⌊2 * Real.sqrt N / (V * Q) / (U / Real.sqrt x)⌋₊ : ℝ) + 1) *
          Real.log (2 * N * V) *
          (U ^ 2 * Q * N * V +
            x ^ ((1 : ℝ) / 4) * U ^ ((1 : ℝ) / 2) * N ^ ((9 : ℝ) / 4) * V ^ ((3 : ℝ) / 2) *
              (Q : ℝ) ^ (-(1 : ℝ) / 2)))
    {x M N U V : ℝ} (hx : 8 ≤ x) (hM : 1 ≤ M) (hN : 1 ≤ N) (hNM : N ≤ M ^ ((1 : ℝ) / 4))
    (hMx : M ≤ x ^ ((4 : ℝ) / 15)) (hUV : U * V = M) (hU1 : M ^ ((1 : ℝ) / 2) ≤ U)
    (hU2 : U ≤ M ^ ((5 : ℝ) / 6)) (hV1 : 1 ≤ V)
    (a b c : ℕ → ℂ) (ha : UnitBounded a) (hb : UnitBounded b) (hc : UnitBounded c) :
    ‖tripleSumZC x N U V a b c‖ ≤
      (8 + Real.sqrt (24 * K)) *
        ((x ^ ((1 : ℝ) / 12) * M ^ ((7 : ℝ) / 12) * N ^ ((11 : ℝ) / 12) +
          M ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 2)) * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hU1' : 1 ≤ U := le_trans (Real.one_le_rpow hM (by norm_num)) hU1
  have hU0 : 0 < U := by linarith
  have hV0 : 0 < V := by linarith
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hlx : 1 ≤ Real.log x := by
    have := BI.log_two_gt
    have h8 : Real.log 8 ≤ Real.log x := Real.log_le_log (by norm_num) hx
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      push_cast
      ring
    linarith
  have hlx0 : 0 ≤ Real.log x := by linarith
  -- twelfth roots
  set X := x ^ ((1 : ℝ) / 12) with hX
  set Mm := M ^ ((1 : ℝ) / 12) with hMm
  set Nn := N ^ ((1 : ℝ) / 12) with hNn
  set Uu := U ^ ((1 : ℝ) / 12) with hUu
  set Vv := V ^ ((1 : ℝ) / 12) with hVv
  have hX1 : 1 ≤ X := one_le_root12 hx1
  have hMm1 : 1 ≤ Mm := one_le_root12 hM
  have hNn1 : 1 ≤ Nn := one_le_root12 hN
  have hUu1 : 1 ≤ Uu := one_le_root12 hU1'
  have hVv1 : 1 ≤ Vv := one_le_root12 hV1
  have hX0 : 0 < X := by linarith
  have hMm0 : 0 < Mm := by linarith
  have hNn0 : 0 < Nn := by linarith
  have hUu0 : 0 < Uu := by linarith
  have hVv0 : 0 < Vv := by linarith
  have hx12 : X ^ 12 = x := root12_pow_twelve hx0.le
  have hM12 : Mm ^ 12 = M := root12_pow_twelve hM0.le
  have hN12 : Nn ^ 12 = N := root12_pow_twelve hN0.le
  have hU12 : Uu ^ 12 = U := root12_pow_twelve hU0.le
  have hV12 : Vv ^ 12 = V := root12_pow_twelve hV0.le
  have hUV' : Uu * Vv = Mm := by
    rw [hUu, hVv, hMm, ← Real.mul_rpow hU0.le hV0.le, hUV]
  -- the hypotheses in twelfth roots
  have hNM' : Nn ^ 12 ≤ Mm ^ 3 := by
    rw [hN12, ← rpow_eq_pow_root12 hM0.le 3 ((1 : ℝ) / 4) (by norm_num)]
    exact hNM
  have hU1'' : Mm ^ 6 ≤ Uu ^ 12 := by
    rw [hU12, ← rpow_eq_pow_root12 hM0.le 6 ((1 : ℝ) / 2) (by norm_num)]
    exact hU1
  have hU2'' : Uu ^ 12 ≤ Mm ^ 10 := by
    rw [hU12, ← rpow_eq_pow_root12 hM0.le 10 ((5 : ℝ) / 6) (by norm_num)]
    exact hU2
  have hM13 : Mm ^ 39 ≤ X ^ 12 := by
    rw [hx12, ← rpow_eq_pow_root12 hM0.le 39 ((39 : ℝ) / 12) (by norm_num)]
    calc M ^ ((39 : ℝ) / 12) ≤ (x ^ ((4 : ℝ) / 15)) ^ ((39 : ℝ) / 12) :=
          Real.rpow_le_rpow hM0.le hMx (by norm_num)
      _ = x ^ ((13 : ℝ) / 15) := by
          rw [← Real.rpow_mul hx0.le]
          norm_num
      _ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
      _ = x := Real.rpow_one x
  -- derived inequalities: `Vv² ≤ Mm`, `Uu⁶ ≤ Mm⁵`, `Mm³ ≤ Uu⁶`
  have hVv2 : Vv ^ 2 ≤ Mm := by
    have h1 : Vv ^ 12 ≤ Mm ^ 6 := by
      have : Uu ^ 12 * Vv ^ 12 = Mm ^ 12 := by rw [← mul_pow, hUV']
      nlinarith [pow_pos hUu0 12, pow_pos hVv0 12, pow_pos hMm0 6]
    have : (Vv ^ 2) ^ 6 ≤ Mm ^ 6 := by rw [← pow_mul]; exact h1
    exact le_of_pow_le_pow_left₀ (by norm_num) hMm0.le this
  have hUu6 : Uu ^ 6 ≤ Mm ^ 5 := by
    have : (Uu ^ 6) ^ 2 ≤ (Mm ^ 5) ^ 2 := by rw [← pow_mul, ← pow_mul]; exact hU2''
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
  have hMm3 : Mm ^ 3 ≤ Uu ^ 6 := by
    have : (Mm ^ 3) ^ 2 ≤ (Uu ^ 6) ^ 2 := by rw [← pow_mul, ← pow_mul]; exact hU1''
    exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
  have hUu6Vv8 : Uu ^ 6 * Vv ^ 8 ≤ Mm ^ 7 := by
    calc Uu ^ 6 * Vv ^ 8 = (Uu * Vv) ^ 6 * Vv ^ 2 := by ring
      _ = Mm ^ 6 * Vv ^ 2 := by rw [hUV']
      _ ≤ Mm ^ 6 * Mm := mul_le_mul_of_nonneg_left hVv2 (by positivity)
      _ = Mm ^ 7 := by ring
  have hUu12Vv6 : Uu ^ 12 * Vv ^ 6 ≤ Mm ^ 11 := by
    calc Uu ^ 12 * Vv ^ 6 = (Uu * Vv) ^ 6 * Uu ^ 6 := by ring
      _ = Mm ^ 6 * Uu ^ 6 := by rw [hUV']
      _ ≤ Mm ^ 6 * Mm ^ 5 := mul_le_mul_of_nonneg_left hUu6 (by positivity)
      _ = Mm ^ 11 := by ring
  -- the target in twelfth roots
  have htarget : x ^ ((1 : ℝ) / 12) * M ^ ((7 : ℝ) / 12) * N ^ ((11 : ℝ) / 12) +
      M ^ ((11 : ℝ) / 12) * N ^ ((1 : ℝ) / 2) = X * Mm ^ 7 * Nn ^ 11 + Mm ^ 11 * Nn ^ 6 := by
    rw [rpow_eq_pow_root12 hM0.le 7 ((7 : ℝ) / 12) (by norm_num), rpow_eq_pow_root12 hN0.le 11 ((11 : ℝ) / 12) (by norm_num),
      rpow_eq_pow_root12 hM0.le 11 ((11 : ℝ) / 12) (by norm_num), rpow_eq_pow_root12 hN0.le 6 ((1 : ℝ) / 2) (by norm_num)]
  rw [htarget]
  set Tgt := X * Mm ^ 7 * Nn ^ 11 + Mm ^ 11 * Nn ^ 6 with hTgt
  have hTgt1 : X * Mm ^ 7 * Nn ^ 11 ≤ Tgt := by rw [hTgt]; exact le_add_of_nonneg_right (by positivity)
  have hTgt2 : Mm ^ 11 * Nn ^ 6 ≤ Tgt := by rw [hTgt]; exact le_add_of_nonneg_left (by positivity)
  have hTgt0 : 0 ≤ Tgt := by positivity
  have hsq : 0 ≤ Real.sqrt (24 * K) := Real.sqrt_nonneg _
  -- common ingredients for the core bound
  have hH : U * V ^ 2 * Real.sqrt N ≤ Real.sqrt x := by
    have h0 : 0 ≤ U * V ^ 2 * Real.sqrt N :=
      mul_nonneg (mul_nonneg hU0.le (sq_nonneg V)) (Real.sqrt_nonneg N)
    rw [← Real.sqrt_sq h0]
    apply Real.sqrt_le_sqrt
    rw [← hU12, ← hV12, ← hx12, sqrt_eq_root12 hN0.le]
    calc (Uu ^ 12 * (Vv ^ 12) ^ 2 * Nn ^ 6) ^ 2 = (Uu * Vv) ^ 24 * Vv ^ 24 * Nn ^ 12 := by ring
      _ = Mm ^ 24 * Vv ^ 24 * Nn ^ 12 := by rw [hUV']
      _ ≤ Mm ^ 24 * Mm ^ 12 * Mm ^ 3 := by
          have h1 : Vv ^ 24 ≤ Mm ^ 12 := by
            have : (Vv ^ 2) ^ 12 ≤ Mm ^ 12 := pow_le_pow_left₀ (by positivity) hVv2 12
            rw [← pow_mul] at this
            exact this
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hNM' (by positivity)
            (by positivity)
      _ = Mm ^ 39 := by ring
      _ ≤ X ^ 12 := hM13
  have hNVx : 2 * N * V ≤ x ^ 2 := by
    rw [← hN12, ← hV12, ← hx12]
    have h1 : Vv ^ 12 ≤ Mm ^ 6 := by
      have : (Vv ^ 2) ^ 6 ≤ Mm ^ 6 := pow_le_pow_left₀ (by positivity) hVv2 6
      rw [← pow_mul] at this
      exact this
    have h2 : Nn ^ 12 * Vv ^ 12 ≤ Mm ^ 9 := by
      calc Nn ^ 12 * Vv ^ 12 ≤ Mm ^ 3 * Mm ^ 6 :=
            mul_le_mul hNM' h1 (by positivity) (by positivity)
        _ = Mm ^ 9 := by ring
    have h3 : Mm ^ 9 ≤ Mm ^ 39 := pow_le_pow_right₀ hMm1 (by norm_num)
    have h4 : (X ^ 12) ^ 2 = X ^ 12 * X ^ 12 := by ring
    have h5 : (2 : ℝ) ≤ X ^ 12 := by rw [hx12]; linarith
    rw [h4]
    nlinarith [pow_pos hX0 12]
  have hL₀ : Real.log (2 * N * V) ≤ 2 * Real.log x := by
    calc Real.log (2 * N * V) ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hNVx
      _ = 2 * Real.log x := by rw [Real.log_pow]; push_cast; ring
  have hL₀0 : 0 ≤ Real.log (2 * N * V) := Real.log_nonneg (by nlinarith)
  have hNx : N ≤ x := by
    rw [← hN12, ← hx12]
    calc Nn ^ 12 ≤ Mm ^ 3 := hNM'
      _ ≤ Mm ^ 39 := pow_le_pow_right₀ hMm1 (by norm_num)
      _ ≤ X ^ 12 := hM13
  have hJ : ∀ Q : ℕ, 1 ≤ Q →
      ((Nat.log 2 ⌊2 * Real.sqrt N / (V * Q) / (U / Real.sqrt x)⌋₊ : ℝ) + 1) ≤ 4 * Real.log x := by
    intro Q hQ
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
    apply J_bound hx (by positivity)
    have hsN : Real.sqrt N ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
    have hsx : Real.sqrt x ≤ x := by
      rw [Real.sqrt_le_left hx0.le]
      nlinarith
    have hQ1' : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
    have hVQU : 1 ≤ V * Q * U :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hV1 hQ1') hU1'
    calc 2 * Real.sqrt N / (V * Q) / (U / Real.sqrt x) = 2 * Real.sqrt N * Real.sqrt x / (V * Q * U) := by
          field_simp
      _ ≤ 2 * Real.sqrt N * Real.sqrt x / 1 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hVQU
      _ = 2 * Real.sqrt N * Real.sqrt x := by ring
      _ ≤ 2 * x := by
          have : Real.sqrt N * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
            mul_le_mul_of_nonneg_right hsN (Real.sqrt_nonneg _)
          rw [Real.mul_self_sqrt hx0.le] at this
          linarith
  -- the core bound in the form `‖S‖² ≤ 8 K (log x)² · T(Q)`
  have hcore' : ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ 2 * V * N →
      ‖tripleSumZC x N U V a b c‖ ^ 2 ≤ 8 * K * Real.log x ^ 2 *
        (Uu ^ 24 * Q * Nn ^ 12 * Vv ^ 12 +
          X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Q : ℝ) ^ (-(1 : ℝ) / 2)) := by
    intro Q hQ hQ2
    have h := hcore Q hU1' hV1 hN hx0 hQ hQ2 hH a b c ha hb hc
    have hT : U ^ 2 * Q * N * V +
        x ^ ((1 : ℝ) / 4) * U ^ ((1 : ℝ) / 2) * N ^ ((9 : ℝ) / 4) * V ^ ((3 : ℝ) / 2) *
          (Q : ℝ) ^ (-(1 : ℝ) / 2) =
        Uu ^ 24 * Q * Nn ^ 12 * Vv ^ 12 +
          X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Q : ℝ) ^ (-(1 : ℝ) / 2) := by
      rw [rpow_eq_pow_root12 hx0.le 3 ((1 : ℝ) / 4) (by norm_num), rpow_eq_pow_root12 hU0.le 6 ((1 : ℝ) / 2) (by norm_num),
        rpow_eq_pow_root12 hN0.le 27 ((9 : ℝ) / 4) (by norm_num), rpow_eq_pow_root12 hV0.le 18 ((3 : ℝ) / 2) (by norm_num),
        ← hX, ← hUu, ← hNn, ← hVv, ← hU12, ← hN12, ← hV12]
      ring
    rw [hT] at h
    have hT0 : 0 ≤ Uu ^ 24 * Q * Nn ^ 12 * Vv ^ 12 +
        X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Q : ℝ) ^ (-(1 : ℝ) / 2) := by positivity
    refine h.trans ?_
    have h1 := hJ Q hQ
    calc K * ((Nat.log 2 ⌊2 * Real.sqrt N / (V * Q) / (U / Real.sqrt x)⌋₊ : ℝ) + 1) *
          Real.log (2 * N * V) * _
        ≤ K * (4 * Real.log x) * (2 * Real.log x) * _ := by
          gcongr
      _ = 8 * K * Real.log x ^ 2 * _ := by ring
  -- from `‖S‖² ≤ c² Z²` to `‖S‖ ≤ c Z`
  have hsqrt : ∀ Z : ℝ, 0 ≤ Z → ‖tripleSumZC x N U V a b c‖ ^ 2 ≤ 24 * K * Real.log x ^ 2 * Z ^ 2 →
      ‖tripleSumZC x N U V a b c‖ ≤ Real.sqrt (24 * K) * Real.log x * Z := by
    intro Z hZ h
    have : ‖tripleSumZC x N U V a b c‖ ^ 2 ≤ (Real.sqrt (24 * K) * Real.log x * Z) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      exact h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  -- the balancing parameter `Q₀ = X² Nn¹⁰ Vv⁴ / Uu¹²`
  set Q₀ : ℝ := X ^ 2 * Nn ^ 10 * Vv ^ 4 / Uu ^ 12 with hQ₀
  have hQ₀0 : 0 < Q₀ := by positivity
  have hVN : V * N = Vv ^ 12 * Nn ^ 12 := by rw [hV12, hN12]
  rcases le_or_gt Q₀ 1 with hQ₀1 | hQ₀1
  · -- Case A: `Q = 1`
    have h := hcore' 1 le_rfl (by push_cast; nlinarith)
    push_cast at h
    rw [Real.one_rpow, mul_one, mul_one] at h
    -- the second term is at most the first
    have hsec : X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 ≤ Uu ^ 24 * Nn ^ 12 * Vv ^ 12 := by
      have h1 : X ^ 2 * Nn ^ 10 * Vv ^ 4 ≤ Uu ^ 12 := by
        rw [hQ₀, div_le_one (by positivity)] at hQ₀1
        exact hQ₀1
      have h2 : X * Nn ^ 5 * Vv ^ 2 ≤ Uu ^ 6 := by
        have : (X * Nn ^ 5 * Vv ^ 2) ^ 2 ≤ (Uu ^ 6) ^ 2 := by
          calc (X * Nn ^ 5 * Vv ^ 2) ^ 2 = X ^ 2 * Nn ^ 10 * Vv ^ 4 := by ring
            _ ≤ Uu ^ 12 := h1
            _ = (Uu ^ 6) ^ 2 := by ring
        exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
      have h3 : (X * Nn ^ 5 * Vv ^ 2) ^ 3 ≤ (Uu ^ 6) ^ 3 := pow_le_pow_left₀ (by positivity) h2 3
      calc X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 = (X * Nn ^ 5 * Vv ^ 2) ^ 3 * (Uu ^ 6 * Nn ^ 12 * Vv ^ 12) := by
            ring
        _ ≤ (Uu ^ 6) ^ 3 * (Uu ^ 6 * Nn ^ 12 * Vv ^ 12) :=
            mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = Uu ^ 24 * Nn ^ 12 * Vv ^ 12 := by ring
    have hZ : ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
        24 * K * Real.log x ^ 2 * (Uu ^ 12 * Nn ^ 6 * Vv ^ 6) ^ 2 := by
      refine h.trans ?_
      have : Uu ^ 24 * Nn ^ 12 * Vv ^ 12 + X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 ≤
          3 * (Uu ^ 12 * Nn ^ 6 * Vv ^ 6) ^ 2 := by
        have : (Uu ^ 12 * Nn ^ 6 * Vv ^ 6) ^ 2 = Uu ^ 24 * Nn ^ 12 * Vv ^ 12 := by ring
        rw [this]
        have hA0 : 0 < Uu ^ 24 * Nn ^ 12 * Vv ^ 12 := by positivity
        linarith [hA0, hsec]
      calc 8 * K * Real.log x ^ 2 * (Uu ^ 24 * Nn ^ 12 * Vv ^ 12 + X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18)
          ≤ 8 * K * Real.log x ^ 2 * (3 * (Uu ^ 12 * Nn ^ 6 * Vv ^ 6) ^ 2) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have hS := hsqrt _ (by positivity) hZ
    calc ‖tripleSumZC x N U V a b c‖ ≤ Real.sqrt (24 * K) * Real.log x * (Uu ^ 12 * Nn ^ 6 * Vv ^ 6) := hS
      _ ≤ Real.sqrt (24 * K) * Real.log x * (Mm ^ 11 * Nn ^ 6) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hsq hlx0)
          calc Uu ^ 12 * Nn ^ 6 * Vv ^ 6 = (Uu ^ 12 * Vv ^ 6) * Nn ^ 6 := by ring
            _ ≤ Mm ^ 11 * Nn ^ 6 := mul_le_mul_of_nonneg_right hUu12Vv6 (by positivity)
      _ ≤ (8 + Real.sqrt (24 * K)) * (Tgt * Real.log x) := by
          have : Real.sqrt (24 * K) * Real.log x * (Mm ^ 11 * Nn ^ 6) ≤
              Real.sqrt (24 * K) * Real.log x * Tgt :=
            mul_le_mul_of_nonneg_left hTgt2 (mul_nonneg hsq hlx0)
          nlinarith [mul_nonneg hTgt0 hlx0]
  rcases le_or_gt Q₀ (V * N) with hQ₀VN | hQ₀VN
  · -- Case B: `Q = ⌈Q₀⌉`
    set Q : ℕ := ⌈Q₀⌉₊ with hQ
    have hQ1 : 1 ≤ Q := Nat.one_le_ceil_iff.2 hQ₀0
    have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
    have hQge : Q₀ ≤ Q := Nat.le_ceil Q₀
    have hQle : (Q : ℝ) ≤ 2 * Q₀ := by
      have := Nat.ceil_lt_add_one hQ₀0.le
      rw [← hQ] at this
      linarith
    have hQ2 : (Q : ℝ) ≤ 2 * V * N := by linarith
    have h := hcore' Q hQ1 hQ2
    -- `Q^{-1/2} ≤ Q₀^{-1/2} = Uu⁶/(X Nn⁵ Vv²)`
    have hQinv : (Q : ℝ) ^ (-(1 : ℝ) / 2) ≤ Uu ^ 6 / (X * Nn ^ 5 * Vv ^ 2) := by
      have hsq : Real.sqrt Q₀ = X * Nn ^ 5 * Vv ^ 2 / Uu ^ 6 := by
        rw [hQ₀, show X ^ 2 * Nn ^ 10 * Vv ^ 4 / Uu ^ 12 = (X * Nn ^ 5 * Vv ^ 2 / Uu ^ 6) ^ 2 by ring]
        exact Real.sqrt_sq (by positivity)
      rw [show -(1 : ℝ) / 2 = -(1 / 2) by ring, Real.rpow_neg hQ0.le, ← Real.sqrt_eq_rpow]
      calc (Real.sqrt Q)⁻¹ ≤ (Real.sqrt Q₀)⁻¹ :=
            inv_anti₀ (Real.sqrt_pos.2 hQ₀0) (Real.sqrt_le_sqrt hQge)
        _ = Uu ^ 6 / (X * Nn ^ 5 * Vv ^ 2) := by rw [hsq, inv_div]
    have hZ : ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
        24 * K * Real.log x ^ 2 * (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) ^ 2 := by
      refine h.trans ?_
      have h1 : Uu ^ 24 * Q * Nn ^ 12 * Vv ^ 12 ≤ 2 * (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) ^ 2 := by
        calc Uu ^ 24 * Q * Nn ^ 12 * Vv ^ 12 ≤ Uu ^ 24 * (2 * Q₀) * Nn ^ 12 * Vv ^ 12 := by
              gcongr
          _ = 2 * (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) ^ 2 := by
              rw [hQ₀]
              first | (field_simp; done) | (field_simp; ring)
      have h2 : X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Q : ℝ) ^ (-(1 : ℝ) / 2) ≤
          (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) ^ 2 := by
        calc X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Q : ℝ) ^ (-(1 : ℝ) / 2)
            ≤ X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Uu ^ 6 / (X * Nn ^ 5 * Vv ^ 2)) :=
              mul_le_mul_of_nonneg_left hQinv (by positivity)
          _ = (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) ^ 2 := by
              first | (field_simp; done) | (field_simp; ring)
      calc 8 * K * Real.log x ^ 2 * (Uu ^ 24 * Q * Nn ^ 12 * Vv ^ 12 +
            X ^ 3 * Uu ^ 6 * Nn ^ 27 * Vv ^ 18 * (Q : ℝ) ^ (-(1 : ℝ) / 2))
          ≤ 8 * K * Real.log x ^ 2 * (3 * (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ = _ := by ring
    have hS := hsqrt _ (by positivity) hZ
    calc ‖tripleSumZC x N U V a b c‖
        ≤ Real.sqrt (24 * K) * Real.log x * (X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8) := hS
      _ ≤ Real.sqrt (24 * K) * Real.log x * (X * Mm ^ 7 * Nn ^ 11) := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hsq hlx0)
          calc X * Uu ^ 6 * Nn ^ 11 * Vv ^ 8 = X * Nn ^ 11 * (Uu ^ 6 * Vv ^ 8) := by ring
            _ ≤ X * Nn ^ 11 * Mm ^ 7 := mul_le_mul_of_nonneg_left hUu6Vv8 (by positivity)
            _ = X * Mm ^ 7 * Nn ^ 11 := by ring
      _ ≤ (8 + Real.sqrt (24 * K)) * (Tgt * Real.log x) := by
          have : Real.sqrt (24 * K) * Real.log x * (X * Mm ^ 7 * Nn ^ 11) ≤
              Real.sqrt (24 * K) * Real.log x * Tgt :=
            mul_le_mul_of_nonneg_left hTgt1 (mul_nonneg hsq hlx0)
          nlinarith [mul_nonneg hTgt0 hlx0]
  · -- Case C: `Q₀ > VN`, the trivial bound
    have htriv := tripleSum_trivial (x := x) hN0.le hU0.le hV0.le a b c ha hb hc
    -- `X > Mm⁵ Nn`
    have hX5 : Mm ^ 5 * Nn < X := by
      have h1 : Vv ^ 12 * Nn ^ 12 * Uu ^ 12 < X ^ 2 * Nn ^ 10 * Vv ^ 4 := by
        rw [hQ₀, lt_div_iff₀ (by positivity), hVN] at hQ₀VN
        exact hQ₀VN
      have h2 : Uu ^ 12 * Vv ^ 8 * Nn ^ 2 < X ^ 2 := by
        have hpos : 0 < Vv ^ 4 * Nn ^ 10 := by positivity
        nlinarith [pow_pos hVv0 4, pow_pos hNn0 10]
      have h3 : Mm ^ 10 * Nn ^ 2 < X ^ 2 := by
        have : Mm ^ 10 ≤ Uu ^ 12 * Vv ^ 8 := by
          calc Mm ^ 10 = (Uu * Vv) ^ 8 * Mm ^ 2 := by rw [hUV']; ring
            _ ≤ (Uu * Vv) ^ 8 * Uu ^ 4 := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                have : (Mm ^ 2) ^ 3 ≤ (Uu ^ 4) ^ 3 := by
                  rw [← pow_mul, ← pow_mul]
                  exact hU1''
                exact le_of_pow_le_pow_left₀ (by norm_num) (by positivity) this
            _ = Uu ^ 12 * Vv ^ 8 := by ring
        nlinarith [pow_pos hNn0 2]
      have : (Mm ^ 5 * Nn) ^ 2 < X ^ 2 := by
        rw [mul_pow, ← pow_mul]
        exact h3
      exact lt_of_pow_lt_pow_left₀ 2 hX0.le this
    calc ‖tripleSumZC x N U V a b c‖ ≤ 8 * (N * U * V) := htriv
      _ = 8 * (N * M) := by rw [← hUV]; ring
      _ = 8 * (Mm ^ 12 * Nn ^ 12) := by rw [hM12, hN12]; ring
      _ = 8 * ((Mm ^ 5 * Nn) * (Mm ^ 7 * Nn ^ 11)) := by ring
      _ ≤ 8 * (X * (Mm ^ 7 * Nn ^ 11)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hX5.le (by positivity)
      _ = 8 * (X * Mm ^ 7 * Nn ^ 11) := by ring
      _ ≤ 8 * Tgt := by linarith
      _ ≤ (8 + Real.sqrt (24 * K)) * (Tgt * Real.log x) := by
          nlinarith [mul_nonneg hTgt0 hlx0, mul_nonneg hsq (mul_nonneg hTgt0 hlx0)]

/-! ### Zhai–Cao, Lemma 9 -/

/-- The core estimate with its constant. -/
theorem core_exists : ∃ K : ℝ, 0 ≤ K ∧ ∀ {x U V N : ℝ} (Q : ℕ), 1 ≤ U → 1 ≤ V → 1 ≤ N → 0 < x →
    1 ≤ Q → (Q : ℝ) ≤ 2 * V * N → U * V ^ 2 * Real.sqrt N ≤ Real.sqrt x →
    ∀ (a b c : ℕ → ℂ), UnitBounded a → UnitBounded b → UnitBounded c →
    ‖tripleSumZC x N U V a b c‖ ^ 2 ≤
      K * ((Nat.log 2 ⌊2 * Real.sqrt N / (V * Q) / (U / Real.sqrt x)⌋₊ : ℝ) + 1) *
        Real.log (2 * N * V) *
        (U ^ 2 * Q * N * V +
          x ^ ((1 : ℝ) / 4) * U ^ ((1 : ℝ) / 2) * N ^ ((9 : ℝ) / 4) * V ^ ((3 : ℝ) / 2) *
            (Q : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨C1, hC1, hin⟩ := inner_sum_bound
  obtain ⟨C6, hC6⟩ := zhaiCao_lemma6_holds (1 / 2) 1 (by norm_num)
  set C6' := max C6 0 with hC6'
  have hC6'0 : 0 ≤ C6' := le_max_right _ _
  have hcount : ∀ M N Δ : ℝ, 1 ≤ M → 1 ≤ N → 0 < Δ →
      (quadrupleCount (1 / 2) 1 M N Δ : ℝ) ≤
        C6' * (M * N * Real.log (2 * M * N) + Δ * M ^ 2 * N ^ 2) := by
    intro M N Δ hM hN hΔ
    refine (hC6 M N Δ hM hN hΔ).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    have : 0 ≤ Real.log (2 * M * N) := Real.log_nonneg (by nlinarith)
    positivity
  refine ⟨4 * C6' * (18 + 18 * C1) + 144 * C1 * C6', by positivity, ?_⟩
  intro x U V N Q hU hV hN hx hQ hQ2 hH a b c ha hb hc
  exact core_bound hC1 hC6'0 hin hcount Q hU hV hN hx hQ hQ2 hH a b c ha hb hc

/-- **Zhai–Cao, Lemma 9** holds. -/
theorem _root_.LeanProofs.IntegerPoints.zhaiCao_lemma9_holds : zhaiCao_lemma9 := by
  intro ε hε
  obtain ⟨K, hK, hcore⟩ := core_exists
  refine ⟨8 + Real.sqrt (24 * K), 8, fun x M N U a b c hx hN1 hNM hxM hMx hU1 hU2 ha hb hc => ?_⟩
  have hx0 : 0 < x := by linarith
  have hM1 : (1 : ℝ) ≤ M := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have h2 : (1 : ℝ) ≤ (M : ℝ) ^ ((1 : ℝ) / 4) := le_trans this hNM
    by_contra h
    push Not at h
    have : (M : ℝ) ^ ((1 : ℝ) / 4) < 1 :=
      Real.rpow_lt_one (Nat.cast_nonneg M) h (by norm_num)
    linarith
  have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hM0 : (0 : ℝ) < M := by linarith
  have hU1' : (1 : ℝ) ≤ U := le_trans (Real.one_le_rpow hM1 (by norm_num)) hU1
  have hU0 : (0 : ℝ) < U := by linarith
  set V : ℝ := (M : ℝ) / U with hV
  have hUV : U * V = M := by rw [hV]; field_simp
  have hV1 : 1 ≤ V := by
    rw [hV, le_div_iff₀ hU0, one_mul]
    calc (U : ℝ) ≤ (M : ℝ) ^ ((5 : ℝ) / 6) := hU2
      _ ≤ (M : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (by norm_num)
      _ = M := Real.rpow_one _
  have hV0 : 0 < V := by linarith
  -- `V ≤ M^{5/6}` and `V ≥ M^{1/6}`
  have hV2 : V ≤ (M : ℝ) ^ ((5 : ℝ) / 6) := by
    rw [hV, div_le_iff₀ hU0]
    calc (M : ℝ) = (M : ℝ) ^ ((5 : ℝ) / 6) * (M : ℝ) ^ ((1 : ℝ) / 6) := by
          rw [← Real.rpow_add hM0]; norm_num
      _ ≤ (M : ℝ) ^ ((5 : ℝ) / 6) * U := mul_le_mul_of_nonneg_left hU1 (by positivity)
  have hV1' : (M : ℝ) ^ ((1 : ℝ) / 2) ≤ V ∨ (M : ℝ) ^ ((1 : ℝ) / 2) ≤ U := by
    by_contra h
    push Not at h
    have : U * V < (M : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 2) :=
      mul_lt_mul'' h.2 h.1 hU0.le hV0.le
    rw [hUV, ← Real.rpow_add hM0] at this
    norm_num at this
  rcases hV1' with hVbig | hUbig
  · -- swap: `V` plays the role of `U`
    rw [tripleSumZC_swap]
    exact lemma9_main hK hcore hx hM1 hN1' hNM hMx (by rw [mul_comm]; exact hUV) hVbig hV2 hU1'
      a c b ha hc hb
  · exact lemma9_main hK hcore hx hM1 hN1' hNM hMx hUV hUbig hU2 hV1 a b c ha hb hc


end L9

end LeanProofs.IntegerPoints

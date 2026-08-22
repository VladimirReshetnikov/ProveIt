import IntegerPoints.Lemma1

/-!
# The exponent pair `(1/2, 1/2)`

For `f ∈ F(N, 2, s, y, 1/4)` one has `-f'' ≍ s y t^{-s-1} ≍ z/N` on
`[N, 2N]`, where `z = y N^{-s} ≥ 1`, so the van der Corput second-derivative
test gives `‖∑ e(f(n))‖ ≪ N √(z/N) + √(N/z) ≤ 2 √(zN)`.  Hence
`(1/2, 1/2)` is an exponent pair (this is the B-process applied to the
trivial pair `(0, 1)`).
-/

open Real Finset

namespace LeanProofs.IntegerPoints

/-- `(1/2, 1/2)` is an exponent pair. -/
theorem isExponentPair_half_half : IsExponentPair (1 / 2) (1 / 2) := by
  refine ⟨by norm_num, le_rfl, le_rfl, by norm_num, fun s hs => ?_⟩
  -- the constants
  set κ : ℝ := Real.sqrt (3 / 4 * s * (2 : ℝ) ^ (-(s + 1))) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκ2 : κ ^ 2 = 3 / 4 * s * (2 : ℝ) ^ (-(s + 1)) := Real.sq_sqrt (by positivity)
  set α : ℝ := 5 / 3 * (2 : ℝ) ^ (s + 1) with hα
  have hα0 : 0 ≤ α := by positivity
  refine ⟨2, 1 / 4, 24 * α * κ + 24 / κ + 4 * κ, by norm_num, by norm_num,
    fun N y a b f hN hy hf => ?_⟩
  obtain ⟨hNa, hab, hb2N, hf2, hcls⟩ := hf
  have hN0 : 0 < N := by linarith
  have hy0 : 0 < y := lt_of_lt_of_le (Real.rpow_pos_of_pos hN0 s) hy
  -- `z = y N^{-s} ≥ 1`
  set z : ℝ := y * N ^ (-s) with hz
  have hz1 : 1 ≤ z := by
    rw [hz, Real.rpow_neg hN0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hN0 s),
      one_mul]
    exact hy
  have hz0 : 0 < z := by linarith
  have hsz : 1 ≤ Real.sqrt z := Real.one_le_sqrt.2 hz1
  have hsz0 : 0 < Real.sqrt z := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  -- the second derivative
  have hf2' : ContDiff ℝ 2 f := by simpa using hf2
  have hd2 : ∀ t ∈ Set.Icc a b,
      |deriv (deriv f) t + s * y * t ^ (-s - 1)| ≤ 1 / 4 * (s * y * t ^ (-s - 1)) := by
    intro t ht
    have := hcls 1 (by norm_num) t ht
    simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, add_zero, pow_one,
      Nat.cast_one, iteratedDeriv_succ, iteratedDeriv_zero] at this
    calc |deriv (deriv f) t + s * y * t ^ (-s - 1)|
        = |deriv (deriv f) t - -1 * s * y * t ^ (-s - 1)| := by ring_nf
      _ ≤ 1 / 4 * s * y * t ^ (-s - 1) := this
      _ = 1 / 4 * (s * y * t ^ (-s - 1)) := by ring
  -- `λ₂ = κ² z / N`
  set lam2 : ℝ := κ ^ 2 * z / N with hlam2
  have hlam2pos : 0 < lam2 := by positivity
  have hpow : ∀ t ∈ Set.Icc a b, lam2 ≤ 3 / 4 * (s * y * t ^ (-s - 1)) ∧
      5 / 4 * (s * y * t ^ (-s - 1)) ≤ α * lam2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hN0 (hNa.trans ht.1)
    have htN : N ≤ t := hNa.trans ht.1
    have ht2N : t ≤ 2 * N := ht.2.trans hb2N
    have h1 : (2 * N) ^ (-s - 1) ≤ t ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
    have h2 : t ^ (-s - 1) ≤ N ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hN0 htN (by linarith)
    have hsy : 0 < s * y := by positivity
    -- `(2N)^{-s-1} = 2^{-(s+1)} N^{-s-1}` and `κ² z / N = (s/2) 2^{-(s+1)} y N^{-s-1}`
    have hsplit : (2 * N) ^ (-s - 1) = (2 : ℝ) ^ (-(s + 1)) * N ^ (-s - 1) := by
      rw [Real.mul_rpow (by norm_num) hN0.le]
      congr 1
      congr 1
      ring
    have hNs : N ^ (-s - 1) = N ^ (-s) * N⁻¹ := by
      rw [show (-s - 1 : ℝ) = -s + (-1) by ring, Real.rpow_add hN0, Real.rpow_neg_one]
    have hlam2' : lam2 = 3 / 4 * (s * y * (2 * N) ^ (-s - 1)) := by
      rw [hlam2, hκ2, hsplit, hNs, hz]
      ring
    have h2pow : (2 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (-(s + 1)) = 1 := by
      rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
    constructor
    · rw [hlam2']
      have := mul_le_mul_of_nonneg_left h1 hsy.le
      linarith
    · rw [hlam2', hα, hsplit]
      have := mul_le_mul_of_nonneg_left h2 hsy.le
      calc 5 / 4 * (s * y * t ^ (-s - 1)) ≤ 5 / 4 * (s * y * N ^ (-s - 1)) := by linarith
        _ = 5 / 3 * 2 ^ (s + 1) * (3 / 4 * (s * y * (2 ^ (-(s + 1)) * N ^ (-s - 1)))) := by
            have : (5 : ℝ) / 4 * (s * y * N ^ (-s - 1)) =
                5 / 3 * (2 ^ (s + 1) * 2 ^ (-(s + 1))) * (3 / 4 * (s * y * N ^ (-s - 1))) := by
              rw [h2pow]
              ring
            rw [this]
            ring
  -- the summation range
  set A := ⌊a⌋₊ with hA
  set B := ⌊b⌋₊ with hB
  have hrange : intRange a b = Finset.Ioc A B := rfl
  have ha0 : 0 ≤ a := by linarith
  have hAa : (A : ℝ) ≤ a := Nat.floor_le ha0
  have haA : a < A + 1 := Nat.lt_floor_add_one a
  have hBb : (B : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hsub : Set.Icc (A + 1 : ℝ) B ⊆ Set.Icc a b := Set.Icc_subset_Icc haA.le hBb
  have hBA : ((B - A : ℕ) : ℝ) ≤ 2 * N := by
    rcases le_or_gt A B with h | h
    · rw [Nat.cast_sub h]
      linarith
    · rw [Nat.sub_eq_zero_of_le h.le]
      push_cast
      positivity
  -- the target
  have htarget : (y * N ^ (-s)) ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) = Real.sqrt z * Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, hz]
  rw [htarget, hrange]
  have hC1 : 24 * α * κ + 24 / κ ≤ 24 * α * κ + 24 / κ + 4 * κ := by linarith
  have hC2 : 4 * κ ≤ 24 * α * κ + 24 / κ + 4 * κ := by
    have : 0 ≤ 24 * α * κ := by positivity
    have : 0 ≤ 24 / κ := by positivity
    linarith
  have hsqrt : Real.sqrt lam2 = κ * Real.sqrt z / Real.sqrt N := by
    rw [hlam2, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq hκ0.le]
  rcases le_or_gt lam2 (1 / 4) with hsmall | hbig
  · -- the second-derivative test applied to `-f`
    have hg2 := Lemma1.deriv2_neg f
    have hvdc := VdC.second_derivative (fun t => -f t) hf2'.neg A B lam2 α hlam2pos hsmall hα0
      fun t ht => by
        rw [hg2]
        simp only
        have hb := hd2 t (hsub ht)
        have hp := hpow t (hsub ht)
        rw [abs_le] at hb
        constructor <;> linarith [hb.1, hb.2, hp.1, hp.2]
    rw [Lemma1.norm_sum_e_neg] at hvdc
    have hterm1 : 12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 ≤
        24 * α * κ * (Real.sqrt z * Real.sqrt N) := by
      rw [hsqrt]
      have hNs : N / Real.sqrt N = Real.sqrt N := by
        rw [div_eq_iff hsN.ne']
        exact (Real.mul_self_sqrt hN0.le).symm
      calc 12 * α * ((B - A : ℕ) : ℝ) * (κ * Real.sqrt z / Real.sqrt N)
          ≤ 12 * α * (2 * N) * (κ * Real.sqrt z / Real.sqrt N) := by gcongr
        _ = 24 * α * κ * Real.sqrt z * (N / Real.sqrt N) := by ring
        _ = 24 * α * κ * (Real.sqrt z * Real.sqrt N) := by rw [hNs]; ring
    have hterm2 : 24 / Real.sqrt lam2 ≤ 24 / κ * (Real.sqrt z * Real.sqrt N) := by
      rw [hsqrt]
      have : 24 / (κ * Real.sqrt z / Real.sqrt N) = 24 / κ * Real.sqrt N * (1 / Real.sqrt z) := by
        field_simp
      rw [this]
      have h1 : 1 / Real.sqrt z ≤ Real.sqrt z := by
        rw [div_le_iff₀ hsz0]
        nlinarith
      calc 24 / κ * Real.sqrt N * (1 / Real.sqrt z) ≤ 24 / κ * Real.sqrt N * Real.sqrt z :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 24 / κ * (Real.sqrt z * Real.sqrt N) := by ring
    calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖
        ≤ 12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 + 24 / Real.sqrt lam2 := hvdc
      _ ≤ (24 * α * κ + 24 / κ) * (Real.sqrt z * Real.sqrt N) := by
          rw [add_mul]
          exact add_le_add hterm1 hterm2
      _ ≤ (24 * α * κ + 24 / κ + 4 * κ) * (Real.sqrt z * Real.sqrt N) :=
          mul_le_mul_of_nonneg_right hC1 (by positivity)
  · -- trivial bound: `λ₂ > 1/4` means `N < 4 κ² z`
    have hcard : ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ ((B - A : ℕ) : ℝ) := by
      calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ ∑ n ∈ Finset.Ioc A B, ‖e (f n)‖ := norm_sum_le _ _
        _ = ((B - A : ℕ) : ℝ) := by simp [norm_e]
    have hN4 : N < 4 * κ ^ 2 * z := by
      rw [hlam2, lt_div_iff₀ hN0] at hbig
      linarith
    have hsqN : Real.sqrt N ≤ 2 * κ * Real.sqrt z := by
      have : Real.sqrt N ≤ Real.sqrt (4 * κ ^ 2 * z) := Real.sqrt_le_sqrt hN4.le
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hκ0.le,
        show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
      linarith
    calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ ((B - A : ℕ) : ℝ) := hcard
      _ ≤ 2 * N := hBA
      _ = 2 * (Real.sqrt N * Real.sqrt N) := by rw [Real.mul_self_sqrt hN0.le]
      _ ≤ 2 * ((2 * κ * Real.sqrt z) * Real.sqrt N) := by gcongr
      _ = 4 * κ * (Real.sqrt z * Real.sqrt N) := by ring
      _ ≤ (24 * α * κ + 24 / κ + 4 * κ) * (Real.sqrt z * Real.sqrt N) :=
          mul_le_mul_of_nonneg_right hC2 (by positivity)

end LeanProofs.IntegerPoints

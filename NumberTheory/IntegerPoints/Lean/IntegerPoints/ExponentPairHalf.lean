import IntegerPoints.Lemma1

/-!
# The exponent pair `(1/2, 1/2)`

For `f ∈ F(N, 2, s, y, 1/4)` one has `-f'' ≍ s y t^{-s-1} ≍ z/N` on
`[N, 2N]`, where `z = y N^{-s}`.  If `z ≥ 1/2` the van der Corput
second-derivative test gives `‖∑ e(f(n))‖ ≪ N √(z/N) + √(N/z) ≪ √(zN)`;
if `z < 1/2` then `f' ∈ [cz, 1 - cz]` and Kuz'min–Landau gives
`‖∑ e(f(n))‖ ≪ 1/z = y⁻¹ N^s`.  Hence `(1/2, 1/2)` is an exponent pair in
the sense of Graham–Kolesnik (the B-process applied to the trivial pair).
-/

open Real Finset

namespace LeanProofs.IntegerPoints

set_option maxHeartbeats 800000 in
/-- `(1/2, 1/2)` is an exponent pair. -/
theorem isExponentPair_half_half : IsExponentPair (1 / 2) (1 / 2) := by
  refine ⟨by norm_num, le_rfl, le_rfl, by norm_num, fun s hs => ?_⟩
  -- the constants
  set κ : ℝ := Real.sqrt (3 / 4 * s * (2 : ℝ) ^ (-(s + 1))) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκ2 : κ ^ 2 = 3 / 4 * s * (2 : ℝ) ^ (-(s + 1)) := Real.sq_sqrt (by positivity)
  set α : ℝ := 5 / 3 * (2 : ℝ) ^ (s + 1) with hα
  have hα0 : 0 ≤ α := by positivity
  set CA : ℝ := 36 * α * κ + 48 / κ + 6 * κ with hCA
  set CB : ℝ := 16 / 3 * (2 : ℝ) ^ s with hCB
  have hCA0 : 0 ≤ CA := by rw [hCA]; positivity
  have hCB0 : 0 ≤ CB := by rw [hCB]; positivity
  refine ⟨2, 1 / 4, max CA CB, by norm_num, by norm_num, fun N y a b f hN hy hf => ?_⟩
  obtain ⟨hNa, hab, hb2N, hf2, hcls⟩ := hf
  -- `z = y N^{-s}`
  set z : ℝ := y * N ^ (-s) with hz
  have hz0 : 0 < z := by positivity
  have hsz0 : 0 < Real.sqrt z := Real.sqrt_pos.2 hz0
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hzinv : z⁻¹ = y⁻¹ * N ^ s := by
    rw [hz, mul_inv, Real.rpow_neg hN.le, inv_inv]
  -- the derivatives
  have hf2' : ContDiff ℝ 2 f := by simpa using hf2
  have hf' : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf2')).2.2
  have hd1 : ∀ t ∈ Set.Icc a b, |deriv f t - y * t ^ (-s)| < 1 / 4 * (y * t ^ (-s)) := by
    intro t ht
    have := hcls 0 (by norm_num) t ht
    simp only [Finset.range_zero, Finset.prod_empty, Nat.cast_zero, sub_zero, pow_zero,
      zero_add, iteratedDeriv_one] at this
    calc |deriv f t - y * t ^ (-s)| = |deriv f t - 1 * 1 * y * t ^ (-s)| := by ring_nf
      _ < 1 / 4 * 1 * y * t ^ (-s) := this
      _ = 1 / 4 * (y * t ^ (-s)) := by ring
  have hd2 : ∀ t ∈ Set.Icc a b,
      |deriv (deriv f) t + s * y * t ^ (-s - 1)| ≤ 1 / 4 * (s * y * t ^ (-s - 1)) := by
    intro t ht
    have := hcls 1 (by norm_num) t ht
    simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero, add_zero, pow_one,
      Nat.cast_one, iteratedDeriv_succ, iteratedDeriv_zero] at this
    calc |deriv (deriv f) t + s * y * t ^ (-s - 1)|
        = |deriv (deriv f) t - -1 * s * y * t ^ (-s - 1)| := by ring_nf
      _ ≤ 1 / 4 * s * y * t ^ (-s - 1) := this.le
      _ = 1 / 4 * (s * y * t ^ (-s - 1)) := by ring
  -- the summation range
  set A := ⌊a⌋₊ with hA
  set B := ⌊b⌋₊ with hB
  have hrange : intRange a b = Finset.Ioc A B := rfl
  have ha0 : 0 ≤ a := by linarith
  have haA : a < A + 1 := Nat.lt_floor_add_one a
  have hBb : (B : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hsub : Set.Icc (A + 1 : ℝ) B ⊆ Set.Icc a b := Set.Icc_subset_Icc haA.le hBb
  have hBA : ((B - A : ℕ) : ℝ) ≤ 3 * N := by
    have := card_intRange_le hN hNa hab hb2N
    rwa [intRange, Nat.card_Ioc] at this
  -- the target
  have htarget : (y * N ^ (-s)) ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2) =
      Real.sqrt z * Real.sqrt N := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, hz]
  rw [htarget, hrange, ← hzinv]
  have hT0 : 0 ≤ Real.sqrt z * Real.sqrt N + z⁻¹ := by positivity
  rcases le_or_gt (1 / 2) z with hzhalf | hzhalf
  · -- `z ≥ 1/2`: the second-derivative test
    have hbound : ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ CA * (Real.sqrt z * Real.sqrt N) := by
      set lam2 : ℝ := κ ^ 2 * z / N with hlam2
      have hlam2pos : 0 < lam2 := by positivity
      have hpow : ∀ t ∈ Set.Icc a b, lam2 ≤ 3 / 4 * (s * y * t ^ (-s - 1)) ∧
          5 / 4 * (s * y * t ^ (-s - 1)) ≤ α * lam2 := by
        intro t ht
        have ht0 : 0 < t := lt_of_lt_of_le hN (hNa.trans ht.1)
        have htN : N ≤ t := hNa.trans ht.1
        have ht2N : t ≤ 2 * N := ht.2.trans hb2N
        have h1 : (2 * N) ^ (-s - 1) ≤ t ^ (-s - 1) :=
          Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
        have h2 : t ^ (-s - 1) ≤ N ^ (-s - 1) :=
          Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
        have hsy : 0 < s * y := by positivity
        have hsplit : (2 * N) ^ (-s - 1) = (2 : ℝ) ^ (-(s + 1)) * N ^ (-s - 1) := by
          rw [Real.mul_rpow (by norm_num) hN.le]
          congr 1
          congr 1
          ring
        have hNs : N ^ (-s - 1) = N ^ (-s) * N⁻¹ := by
          rw [show (-s - 1 : ℝ) = -s + (-1) by ring, Real.rpow_add hN, Real.rpow_neg_one]
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
      have hsqrt : Real.sqrt lam2 = κ * Real.sqrt z / Real.sqrt N := by
        rw [hlam2, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq hκ0.le]
      have hC1 : 36 * α * κ + 48 / κ ≤ CA := by
        rw [hCA]
        have : 0 ≤ 6 * κ := by positivity
        linarith
      have hC2 : 6 * κ ≤ CA := by
        rw [hCA]
        have : 0 ≤ 36 * α * κ := by positivity
        have : 0 ≤ 48 / κ := by positivity
        linarith
      have hinvz : 1 / Real.sqrt z ≤ 2 * Real.sqrt z := by
        rw [div_le_iff₀ hsz0]
        have := Real.mul_self_sqrt hz0.le
        nlinarith
      rcases le_or_gt lam2 (1 / 4) with hsmall | hbig
      · have hg2 := Lemma1.deriv2_neg f
        have hvdc := VdC.second_derivative (fun t => -f t) hf2'.neg A B lam2 α hlam2pos hsmall
          hα0 fun t ht => by
            rw [hg2]
            simp only
            have hb := hd2 t (hsub ht)
            have hp := hpow t (hsub ht)
            rw [abs_le] at hb
            constructor <;> linarith [hb.1, hb.2, hp.1, hp.2]
        rw [Lemma1.norm_sum_e_neg] at hvdc
        have hterm1 : 12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 ≤
            36 * α * κ * (Real.sqrt z * Real.sqrt N) := by
          rw [hsqrt]
          have hNs : N / Real.sqrt N = Real.sqrt N := by
            rw [div_eq_iff hsN.ne']
            exact (Real.mul_self_sqrt hN.le).symm
          calc 12 * α * ((B - A : ℕ) : ℝ) * (κ * Real.sqrt z / Real.sqrt N)
              ≤ 12 * α * (3 * N) * (κ * Real.sqrt z / Real.sqrt N) := by gcongr
            _ = 36 * α * κ * Real.sqrt z * (N / Real.sqrt N) := by ring
            _ = 36 * α * κ * (Real.sqrt z * Real.sqrt N) := by rw [hNs]; ring
        have hterm2 : 24 / Real.sqrt lam2 ≤ 48 / κ * (Real.sqrt z * Real.sqrt N) := by
          rw [hsqrt]
          have : 24 / (κ * Real.sqrt z / Real.sqrt N) =
              24 / κ * Real.sqrt N * (1 / Real.sqrt z) := by
            field_simp
          rw [this]
          calc 24 / κ * Real.sqrt N * (1 / Real.sqrt z)
              ≤ 24 / κ * Real.sqrt N * (2 * Real.sqrt z) :=
                mul_le_mul_of_nonneg_left hinvz (by positivity)
            _ = 48 / κ * (Real.sqrt z * Real.sqrt N) := by ring
        calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖
            ≤ 12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 + 24 / Real.sqrt lam2 := hvdc
          _ ≤ (36 * α * κ + 48 / κ) * (Real.sqrt z * Real.sqrt N) := by
              rw [add_mul]
              exact add_le_add hterm1 hterm2
          _ ≤ CA * (Real.sqrt z * Real.sqrt N) :=
              mul_le_mul_of_nonneg_right hC1 (by positivity)
      · have hcard : ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ ((B - A : ℕ) : ℝ) := by
          calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ ∑ n ∈ Finset.Ioc A B, ‖e (f n)‖ :=
                norm_sum_le _ _
            _ = ((B - A : ℕ) : ℝ) := by simp [norm_e]
        have hN4 : N < 4 * κ ^ 2 * z := by
          rw [hlam2, lt_div_iff₀ hN] at hbig
          linarith
        have hsqN : Real.sqrt N ≤ 2 * κ * Real.sqrt z := by
          have : Real.sqrt N ≤ Real.sqrt (4 * κ ^ 2 * z) := Real.sqrt_le_sqrt hN4.le
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), Real.sqrt_sq hκ0.le,
            show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
          linarith
        calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ ((B - A : ℕ) : ℝ) := hcard
          _ ≤ 3 * N := hBA
          _ = 3 * (Real.sqrt N * Real.sqrt N) := by rw [Real.mul_self_sqrt hN.le]
          _ ≤ 3 * ((2 * κ * Real.sqrt z) * Real.sqrt N) := by gcongr
          _ = 6 * κ * (Real.sqrt z * Real.sqrt N) := by ring
          _ ≤ CA * (Real.sqrt z * Real.sqrt N) :=
              mul_le_mul_of_nonneg_right hC2 (by positivity)
    calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ CA * (Real.sqrt z * Real.sqrt N) := hbound
      _ ≤ max CA CB * (Real.sqrt z * Real.sqrt N + z⁻¹) :=
          mul_le_mul (le_max_left _ _) (by linarith [inv_pos.2 hz0]) (by positivity)
            (le_trans hCA0 (le_max_left _ _))
  · -- `z < 1/2`: Kuz'min–Landau
    set lam : ℝ := 3 / 4 * (2 : ℝ) ^ (-s) * z with hlam
    have h2s : (0 : ℝ) < (2 : ℝ) ^ (-s) := by positivity
    have h2s1 : (2 : ℝ) ^ (-s) ≤ 1 := by
      rw [Real.rpow_neg (by norm_num)]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) hs.le)
    have hlam0 : 0 < lam := by positivity
    have h2sz : (2 : ℝ) ^ (-s) * z ≤ 1 / 2 := by
      calc (2 : ℝ) ^ (-s) * z ≤ 1 * (1 / 2) :=
            mul_le_mul h2s1 hzhalf.le hz0.le zero_le_one
        _ = 1 / 2 := by ring
    have hlam1 : lam ≤ 1 / 2 := by
      rw [hlam, mul_assoc]
      linarith
    -- `f' ∈ [λ, 1 - λ]` on `[a, b]`
    have hderiv : ∀ t ∈ Set.Icc a b, lam ≤ deriv f t ∧ deriv f t ≤ 1 - lam := by
      intro t ht
      have ht0 : 0 < t := lt_of_lt_of_le hN (hNa.trans ht.1)
      have htN : N ≤ t := hNa.trans ht.1
      have ht2N : t ≤ 2 * N := ht.2.trans hb2N
      have h1 : (2 * N) ^ (-s) ≤ t ^ (-s) := Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
      have h2 : t ^ (-s) ≤ N ^ (-s) := Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
      have hsplit : (2 * N) ^ (-s) = (2 : ℝ) ^ (-s) * N ^ (-s) := Real.mul_rpow (by norm_num) hN.le
      have hb := abs_lt.1 (hd1 t ht)
      have hyt1 : (2 : ℝ) ^ (-s) * z ≤ y * t ^ (-s) := by
        rw [hz, ← mul_assoc, mul_comm ((2 : ℝ) ^ (-s)) y, mul_assoc, ← hsplit]
        exact mul_le_mul_of_nonneg_left h1 hy.le
      have hyt2 : y * t ^ (-s) ≤ z := by
        rw [hz]
        exact mul_le_mul_of_nonneg_left h2 hy.le
      constructor
      · rw [hlam]
        linarith
      · have : lam ≤ 3 / 8 := by
          rw [hlam, mul_assoc]
          linarith
        linarith
    have hanti : AntitoneOn (deriv f) (Set.Icc (A + 1 : ℝ) B) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) hf'.continuous.continuousOn
        (hf'.differentiable one_ne_zero).differentiableOn fun x hx => ?_
      rw [interior_Icc] at hx
      have hb := abs_le.1 (hd2 x (hsub ⟨hx.1.le, hx.2.le⟩))
      have hx0 : 0 < x := lt_of_lt_of_le hN (hNa.trans (hsub ⟨hx.1.le, hx.2.le⟩).1)
      have : 0 < s * y * x ^ (-s - 1) := by positivity
      linarith [hb.2]
    have hKL := KL.kuzmin_landau f A B lam hlam0 hlam1 (hf2'.of_le (by norm_num)) (Or.inr hanti)
      fun t ht => by
        have := hderiv t (hsub ht)
        exact VdC.nearestIntDist_ge 0 (by push_cast; linarith) (by push_cast; linarith)
    have hbound : 4 / lam = CB * z⁻¹ := by
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
      rw [hlam, hCB, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp
      ring
    calc ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤ 4 / lam := hKL
      _ = CB * z⁻¹ := hbound
      _ ≤ max CA CB * (Real.sqrt z * Real.sqrt N + z⁻¹) :=
          mul_le_mul (le_max_right _ _) (by linarith [mul_pos hsz0 hsN]) (by positivity)
            (le_trans hCB0 (le_max_right _ _))

end LeanProofs.IntegerPoints

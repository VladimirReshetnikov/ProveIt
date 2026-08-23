import IntegerPoints.Lemma1

/-!
# A reusable high-curvature Graham–Kolesnik bound

For a phase in `F(N, 2, s, y, ε)` with `0 < ε < 1/2` and natural scale
`L = yN⁻ˢ ≥ 1/2`, the second-derivative test gives
`‖∑ e(f(n))‖ ≪ √L √N`.  This is the common analytic core of the two forms in
which Graham–Kolesnik invoke Theorem 2.2 and of the high-curvature branch of
the exponent pair `(1/2, 1/2)`.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

set_option maxHeartbeats 800000 in
/-- A uniform high-curvature bound for a Graham–Kolesnik phase.  The witness
depends only on `s`; it is therefore stronger than the public invocation forms,
whose constants may also depend on `ε`. -/
theorem gk_high_curvature_bound (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ε N y a b : ℝ) (f : ℝ → ℝ),
        0 < ε → ε < 1 / 2 → 0 < N → 0 < y →
        InGKClass N 2 s y ε a b f → 1 / 2 ≤ y * N ^ (-s) →
        ‖∑ n ∈ intRange a b, e (f n)‖ ≤
          C * (Real.sqrt (y * N ^ (-s)) * Real.sqrt N) := by
  set κ : ℝ := Real.sqrt (1 / 2 * s * (2 : ℝ) ^ (-(s + 1))) with hκ
  have hκ0 : 0 < κ := Real.sqrt_pos.2 (by positivity)
  have hκ2 : κ ^ 2 = 1 / 2 * s * (2 : ℝ) ^ (-(s + 1)) :=
    Real.sq_sqrt (by positivity)
  set α : ℝ := 3 * (2 : ℝ) ^ (s + 1) with hα
  have hα0 : 0 ≤ α := by positivity
  set C : ℝ := 36 * α * κ + 48 / κ + 6 * κ with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C, hC0, ?_⟩
  intro ε N y a b f _hε hεhalf hN hy hf hLhalf
  obtain ⟨hNa, hab, hb2N, hf2, hcls⟩ := hf
  set L : ℝ := y * N ^ (-s) with hL
  have hL0 : 0 < L := by positivity
  have hsL0 : 0 < Real.sqrt L := Real.sqrt_pos.2 hL0
  have hsN0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  have hf2' : ContDiff ℝ 2 f := by simpa using hf2

  have hd2 : ∀ t ∈ Set.Icc a b,
      |deriv (deriv f) t + s * y * t ^ (-s - 1)| ≤
        ε * (s * y * t ^ (-s - 1)) := by
    intro t ht
    have h := hcls 1 (by norm_num) t ht
    simp only [Finset.range_one, Finset.prod_singleton, Nat.cast_zero,
      add_zero, pow_one, Nat.cast_one, iteratedDeriv_succ,
      iteratedDeriv_zero] at h
    calc
      |deriv (deriv f) t + s * y * t ^ (-s - 1)| =
          |deriv (deriv f) t - -1 * s * y * t ^ (-s - 1)| := by ring_nf
      _ ≤ ε * s * y * t ^ (-s - 1) := h.le
      _ = ε * (s * y * t ^ (-s - 1)) := by ring

  set A := ⌊a⌋₊ with hA
  set B := ⌊b⌋₊ with hB
  have hrange : intRange a b = Finset.Ioc A B := rfl
  have ha0 : 0 ≤ a := by linarith
  have haA : a < A + 1 := Nat.lt_floor_add_one a
  have hBb : (B : ℝ) ≤ b := Nat.floor_le (by linarith)
  have hsub : Set.Icc (A + 1 : ℝ) B ⊆ Set.Icc a b :=
    Set.Icc_subset_Icc haA.le hBb
  have hBA : ((B - A : ℕ) : ℝ) ≤ 3 * N := by
    have h := card_intRange_le hN hNa hab hb2N
    rwa [intRange, Nat.card_Ioc] at h

  rw [hrange]
  set lam2 : ℝ := κ ^ 2 * L / N with hlam2
  have hlam2pos : 0 < lam2 := by positivity
  have hpow : ∀ t ∈ Set.Icc a b,
      lam2 ≤ 1 / 2 * (s * y * t ^ (-s - 1)) ∧
        3 / 2 * (s * y * t ^ (-s - 1)) ≤ α * lam2 := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le hN (hNa.trans ht.1)
    have htN : N ≤ t := hNa.trans ht.1
    have ht2N : t ≤ 2 * N := ht.2.trans hb2N
    have h1 : (2 * N) ^ (-s - 1) ≤ t ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
    have h2 : t ^ (-s - 1) ≤ N ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
    have hsy : 0 < s * y := by positivity
    have hsplit : (2 * N) ^ (-s - 1) =
        (2 : ℝ) ^ (-(s + 1)) * N ^ (-s - 1) := by
      rw [Real.mul_rpow (by norm_num) hN.le]
      congr 1
      congr 1
      ring
    have hNs : N ^ (-s - 1) = N ^ (-s) * N⁻¹ := by
      rw [show (-s - 1 : ℝ) = -s + (-1) by ring,
        Real.rpow_add hN, Real.rpow_neg_one]
    have hlam2' : lam2 =
        1 / 2 * (s * y * (2 * N) ^ (-s - 1)) := by
      rw [hlam2, hκ2, hsplit, hNs, hL]
      ring
    have h2pow : (2 : ℝ) ^ (s + 1) * (2 : ℝ) ^ (-(s + 1)) = 1 := by
      rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
    constructor
    · rw [hlam2']
      have h := mul_le_mul_of_nonneg_left h1 hsy.le
      linarith
    · rw [hlam2', hα, hsplit]
      have h := mul_le_mul_of_nonneg_left h2 hsy.le
      calc
        3 / 2 * (s * y * t ^ (-s - 1)) ≤
            3 / 2 * (s * y * N ^ (-s - 1)) := by linarith
        _ = 3 * 2 ^ (s + 1) *
            (1 / 2 * (s * y * (2 ^ (-(s + 1)) * N ^ (-s - 1)))) := by
          have he : 3 / 2 * (s * y * N ^ (-s - 1)) =
              3 * (2 ^ (s + 1) * 2 ^ (-(s + 1))) *
                (1 / 2 * (s * y * N ^ (-s - 1))) := by
            rw [h2pow]
            ring
          rw [he]
          ring

  have hsqrt : Real.sqrt lam2 = κ * Real.sqrt L / Real.sqrt N := by
    rw [hlam2, Real.sqrt_div (by positivity),
      Real.sqrt_mul (by positivity), Real.sqrt_sq hκ0.le]
  have hC1 : 36 * α * κ + 48 / κ ≤ C := by
    rw [hC]
    have : 0 ≤ 6 * κ := by positivity
    linarith
  have hC2 : 6 * κ ≤ C := by
    rw [hC]
    have : 0 ≤ 36 * α * κ := by positivity
    have : 0 ≤ 48 / κ := by positivity
    linarith
  have hinvL : 1 / Real.sqrt L ≤ 2 * Real.sqrt L := by
    rw [div_le_iff₀ hsL0]
    have h := Real.mul_self_sqrt hL0.le
    nlinarith

  rcases le_or_gt lam2 (1 / 4) with hsmall | hbig
  · have hg2 := Lemma1.deriv2_neg f
    have hvdc := VdC.second_derivative (fun t => -f t) hf2'.neg A B
      lam2 α hlam2pos hsmall hα0 fun t ht => by
        rw [hg2]
        simp only
        have hb := hd2 t (hsub ht)
        have hp := hpow t (hsub ht)
        rw [abs_le] at hb
        have ht0 : 0 < t :=
          lt_of_lt_of_le hN (hNa.trans (hsub ht).1)
        have hbase : 0 ≤ s * y * t ^ (-s - 1) := by positivity
        have hεbase : ε * (s * y * t ^ (-s - 1)) ≤
            1 / 2 * (s * y * t ^ (-s - 1)) :=
          mul_le_mul_of_nonneg_right hεhalf.le hbase
        constructor <;> linarith [hb.1, hb.2, hp.1, hp.2, hεbase]
    rw [Lemma1.norm_sum_e_neg] at hvdc
    have hterm1 :
        12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 ≤
          36 * α * κ * (Real.sqrt L * Real.sqrt N) := by
      rw [hsqrt]
      have hNsqrt : N / Real.sqrt N = Real.sqrt N := by
        rw [div_eq_iff hsN0.ne']
        exact (Real.mul_self_sqrt hN.le).symm
      calc
        12 * α * ((B - A : ℕ) : ℝ) *
            (κ * Real.sqrt L / Real.sqrt N) ≤
            12 * α * (3 * N) *
              (κ * Real.sqrt L / Real.sqrt N) := by gcongr
        _ = 36 * α * κ * Real.sqrt L * (N / Real.sqrt N) := by ring
        _ = 36 * α * κ * (Real.sqrt L * Real.sqrt N) := by
          rw [hNsqrt]
          ring
    have hterm2 : 24 / Real.sqrt lam2 ≤
        48 / κ * (Real.sqrt L * Real.sqrt N) := by
      rw [hsqrt]
      have he : 24 / (κ * Real.sqrt L / Real.sqrt N) =
          24 / κ * Real.sqrt N * (1 / Real.sqrt L) := by
        field_simp
      rw [he]
      calc
        24 / κ * Real.sqrt N * (1 / Real.sqrt L) ≤
            24 / κ * Real.sqrt N * (2 * Real.sqrt L) :=
          mul_le_mul_of_nonneg_left hinvL (by positivity)
        _ = 48 / κ * (Real.sqrt L * Real.sqrt N) := by ring
    calc
      ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤
          12 * α * ((B - A : ℕ) : ℝ) * Real.sqrt lam2 +
            24 / Real.sqrt lam2 := hvdc
      _ ≤ (36 * α * κ + 48 / κ) *
          (Real.sqrt L * Real.sqrt N) := by
        rw [add_mul]
        exact add_le_add hterm1 hterm2
      _ ≤ C * (Real.sqrt L * Real.sqrt N) :=
        mul_le_mul_of_nonneg_right hC1 (by positivity)
  · have hcard : ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤
        ((B - A : ℕ) : ℝ) := by
      calc
        ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤
            ∑ n ∈ Finset.Ioc A B, ‖e (f n)‖ := norm_sum_le _ _
        _ = ((B - A : ℕ) : ℝ) := by simp [norm_e]
    have hN4 : N < 4 * κ ^ 2 * L := by
      rw [hlam2, lt_div_iff₀ hN] at hbig
      linarith
    have hsqN : Real.sqrt N ≤ 2 * κ * Real.sqrt L := by
      have h : Real.sqrt N ≤ Real.sqrt (4 * κ ^ 2 * L) :=
        Real.sqrt_le_sqrt hN4.le
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
        Real.sqrt_sq hκ0.le,
        show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
            Real.sqrt_sq (by norm_num)]] at h
      linarith
    calc
      ‖∑ n ∈ Finset.Ioc A B, e (f n)‖ ≤
          ((B - A : ℕ) : ℝ) := hcard
      _ ≤ 3 * N := hBA
      _ = 3 * (Real.sqrt N * Real.sqrt N) := by
        rw [Real.mul_self_sqrt hN.le]
      _ ≤ 3 * ((2 * κ * Real.sqrt L) * Real.sqrt N) := by gcongr
      _ = 6 * κ * (Real.sqrt L * Real.sqrt N) := by ring
      _ ≤ C * (Real.sqrt L * Real.sqrt N) :=
        mul_le_mul_of_nonneg_right hC2 (by positivity)

end LeanProofs.IntegerPoints

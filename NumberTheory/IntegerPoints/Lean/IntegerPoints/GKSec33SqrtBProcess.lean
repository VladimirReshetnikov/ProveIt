import IntegerPoints.GKLemma36
import IntegerPoints.GKSec33SqrtPhase

/-!
# Graham--Kolesnik section 3.3: the square-root B-process

This module specializes Lemma 3.6 to the phase

`f(x) = 2 H R sqrt x`,  `H = Q^2`,  `N = R^2`,  `F = HN`.

Its derivative interval is exactly `[H / sqrt 2, H]`, and the stationary
point belonging to an integer frequency `nu` is `(HR / nu)^2`.  Besides the
specialized B-process bound, we record the endpoint derivatives, the
critical-point calculation, and the exact simplification of the dual
summand.  These are kept separate so that the later resonant lower-bound
argument need not reopen the analytic proof of Lemma 3.6.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

namespace GKSec33

/-! ### Scales and the dual sum -/

/-- The integral frequency scale `H = Q^2`, viewed as a real number. -/
def sqrtBH (Q : ℕ) : ℝ := (Q : ℝ) ^ 2

/-- The summation scale `N = R^2`, viewed as a real number. -/
def sqrtBN (R : ℕ) : ℝ := (R : ℝ) ^ 2

/-- The phase parameter `t = HR`. -/
def sqrtBT (Q R : ℕ) : ℝ := sqrtBH Q * (R : ℝ)

/-- The Lemma-3.6 curvature scale `F = HN`. -/
def sqrtBF (Q R : ℕ) : ℝ := sqrtBH Q * sqrtBN R

/-- The stationary point solving `f'(x) = nu` for the square-root phase. -/
noncomputable def sqrtCritical (t : ℝ) (ν : ℤ) : ℝ :=
  (t / (ν : ℝ)) ^ 2

/-- The square-root B-process main sum, with both its phase and curvature
already simplified at the stationary point. -/
noncomputable def sqrtBDualMain (Q R : ℕ) : ℂ :=
  ∑ ν ∈ Finset.Icc ⌈sqrtBH Q / Real.sqrt 2⌉ (Q ^ 2 : ℤ),
    e (sqrtBT Q R ^ 2 / (ν : ℝ) - 1 / 8) /
      ((Real.sqrt ((ν : ℝ) ^ 3 / (2 * sqrtBT Q R ^ 2)) : ℝ) : ℂ)

/-! ### Exact derivatives -/

/-- The first derivative of the smooth square-root phase on its unchanged
positive half-line. -/
theorem deriv_sqrtPhase_eq_div_sqrt (t x : ℝ) (hx : 1 / 2 < x) :
    deriv (sqrtPhase t) x = t / Real.sqrt x := by
  have h := iteratedDeriv_sqrtPhase t x 0 hx
  simp only [Nat.zero_add, pow_zero, Finset.range_zero, Finset.prod_empty,
    one_mul, Nat.cast_zero, sub_zero, iteratedDeriv_one] at h
  calc
    deriv (sqrtPhase t) x = t * x ^ (-(1 / 2 : ℝ)) := h
    _ = t / Real.sqrt x := by
      rw [Real.rpow_neg (le_of_lt (lt_trans (by norm_num) hx)),
        Real.sqrt_eq_rpow, div_eq_mul_inv]
      congr 2

/-- Rewriting the `-3/2` power as the reciprocal of `x sqrt x`. -/
theorem rpow_neg_three_halves_eq_inv_mul_sqrt {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 2 : ℝ)) = (x * Real.sqrt x)⁻¹ := by
  calc
    x ^ (-(3 / 2 : ℝ)) = x ^ (-(1 + 1 / 2 : ℝ)) := by
      congr 1
      ring
    _ = (x ^ (1 + 1 / 2 : ℝ))⁻¹ := Real.rpow_neg hx.le _
    _ = (x ^ (1 : ℝ) * x ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.rpow_add hx]
    _ = (x * Real.sqrt x)⁻¹ := by
      rw [Real.rpow_one, ← Real.sqrt_eq_rpow]

/-- Exact second derivative of the smooth square-root phase. -/
theorem iteratedDeriv_two_sqrtPhase (t x : ℝ) (hx : 1 / 2 < x) :
    iteratedDeriv 2 (sqrtPhase t) x =
      -((1 / 2 : ℝ) * t * x ^ (-(3 / 2 : ℝ))) := by
  have h := iteratedDeriv_sqrtPhase t x 1 hx
  norm_num [Finset.prod_range_succ] at h
  exact h

/-- Exact third derivative of the smooth square-root phase. -/
theorem iteratedDeriv_three_sqrtPhase (t x : ℝ) (hx : 1 / 2 < x) :
    iteratedDeriv 3 (sqrtPhase t) x =
      (3 / 4 : ℝ) * t * x ^ (-(5 / 2 : ℝ)) := by
  have h := iteratedDeriv_sqrtPhase t x 2 hx
  norm_num [Finset.prod_range_succ] at h
  exact h

/-- Exact fourth derivative of the smooth square-root phase. -/
theorem iteratedDeriv_four_sqrtPhase (t x : ℝ) (hx : 1 / 2 < x) :
    iteratedDeriv 4 (sqrtPhase t) x =
      -((15 / 8 : ℝ) * t * x ^ (-(7 / 2 : ℝ))) := by
  have h := iteratedDeriv_sqrtPhase t x 3 hx
  norm_num [Finset.prod_range_succ] at h
  exact h

/-- Multiplying the phase scale by the missing square root converts each
half-integral derivative scale into the integral scale used by Lemma 3.6. -/
theorem sqrtScale_rpow {N t F p : ℝ} (hN : 0 < N)
    (hF : F = t * Real.sqrt N) :
    t * N ^ (-(1 / 2 : ℝ) - p) = F * N ^ (-(1 + p)) := by
  rw [hF, Real.sqrt_eq_rpow]
  calc
    t * N ^ (-(1 / 2 : ℝ) - p) =
        t * N ^ ((1 / 2 : ℝ) + -(1 + p)) := by
      congr 2
      ring
    _ = t * (N ^ (1 / 2 : ℝ) * N ^ (-(1 + p))) := by
      rw [Real.rpow_add hN]
    _ = (t * N ^ (1 / 2 : ℝ)) * N ^ (-(1 + p)) := by ring

/-- On `[N,2N]`, the negative `3/2` power is at least one quarter of its
value at `N`.  The deliberately rational constant avoids introducing a
square-root constant into the derivative hypotheses of Lemma 3.6. -/
theorem quarter_rpow_neg_three_halves_le {N x : ℝ} (hN : 0 < N)
    (hx : x ∈ Set.Icc N (2 * N)) :
    (1 / 4 : ℝ) * N ^ (-(3 / 2 : ℝ)) ≤ x ^ (-(3 / 2 : ℝ)) := by
  have hx0 : 0 < x := hN.trans_le hx.1
  have hsqrt : Real.sqrt x ≤ 2 * Real.sqrt N := by
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num)
    calc
      Real.sqrt x ≤ Real.sqrt (4 * N) :=
        Real.sqrt_le_sqrt (by linarith [hx.2])
      _ = Real.sqrt 4 * Real.sqrt N := Real.sqrt_mul (by norm_num) N
      _ = 2 * Real.sqrt N := by
        rw [hsqrt4]
  have hden : x * Real.sqrt x ≤ 4 * (N * Real.sqrt N) := by
    calc
      x * Real.sqrt x ≤ (2 * N) * (2 * Real.sqrt N) :=
        mul_le_mul hx.2 hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = 4 * (N * Real.sqrt N) := by ring
  have hden0 : 0 < x * Real.sqrt x := by positivity
  have hinv : 1 / (4 * (N * Real.sqrt N)) ≤ 1 / (x * Real.sqrt x) :=
    one_div_le_one_div_of_le hden0 hden
  rw [rpow_neg_three_halves_eq_inv_mul_sqrt hN,
    rpow_neg_three_halves_eq_inv_mul_sqrt hx0]
  calc
    (1 / 4 : ℝ) * (N * Real.sqrt N)⁻¹ =
        1 / (4 * (N * Real.sqrt N)) := by
      field_simp [hN.ne', (Real.sqrt_pos.2 hN).ne']
    _ ≤ 1 / (x * Real.sqrt x) := hinv
    _ = (x * Real.sqrt x)⁻¹ := by rw [one_div]

/-! ### Lemma-3.6 hypotheses -/

/-- Uniform derivative bounds for the square-root phase on `[N,2N]`, in
the exact normalization expected by Lemma 3.6. -/
theorem sqrtPhase_gk36_derivative_bounds {N t F : ℝ}
    (hN : 1 / 2 < N) (ht : 0 < t) (hF : F = t * Real.sqrt N) :
    (∀ x ∈ Set.Icc N (2 * N),
      (1 / 8 : ℝ) * F * N ^ (-(2 : ℝ)) ≤
          -iteratedDeriv 2 (sqrtPhase t) x ∧
        -iteratedDeriv 2 (sqrtPhase t) x ≤
          (1 / 2 : ℝ) * F * N ^ (-(2 : ℝ))) ∧
    (∀ x ∈ Set.Icc N (2 * N),
      |iteratedDeriv 3 (sqrtPhase t) x| ≤
        (3 / 4 : ℝ) * F * N ^ (-(3 : ℝ))) ∧
    (∀ x ∈ Set.Icc N (2 * N),
      |iteratedDeriv 4 (sqrtPhase t) x| ≤
        (15 / 8 : ℝ) * F * N ^ (-(4 : ℝ))) := by
  have hN0 : 0 < N := lt_trans (by norm_num) hN
  have hscale2 :
      t * N ^ (-(3 / 2 : ℝ)) = F * N ^ (-(2 : ℝ)) := by
    have hs := sqrtScale_rpow hN0 hF (p := (1 : ℝ))
    convert hs using 1
    all_goals norm_num
  have hscale3 :
      t * N ^ (-(5 / 2 : ℝ)) = F * N ^ (-(3 : ℝ)) := by
    have hs := sqrtScale_rpow hN0 hF (p := (2 : ℝ))
    convert hs using 1
    all_goals norm_num
  have hscale4 :
      t * N ^ (-(7 / 2 : ℝ)) = F * N ^ (-(4 : ℝ)) := by
    have hs := sqrtScale_rpow hN0 hF (p := (3 : ℝ))
    convert hs using 1
    all_goals norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hxhalf : 1 / 2 < x := hN.trans_le hx.1
    have hx0 : 0 < x := hN0.trans_le hx.1
    have hpow0 : 0 < x ^ (-(3 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hlower := quarter_rpow_neg_three_halves_le hN0 hx
    have hupper : x ^ (-(3 / 2 : ℝ)) ≤ N ^ (-(3 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 hx.1 (by norm_num)
    rw [iteratedDeriv_two_sqrtPhase t x hxhalf, neg_neg]
    constructor
    · calc
        (1 / 8 : ℝ) * F * N ^ (-(2 : ℝ)) =
            (1 / 8 : ℝ) * (F * N ^ (-(2 : ℝ))) := by ring
        _ = (1 / 8 : ℝ) * (t * N ^ (-(3 / 2 : ℝ))) := by
          rw [hscale2]
        _ =
            (1 / 2 : ℝ) * t * ((1 / 4 : ℝ) * N ^ (-(3 / 2 : ℝ))) := by
          ring
        _ ≤ (1 / 2 : ℝ) * t * x ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlower (by positivity)
    · calc
        (1 / 2 : ℝ) * t * x ^ (-(3 / 2 : ℝ)) ≤
            (1 / 2 : ℝ) * t * N ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hupper (by positivity)
        _ = (1 / 2 : ℝ) * (t * N ^ (-(3 / 2 : ℝ))) := by ring
        _ = (1 / 2 : ℝ) * (F * N ^ (-(2 : ℝ))) := by
          rw [hscale2]
        _ = (1 / 2 : ℝ) * F * N ^ (-(2 : ℝ)) := by ring
  · intro x hx
    have hxhalf : 1 / 2 < x := hN.trans_le hx.1
    have hx0 : 0 < x := hN0.trans_le hx.1
    have hpow0 : 0 < x ^ (-(5 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hupper : x ^ (-(5 / 2 : ℝ)) ≤ N ^ (-(5 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 hx.1 (by norm_num)
    rw [iteratedDeriv_three_sqrtPhase t x hxhalf,
      abs_of_pos (by positivity)]
    calc
      (3 / 4 : ℝ) * t * x ^ (-(5 / 2 : ℝ)) ≤
          (3 / 4 : ℝ) * t * N ^ (-(5 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = (3 / 4 : ℝ) * (t * N ^ (-(5 / 2 : ℝ))) := by ring
      _ = (3 / 4 : ℝ) * (F * N ^ (-(3 : ℝ))) := by
        rw [hscale3]
      _ = (3 / 4 : ℝ) * F * N ^ (-(3 : ℝ)) := by ring
  · intro x hx
    have hxhalf : 1 / 2 < x := hN.trans_le hx.1
    have hx0 : 0 < x := hN0.trans_le hx.1
    have hpow0 : 0 < x ^ (-(7 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hupper : x ^ (-(7 / 2 : ℝ)) ≤ N ^ (-(7 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hN0 hx.1 (by norm_num)
    rw [iteratedDeriv_four_sqrtPhase t x hxhalf, abs_neg,
      abs_of_pos (by positivity)]
    calc
      (15 / 8 : ℝ) * t * x ^ (-(7 / 2 : ℝ)) ≤
          (15 / 8 : ℝ) * t * N ^ (-(7 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hupper (by positivity)
      _ = (15 / 8 : ℝ) * (t * N ^ (-(7 / 2 : ℝ))) := by ring
      _ = (15 / 8 : ℝ) * (F * N ^ (-(4 : ℝ))) := by
        rw [hscale4]
      _ = (15 / 8 : ℝ) * F * N ^ (-(4 : ℝ)) := by ring

/-- The two endpoint derivatives are exactly `H` and `H / sqrt 2`. -/
theorem sqrtPhase_endpoint_derivs {Q R : ℕ} (hQ : 0 < Q) (hR : 0 < R) :
    deriv (sqrtPhase (sqrtBT Q R)) (sqrtBN R) = sqrtBH Q ∧
      deriv (sqrtPhase (sqrtBT Q R)) (2 * sqrtBN R) =
        sqrtBH Q / Real.sqrt 2 := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hNhalf : 1 / 2 < sqrtBN R := by
    rw [sqrtBN]
    nlinarith [sq_nonneg ((R : ℝ) - 1)]
  have h2Nhalf : 1 / 2 < 2 * sqrtBN R := hNhalf.trans (by linarith)
  constructor
  · rw [deriv_sqrtPhase_eq_div_sqrt _ _ hNhalf]
    simp only [sqrtBT, sqrtBN, sqrtBH]
    rw [Real.sqrt_sq hR0.le]
    field_simp [hR0.ne']
  · rw [deriv_sqrtPhase_eq_div_sqrt _ _ h2Nhalf]
    have hsqrt : Real.sqrt (2 * sqrtBN R) =
        Real.sqrt 2 * (R : ℝ) := by
      rw [sqrtBN, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_sq hR0.le]
    rw [hsqrt]
    simp only [sqrtBT, sqrtBH]
    field_simp [hR0.ne', (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']

/-! ### Critical points and the simplified summand -/

/-- The explicit stationary point lies in `[N,2N]` and has derivative
exactly `nu` whenever `nu` lies between the endpoint derivatives. -/
theorem sqrtCritical_spec {N t : ℝ} {ν : ℤ} (hN : 1 / 2 < N) (ht : 0 < t)
    (hνlo : t / Real.sqrt (2 * N) ≤ (ν : ℝ))
    (hνhi : (ν : ℝ) ≤ t / Real.sqrt N) :
    sqrtCritical t ν ∈ Set.Icc N (2 * N) ∧
      deriv (sqrtPhase t) (sqrtCritical t ν) = (ν : ℝ) := by
  have hN0 : 0 < N := lt_trans (by norm_num) hN
  have h2N0 : 0 < 2 * N := by positivity
  have hsN0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hs2N0 : 0 < Real.sqrt (2 * N) := Real.sqrt_pos.2 h2N0
  have hν0 : (0 : ℝ) < ν := (div_pos ht hs2N0).trans_le hνlo
  have hquot0 : 0 < t / (ν : ℝ) := div_pos ht hν0
  have hsNle : Real.sqrt N ≤ t / (ν : ℝ) := by
    rw [le_div_iff₀ hν0]
    have := (le_div_iff₀ hsN0).1 hνhi
    simpa [mul_comm] using this
  have hquotle : t / (ν : ℝ) ≤ Real.sqrt (2 * N) := by
    rw [div_le_iff₀ hν0]
    have := (div_le_iff₀ hs2N0).1 hνlo
    simpa [mul_comm] using this
  have hxmem : sqrtCritical t ν ∈ Set.Icc N (2 * N) := by
    unfold sqrtCritical
    constructor
    · calc
        N = (Real.sqrt N) ^ 2 := (Real.sq_sqrt hN0.le).symm
        _ ≤ (t / (ν : ℝ)) ^ 2 :=
          (sq_le_sq₀ (Real.sqrt_nonneg N) hquot0.le).2 hsNle
    · calc
        (t / (ν : ℝ)) ^ 2 ≤ (Real.sqrt (2 * N)) ^ 2 :=
          (sq_le_sq₀ hquot0.le (Real.sqrt_nonneg _)).2 hquotle
        _ = 2 * N := Real.sq_sqrt h2N0.le
  refine ⟨hxmem, ?_⟩
  rw [deriv_sqrtPhase_eq_div_sqrt _ _ (hN.trans_le hxmem.1)]
  unfold sqrtCritical
  rw [Real.sqrt_sq hquot0.le]
  field_simp [ht.ne', hν0.ne']

/-- The stationary phase is exactly `t^2 / nu`. -/
theorem sqrtCritical_phase {t : ℝ} {ν : ℤ} (ht : 0 < t)
    (hν : (0 : ℝ) < ν) (hx : 1 / 2 < sqrtCritical t ν) :
    sqrtPhase t (sqrtCritical t ν) - (ν : ℝ) * sqrtCritical t ν =
      t ^ 2 / (ν : ℝ) := by
  have hquot0 : 0 < t / (ν : ℝ) := div_pos ht hν
  unfold sqrtCritical at hx ⊢
  unfold sqrtPhase
  rw [L9.hfun_eq hx.le, Real.sqrt_sq hquot0.le]
  field_simp [hν.ne']
  ring

/-- The absolute curvature at the stationary point is exactly
`nu^3 / (2t^2)`. -/
theorem sqrtCritical_curvature {t : ℝ} {ν : ℤ} (ht : 0 < t)
    (hν : (0 : ℝ) < ν) (hx : 1 / 2 < sqrtCritical t ν) :
    |iteratedDeriv 2 (sqrtPhase t) (sqrtCritical t ν)| =
      (ν : ℝ) ^ 3 / (2 * t ^ 2) := by
  have hquot0 : 0 < t / (ν : ℝ) := div_pos ht hν
  have hderiv : iteratedDeriv 2 (sqrtPhase t) (sqrtCritical t ν) =
      -((ν : ℝ) ^ 3 / (2 * t ^ 2)) := by
    rw [iteratedDeriv_two_sqrtPhase t _ hx]
    unfold sqrtCritical
    rw [rpow_neg_three_halves_eq_inv_mul_sqrt (sq_pos_of_pos hquot0),
      Real.sqrt_sq hquot0.le]
    field_simp [ht.ne', hν.ne']
  rw [hderiv, abs_neg, abs_of_pos]
  positivity

/-- The stationary summand in Lemma 3.6 agrees with the explicit dual
summand used by `sqrtBDualMain`. -/
theorem sqrtCritical_main_term {N t : ℝ} {ν : ℤ} (hN : 1 / 2 < N)
    (ht : 0 < t) (hνlo : t / Real.sqrt (2 * N) ≤ (ν : ℝ))
    (hνhi : (ν : ℝ) ≤ t / Real.sqrt N) :
    e (sqrtPhase t (sqrtCritical t ν) -
          (ν : ℝ) * sqrtCritical t ν - 1 / 8) /
        ((Real.sqrt
          |iteratedDeriv 2 (sqrtPhase t) (sqrtCritical t ν)| : ℝ) : ℂ) =
      e (t ^ 2 / (ν : ℝ) - 1 / 8) /
        ((Real.sqrt ((ν : ℝ) ^ 3 / (2 * t ^ 2)) : ℝ) : ℂ) := by
  obtain ⟨hxmem, _⟩ := sqrtCritical_spec hN ht hνlo hνhi
  have h2N0 : 0 < 2 * N := by linarith
  have hν : (0 : ℝ) < ν :=
    (div_pos ht (Real.sqrt_pos.2 h2N0)).trans_le hνlo
  rw [sqrtCritical_phase ht hν (hN.trans_le hxmem.1),
    sqrtCritical_curvature ht hν (hN.trans_le hxmem.1)]

/-! ### Scale simplification and the specialized B-process -/

/-- The two scales in the error term of Lemma 3.6 reduce exactly to `H`
and `R/Q`. -/
theorem sqrtB_error_scales {Q R : ℕ} (hQ : 0 < Q) (hR : 0 < R) :
    sqrtBF Q R * (sqrtBN R)⁻¹ = sqrtBH Q ∧
      sqrtBF Q R ^ (-(1 : ℝ) / 2) * sqrtBN R =
        (R : ℝ) / (Q : ℝ) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hF0 : 0 < sqrtBF Q R := by
    simp only [sqrtBF, sqrtBH, sqrtBN]
    positivity
  constructor
  · simp only [sqrtBF, sqrtBN]
    field_simp [hR0.ne']
  · have hsqrtF : Real.sqrt (sqrtBF Q R) = (Q : ℝ) * (R : ℝ) := by
      rw [sqrtBF, sqrtBH, sqrtBN, ← mul_pow,
        Real.sqrt_sq (mul_nonneg hQ0.le hR0.le)]
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hF0.le, ← Real.sqrt_eq_rpow, hsqrtF]
    simp only [sqrtBN]
    field_simp [hQ0.ne', hR0.ne']

/-- A nonnegative absolute constant gives the square-root B-process estimate
at the perfect-square scales `H = Q^2`, `N = R^2`, `t = HR`, `F = HN`.
The main sum has the exact stationary phase and curvature displayed in
`sqrtBDualMain`. -/
theorem exists_sqrtBProcess_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Q R : ℕ, 0 < Q → 0 < R →
      ‖(∑ n ∈ intRange (sqrtBN R) (2 * sqrtBN R),
          e (sqrtPhase (sqrtBT Q R) n)) - sqrtBDualMain Q R‖ ≤
        B * (Real.log (sqrtBH Q + 2) + (R : ℝ) / (Q : ℝ)) := by
  obtain ⟨C, hC⟩ := gk_lemma36_holds
    (1 / 8) (1 / 2) (3 / 4) (15 / 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro Q R hQ hR
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have hN0 : 0 < sqrtBN R := by simp [sqrtBN]; positivity
  have hNhalf : 1 / 2 < sqrtBN R := by
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
    rw [sqrtBN]
    nlinarith [sq_nonneg ((R : ℝ) - 1)]
  have hH0 : 0 < sqrtBH Q := by simp [sqrtBH]; positivity
  have ht0 : 0 < sqrtBT Q R := by simp [sqrtBT]; positivity
  have hF0 : 0 < sqrtBF Q R := by simp [sqrtBF]; positivity
  have hscale : sqrtBF Q R = sqrtBT Q R * Real.sqrt (sqrtBN R) := by
    rw [sqrtBF, sqrtBT, sqrtBN, Real.sqrt_sq hR0.le]
    ring
  obtain ⟨hd2, hd3, hd4⟩ :=
    sqrtPhase_gk36_derivative_bounds hNhalf ht0 hscale
  obtain ⟨hleft, hright⟩ := sqrtPhase_endpoint_derivs hQ hR
  have hleftScale :
      sqrtBT Q R / Real.sqrt (sqrtBN R) = sqrtBH Q := by
    calc
      sqrtBT Q R / Real.sqrt (sqrtBN R) =
          deriv (sqrtPhase (sqrtBT Q R)) (sqrtBN R) :=
        (deriv_sqrtPhase_eq_div_sqrt _ _ hNhalf).symm
      _ = sqrtBH Q := hleft
  have hrightScale :
      sqrtBT Q R / Real.sqrt (2 * sqrtBN R) =
        sqrtBH Q / Real.sqrt 2 := by
    calc
      sqrtBT Q R / Real.sqrt (2 * sqrtBN R) =
          deriv (sqrtPhase (sqrtBT Q R)) (2 * sqrtBN R) :=
        (deriv_sqrtPhase_eq_div_sqrt _ _ (hNhalf.trans (by linarith))).symm
      _ = sqrtBH Q / Real.sqrt 2 := hright
  have hcrit : ∀ ν : ℤ,
      deriv (sqrtPhase (sqrtBT Q R)) (2 * sqrtBN R) ≤ (ν : ℝ) →
      (ν : ℝ) ≤ deriv (sqrtPhase (sqrtBT Q R)) (sqrtBN R) →
      sqrtCritical (sqrtBT Q R) ν ∈ Set.Icc (sqrtBN R) (2 * sqrtBN R) ∧
        deriv (sqrtPhase (sqrtBT Q R))
          (sqrtCritical (sqrtBT Q R) ν) = (ν : ℝ) := by
    intro ν hνlo hνhi
    apply sqrtCritical_spec hNhalf ht0
    · rw [hrightScale]
      simpa [hright] using hνlo
    · rw [hleftScale]
      simpa [hleft] using hνhi
  have hbound := hC (sqrtBN R) (sqrtBF Q R) (sqrtBN R)
    (2 * sqrtBN R) (sqrtPhase (sqrtBT Q R))
    (sqrtCritical (sqrtBT Q R)) hN0 hF0 le_rfl (by linarith)
    le_rfl (sqrtPhase_contDiff_nat (sqrtBT Q R) 4) hd2 hd3 hd4 hcrit
  have hfloor : ⌊sqrtBH Q⌋ = (Q ^ 2 : ℤ) := by
    rw [sqrtBH, ← Nat.cast_pow, Int.floor_natCast]
    norm_cast
  have hmain :
      (∑ ν ∈ Finset.Icc
          ⌈deriv (sqrtPhase (sqrtBT Q R)) (2 * sqrtBN R)⌉
          ⌊deriv (sqrtPhase (sqrtBT Q R)) (sqrtBN R)⌋,
        e (sqrtPhase (sqrtBT Q R) (sqrtCritical (sqrtBT Q R) ν) -
              (ν : ℝ) * sqrtCritical (sqrtBT Q R) ν - 1 / 8) /
          ((Real.sqrt
            |iteratedDeriv 2 (sqrtPhase (sqrtBT Q R))
              (sqrtCritical (sqrtBT Q R) ν)| : ℝ) : ℂ)) =
        sqrtBDualMain Q R := by
    rw [hright, hleft, hfloor]
    unfold sqrtBDualMain
    apply Finset.sum_congr rfl
    intro ν hν
    have hν' := hν
    simp only [Finset.mem_Icc] at hν'
    have hνlo : sqrtBT Q R / Real.sqrt (2 * sqrtBN R) ≤ (ν : ℝ) := by
      calc
        sqrtBT Q R / Real.sqrt (2 * sqrtBN R) =
            sqrtBH Q / Real.sqrt 2 := by
          have hsqrt : Real.sqrt (2 * sqrtBN R) =
              Real.sqrt 2 * (R : ℝ) := by
            rw [sqrtBN, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
              Real.sqrt_sq hR0.le]
          rw [hsqrt, sqrtBT]
          field_simp [hR0.ne',
            (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']
        _ ≤ (⌈sqrtBH Q / Real.sqrt 2⌉ : ℤ) := Int.le_ceil _
        _ ≤ (ν : ℝ) := by exact_mod_cast hν'.1
    have hνhi : (ν : ℝ) ≤
        sqrtBT Q R / Real.sqrt (sqrtBN R) := by
      calc
        (ν : ℝ) ≤ (Q ^ 2 : ℤ) := by exact_mod_cast hν'.2
        _ = sqrtBH Q := by simp [sqrtBH]
        _ = sqrtBT Q R / Real.sqrt (sqrtBN R) := by
          rw [sqrtBT, sqrtBN, Real.sqrt_sq hR0.le]
          field_simp [hR0.ne']
    exact sqrtCritical_main_term hNhalf ht0 hνlo hνhi
  obtain ⟨hscaleLog, hscaleTime⟩ := sqrtB_error_scales hQ hR
  rw [hmain, hscaleLog, hscaleTime] at hbound
  have hfactor0 :
      0 ≤ Real.log (sqrtBH Q + 2) + (R : ℝ) / (Q : ℝ) := by
    exact add_nonneg (Real.log_nonneg (by linarith [hH0]))
      (div_nonneg hR0.le hQ0.le)
  exact hbound.trans
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hfactor0)

end GKSec33

end LeanProofs.IntegerPoints

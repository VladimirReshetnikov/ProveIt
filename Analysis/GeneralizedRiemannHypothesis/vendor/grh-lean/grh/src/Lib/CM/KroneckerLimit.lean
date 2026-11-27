import Lib.CM.Sigma.Basic

/-!
# Kronecker's first limit formula

`New.kronecker_limit` computes the first two terms at `s = 1` of the Epstein zeta function of a
lattice in `ℂ`, in terms of its area and of the discriminant `g₂³ - 27 g₃²`. The Epstein function is
not continued analytically: only real `s` with `1 < s < 2` occur, and a right derivative at `1`.

For the lattice `ℤ τ + ℤ`, each row `∑ n, |m τ + n|^(-2s)` with `m ≥ 1` is compared with the
integral `∫ |m τ + t|^(-2s) dt` (`New.hasSum_shiftedTerm`). The errors `New.meanError` sum to a
function continuous on `[1, 2]`, the integrals to a multiple of `ζ(2s - 1)`, which has a simple pole
at 1. At `s = 1` the cotangent series expresses the errors through `log |∏ (1 - q ^ n)|`
(`New.tsum_meanError_one`).

Notions from other files:
* `PeriodPair.area`: The area |Im(ω̄₁ω₂)| of the fundamental parallelogram spanned by the periods
  ω₁, ω₂ of a period pair.

## Relation to the literature

Known result: Kronecker's first limit formula. Here the real limit from the right is proved for any
lattice and stated with the discriminant. Rows are compared with integrals by the mean value
theorem. Source: C. L. Siegel, Lectures on Advanced Analytic Number Theory (1961), Chapter I,
Theorem 1; for a proof of this shape, F. Chamizo, A simple evaluation of a theta value, the
Kronecker limit formula and a formula of Ramanujan, Ramanujan J. (2022), Prop. 3.1.
-/

open Complex Nat Equiv MeasureTheory Set Real Function Periodic ModularForm intervalIntegral

/-- The series `∑ m^(-s)` for real `s > 1`, in terms of the entire function `riemannZeta₀`, which is
`ζ(s) - 1 / (s - 1)` for `s ≠ 1`. -/
lemma New.hasSum_pnat_rpow_neg (s : ℝ) (hs : 1 < s) :
    HasSum (fun m : ℕ+ ↦ (m : ℝ) ^ (-s)) ((s - 1)⁻¹ + (riemannZeta₀ s).re) := by
  have h_pnat : HasSum (fun m : ℕ+ ↦ LSeries.term 1 s m) (riemannZeta s) :=
    hasSum_pnat_iff.mpr (by simpa [LSeriesHasSum] using LSeriesHasSum_one (s := s) (by simpa))
  -- take real parts, with `ζ s = 1 / (s - 1) + riemannZeta₀ s`
  simpa [riemannZeta_eq_inv_sub_add, hs.ne', ← rpow_neg, ← ofReal_natCast, comp_def,
    ← ofReal_cpow, normSq] using hasSum_re h_pnat

/-- For `a > 2`, `|a - b| ≤ 1` and `1 ≤ s ≤ 2`, the values of `t ↦ t^(-2s)` at `a` and `b` differ
by at most `4 (a / 2)^(-3)`, by the mean value theorem. -/
lemma New.norm_rpow_sub_rpow_le {a b s : ℝ} (ha : 2 < a) (hab : |a - b| ≤ 1) (hs : s ∈ Icc 1 2) :
    ‖a ^ (-2 * s) - b ^ (-2 * s)‖ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) := by
  obtain ⟨hs_one, hs_two⟩ := hs
  have h_pos (t : ℝ) (ht : t ∈ Ici (2⁻¹ * a)) : 0 < t := by linarith [mem_Ici.1 ht]
  have h_deriv (t : ℝ) (ht : t ∈ Ici (2⁻¹ * a)) :
      ‖-2 * s * t ^ (-2 * s - 1)‖ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) := by
    have h_pow : t ^ (-2 * s - 1) ≤ (2⁻¹ * a) ^ (-3 : ℝ) :=
      (rpow_le_rpow_of_nonpos (by linarith) ht (by linarith)).trans
        (rpow_le_rpow_of_exponent_le (by linarith) (by linarith))
    rw [norm_eq_abs, abs_mul, abs_of_pos (rpow_pos_of_pos (h_pos t ht) _)]
    exact mul_le_mul (abs_le.2 ⟨by linarith, by linarith⟩) h_pow
      (rpow_pos_of_pos (h_pos t ht) _).le (by norm_num)
  have hb_mem : b ∈ Ici (2⁻¹ * a) := mem_Ici.2 (by linarith [le_abs_self (a - b)])
  calc ‖a ^ (-2 * s) - b ^ (-2 * s)‖
    _ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) * ‖a - b‖ :=
      (convex_Ici (2⁻¹ * a)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := fun t ↦ t ^ (-2 * s))
        (fun t ht ↦ (hasDerivAt_rpow_const (.inl (h_pos t ht).ne')).hasDerivWithinAt) h_deriv
        hb_mem (mem_Ici.2 (by linarith))
    _ ≤ 4 * (2⁻¹ * a) ^ (-3 : ℝ) := mul_le_of_le_one_right (by positivity) hab

/-- The factor `√π Γ(s - 1/2) / Γ(s) * y^(1 - 2s)`. For `s > 1/2` it is the value of Euler's beta
integral `∫ |z + t|^(-2s) dt` over the real line when `im z = y > 0`. -/
noncomputable def New.betaFactor (y s : ℝ) : ℝ :=
  √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * y ^ (1 - 2 * s)

lemma New.betaFactor_one (y : ℝ) : betaFactor y 1 = π / y := by
  norm_num [betaFactor, Real.Gamma_one_half_eq, rpow_neg_one, pi_pos.le, div_eq_mul_inv]

/-- The derivative at `s = 1` of the value `√π Γ(s - 1/2) / Γ(s) * y^(1 - 2s)` of Euler's beta
integral; the Euler constants from `Γ'(1/2)` and `Γ'(1)` cancel. -/
lemma New.hasDerivAt_betaFactor {y : ℝ} (hy : 0 < y) :
    HasDerivAt (betaFactor y) (-2 * π / y * (Real.log 2 + Real.log y)) 1 := by
  have hΓ : HasDerivAt (fun s : ℝ ↦ Real.Gamma (s - 1 / 2))
      (-√π * (eulerMascheroniConstant + 2 * Real.log 2)) 1 :=
    HasDerivAt.comp_sub_const 1 (1 / 2) (by simpa only [sub_half] using
      Real.hasDerivAt_Gamma_one_half)
  have h_pow : HasDerivAt (fun x : ℝ ↦ y ^ (1 - 2 * x)) (Real.log y * -2 * y ^ ((1 : ℝ) - 2 * 1))
    1 := ((hasDerivAt_const_mul (x := 1) 2).const_sub 1).const_rpow hy
  unfold betaFactor
  refine (((hΓ.const_mul √π).div hasDerivAt_Gamma_one (by simp)).mul h_pow).congr_deriv ?_
  norm_num [Real.Gamma_one_half_eq, rpow_neg_one, ← mul_assoc, Real.mul_self_sqrt, pi_pos.le]
  field

/-- The powers `q^(j+1)` of `q = exp (2 π i (x + i y))` have modulus less than one for `y > 0`. -/
lemma New.norm_eta_q_lt_one {x y : ℝ} (hy : 0 < y) (j : ℕ) : ‖eta_q j ⟨x, y⟩‖ < 1 := by
  simp [pow_lt_one₀, norm_qParam_lt_one, hy]

/-- For `y > 0` and `q = exp (2 π i (x + i y))`, so that `eta_q m ⟨x, y⟩ = q^(m+1)`, the double
series `∑ q^((m+1)(j+1)) / (m+1)` converges absolutely, and it is minus a logarithm of
`∏ (1 - q^(j+1))`. -/
lemma New.tprod_one_sub_eta_q {x y : ℝ} (hy : 0 < y) :
    let c (m j : ℕ) : ℂ := eta_q m ⟨x, y⟩ ^ j.succ / ofReal m.succ
    Summable (uncurry c) ∧ ∏' j : ℕ, (1 - eta_q j ⟨x, y⟩) = cexp (-∑' m : ℕ, ∑' j : ℕ, c m j) := by
  intro c
  have hc : Summable (uncurry c) := by
    refine .of_norm_bounded ((summable_prod_mul_pow 0
      (norm_eta_q_lt_one (x := x) hy 0)).norm.comp_injective
        (succPNat_injective.prodMap succPNat_injective)) ?_
    simp [c, pow_mul, -cast_add]
    bound -- termwise: dividing by `m + 1` does not increase the modulus
  have h_log (j : ℕ) : ∑' m : ℕ, c m j = -Complex.log (1 - eta_q j ⟨x, y⟩) := by
    simp [c, (hasSum_taylorSeries_neg_log' (norm_eta_q_lt_one hy _)).tsum_eq, pow_right_comm]
  have h_sum : HasSum (fun j : ℕ ↦ Complex.log (1 - eta_q j ⟨x, y⟩))
      (-∑' m : ℕ, ∑' j : ℕ, c m j) := by
    rw [← hc.tsum_comm]
    exact hc.prod_symm.prod.hasSum.neg.congr_fun (by simp [h_log])
  exact ⟨hc, (hasProd_of_hasSum_log (one_sub_eta_q_ne_zero · hy) h_sum).tprod_eq⟩

/-- For `τ = x + i y` with `y > 0`, the series `∑ |m τ + n| ^ r` over `(m, n) ∈ ℤ²` converges for
`r < -2`; its term at `(0, 0)` is `0` in Lean. -/
lemma New.summable_norm_mul_add_rpow {x y r : ℝ} (hy : 0 < y) (hr : r < -2) :
    Summable fun p : ℤ × ℤ ↦ ‖p.1 * (⟨x, y⟩ : ℂ) + p.2‖ ^ r := by
  have h_vec : Summable fun v : Fin 2 → ℤ ↦ ‖v 0 * (⟨x, y⟩ : ℂ) + v 1‖ ^ (- -r) :=
    .of_nonneg_of_le (fun _ ↦ by positivity)
      (EisensteinSeries.summand_bound ⟨⟨x, y⟩, hy⟩ (by linarith))
      ((EisensteinSeries.summable_one_div_norm_rpow (by linarith)).mul_left _)
  simpa [comp_def] using (finTwoArrowEquiv ℤ).symm.summable_iff.2 h_vec

/-- The term `|m τ + n + u|^(-2s)`, for `τ = x + i y`, `p = (m, n)` and a real shift `u`. -/
noncomputable def New.shiftedTerm (x y : ℝ) (p : ℕ+ × ℤ) (s u : ℝ) : ℝ :=
  ‖p.1 * (⟨x, y⟩ : ℂ) + (ofReal u + p.2)‖ ^ (-2 * s)

/-- The term `|m τ + n|^(-2s)` minus the mean of `|m τ + n + u|^(-2s)` over `u ∈ [0, 1]`, for
`τ = x + i y` and `p = (m, n)`. -/
noncomputable def New.meanError (x y : ℝ) (p : ℕ+ × ℤ) (s : ℝ) : ℝ :=
  ∫ u in 0..1, shiftedTerm x y p s 0 - shiftedTerm x y p s u

lemma New.continuous_uncurry_shiftedTerm {x y : ℝ} (hy : 0 < y) (p : ℕ+ × ℤ) :
    Continuous (uncurry (shiftedTerm x y p)) :=
  .rpow (by fun_prop) (by fun_prop) fun _ ↦ .inl ((im_le_norm _).trans_lt' (by simpa)).ne'

lemma New.continuous_meanError {x y : ℝ} (hy : 0 < y) (p : ℕ+ × ℤ) :
    Continuous (meanError x y p) := by
  have := continuous_uncurry_shiftedTerm (x := x) hy p
  unfold meanError
  fun_prop

/-- The series of the errors `meanError x y p s` converges uniformly for `s ∈ [1, 2]`. -/
lemma New.tendstoUniformlyOn_sum_meanError {x y : ℝ} (hy : 0 < y) :
    TendstoUniformlyOn (fun (A : Finset (ℕ+ × ℤ)) (s : ℝ) ↦ ∑ p ∈ A, meanError x y p s)
      (fun s : ℝ ↦ ∑' p : ℕ+ × ℤ, meanError x y p s) .atTop (Icc 1 2) := by
  -- When `|m τ + n| > 2` (all but finitely many terms), the error is at most
  -- `4 (|m τ + n| / 2)^(-3)`.
  let w (p : ℕ+ × ℤ) (u : ℝ) : ℝ := ‖p.1 * (⟨x, y⟩ : ℂ) + (ofReal u + p.2)‖
  have h_major : Summable fun p : ℕ+ × ℤ ↦ (2⁻¹ * w p 0) ^ (-3 : ℝ) := by
    simpa [w, mul_pow] using ((summable_norm_mul_add_rpow hy (r := -3) (by norm_num)).comp_injective
      ((cast_injective.comp PNat.coe_injective).prodMap injective_id)).mul_right _
  have h_bound (p : ℕ+ × ℤ) (hp : (2⁻¹ * w p 0) ^ (-3 : ℝ) < 1) (s : ℝ) (hs : s ∈ Icc (1 : ℝ) 2) :
      ‖meanError x y p s‖ ≤ 4 * (2⁻¹ * w p 0) ^ (-3 : ℝ) * |1 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
    have h_far : 2 < w p 0 := by
      have h_pos : 0 < w p 0 := (im_le_norm _).trans_lt' (by simpa)
      by_contra h_near
      exact hp.not_ge (one_le_rpow_of_pos_of_le_one_of_nonpos (by positivity) (by linarith)
        (by norm_num))
    have h_close : |w p 0 - w p u| ≤ 1 :=
      (abs_norm_sub_norm_le _ _).trans (by simpa using (by grind [abs_le] : |u| ≤ 1))
    exact norm_rpow_sub_rpow_le h_far h_close hs
  exact tendstoUniformlyOn_tsum_of_cofinite_eventually ((h_major.mul_left 4).mul_right _)
    ((h_major.tendsto_cofinite_zero.eventually_lt_const one_pos).mono h_bound)

lemma New.summable_meanError {x y s : ℝ} (hy : 0 < y) (hs : s ∈ Icc (1 : ℝ) 2) :
    Summable fun p : ℕ+ × ℤ ↦ meanError x y p s :=
  HasSum.summable ((tendstoUniformlyOn_sum_meanError hy).tendsto_at hs)

lemma New.continuousOn_tsum_meanError {x y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun s : ℝ ↦ ∑' p : ℕ+ × ℤ, meanError x y p s) (Icc 1 2) :=
  (tendstoUniformlyOn_sum_meanError hy).continuousOn (.of_forall fun _ ↦
    (continuous_finsetSum _ fun p _ ↦ continuous_meanError hy p).continuousOn)

/-- Euler's beta integral along the row `m`: `∫ |m τ + t|^(-2s) dt` over the real line, where
`τ = x + i y`; it equals `betaFactor y s * m ^ (1 - 2s)`. -/
lemma New.integral_shiftedTerm {x y s : ℝ} (hy : 0 < y) (hs : 1 / 2 < s) (m : ℕ+) :
    ∫ t : ℝ, shiftedTerm x y (m, 0) s t = betaFactor y s * m ^ (1 - 2 * s) := by
  have : 0 < s := by linarith
  have : 0 < s - 1 / 2 := by linarith
  let z : ℂ := m * ⟨x, y⟩
  have hz_im : z.im = m * y := by simp [z]
  calc ∫ t : ℝ, shiftedTerm x y (m, 0) s t
    _ = ∫ t : ℝ, (ENNReal.ofReal (‖z + t‖ ^ (-2 * s))).toReal := by
      simp [shiftedTerm, z, rpow_nonneg]
    _ = (∫⁻ t : ℝ, ENNReal.ofReal (‖z + t‖ ^ (-2 * s))).toReal :=
      integral_toReal (by fun_prop) (by simp)
    _ = √π * Real.Gamma (s - 1 / 2) / Real.Gamma s * z.im ^ (-(2 * s - 1)) := by
      have hz_pos : 0 < z.im := by simpa [hz_im] using hy
      rw [lintegral_norm_add_rpow z hz_pos hs, ENNReal.toReal_ofReal (by positivity)]
    _ = betaFactor y s * m ^ (1 - 2 * s) := by
      rw [hz_im, neg_sub, mul_rpow (by positivity) hy.le, betaFactor]
      ring

/-- The row `∑ n, |m τ + n|^(-2s)` (for `τ = x + i y`) is the sum of its errors
`meanError x y (m, n) s` plus the beta integral `betaFactor y s * m ^ (1 - 2s)`. -/
lemma New.hasSum_shiftedTerm {x y s : ℝ} (hy : 0 < y) (hs : s ∈ Icc (1 : ℝ) 2) (m : ℕ+) :
    HasSum (fun n : ℤ ↦ shiftedTerm x y (m, n) s 0)
      (∑' n : ℤ, meanError x y (m, n) s + betaFactor y s * m ^ (1 - 2 * s)) := by
  -- Cutting `ℝ` into unit intervals turns the beta integral into the sum of the means.
  have hs_half : 1 / 2 < s := one_half_lt_one.trans_le hs.1
  -- the integral is nonzero, so the integrand is integrable
  have h_integrable : Integrable (shiftedTerm x y (m, 0) s) := by
    refine .of_integral_ne_zero ((integral_shiftedTerm hy hs_half m).trans_ne ?_)
    have : 0 < s - 1 / 2 := sub_pos.2 hs_half
    have : 0 < s := by linarith
    unfold betaFactor
    positivity
  have h_cut : HasSum (fun n : ℤ ↦ ∫ u in 0..1, shiftedTerm x y (m, n) s u)
      (betaFactor y s * m ^ (1 - 2 * s)) := by
    rw [← integral_shiftedTerm hy hs_half m]
    simpa [shiftedTerm] using h_integrable.hasSum_intervalIntegral_comp_add_int
  refine (((summable_meanError hy hs).prod_factor m).hasSum.add h_cut).congr_fun fun n ↦ ?_
  rw [meanError, intervalIntegral.integral_sub intervalIntegrable_const
    (((continuous_uncurry_shiftedTerm hy (m, n)).uncurry_left s).intervalIntegrable 0 1)]
  simp

/-- Let `τ = x + i y` with `y > 0`, and fix the row `m + 1`. The errors `meanError x y (m + 1, n) 1`
are `|(m+1) τ + n|^(-2)` minus the mean of `|(m+1) τ + n + u|^(-2)` over `u ∈ [0, 1]`. Their sum
over `n : ℤ` is `2 π / y` times the real part of `∑ j, q^((m+1)(j+1)) / (m+1)`, where
`q = exp (2 π i τ)`, so that `eta_q m τ = q^(m+1)`. -/
lemma New.tsum_meanError_row_one {x y : ℝ} (hy : 0 < y) (m : ℕ) :
    ∑' n : ℤ, meanError x y (m.succPNat, n) 1 =
      2 * π / y * (∑' j : ℕ, eta_q m ⟨x, y⟩ ^ j.succ / ofReal m.succ).re := by
  -- For `z = (m+1) τ`, `im (1 / (z - n) + 1 / (z + n)) = -im z * (|z - n|⁻² + |z + n|⁻²)`, so
  -- `-im z` times the row is the imaginary part of the partial fractions of `π cot (π z)`.
  let z : UpperHalfPlane := ⟨m.succ * ⟨x, y⟩, by simpa [-cast_add]⟩
  let F (n : ℤ) : ℝ := shiftedTerm x y (m.succPNat, n) 1 0
  let S : ℝ := ∑' n : ℤ, meanError x y (m.succPNat, n) 1
  have h_row : HasSum F (S + π / y * m.succPNat ^ (1 - 2 * 1 : ℝ)) := by
    rw [← betaFactor_one]
    exact hasSum_shiftedTerm hy (by simp) m.succPNat
  have h_pairs : HasSum (fun n : ℕ ↦ F ↑(n + 1) + F (-↑(n + 1)))
      (S + π / y * m.succPNat ^ (1 - 2 * 1 : ℝ) - F 0) := by
    simpa [sub_eq_add_neg] using (hasSum_nat_add_iff' 1).2 h_row.nat_add_neg
  have h_im (n : ℕ) : (cotTerm z n).im = -m.succ * y * (F ↑(n + 1) + F (-↑(n + 1))) := by
    simp [z, F, shiftedTerm, Complex.sq_norm, normSq]
    ring
  have h_sum : (∑' n : ℕ, cotTerm z n).im =
      -m.succ * y * (S + π / y * m.succPNat ^ (1 - 2 * 1 : ℝ) - F 0) := by
    rw [im_tsum (summable_cotTerm z.coe_mem_integerComplement)]
    exact ((h_pairs.mul_left (-m.succ * y)).congr_fun h_im).tsum_eq
  -- Compare with the `q`-expansion of the cotangent: the terms `n = 0` cancel, and the constant
  -- term `-π` is `-im z` times the integral `π / (y (m+1))`.
  rw [← cot_series_rep' z.coe_mem_integerComplement, pi_mul_cot_pi_q_exp] at h_sum
  have hm_norm : ‖(m : ℂ) + 1‖ = m + 1 := by norm_cast
  have hτ_pos : 0 < ‖(⟨x, y⟩ : ℂ)‖ := hy.trans_le (im_le_norm ⟨x, y⟩)
  let Q : ℝ := (∑' j : ℕ, eta_q m ⟨x, y⟩ ^ j).re
  have h_key : π - 2 * π * Q + y / ((m + 1) * ‖(⟨x, y⟩ : ℂ)‖ ^ 2) =
      -(m + 1) * y * (S + π / (y * (m + 1)) - 1 / ((m + 1) * ‖(⟨x, y⟩ : ℂ)‖) ^ 2) := by
    clear_value S
    norm_num [z, F, shiftedTerm, ← mul_assoc, ← eta_q_eq_cexp, rpow_neg_one, normSq_eq_norm_sq,
      -ofReal_add, hm_norm] at h_sum
    linear_combination (norm := field) h_sum
  rw [show (∑' j : ℕ, eta_q m ⟨x, y⟩ ^ j.succ / ofReal m.succ).re = (Q - 1) / (m + 1) by
    norm_num [Q, tsum_div_const, geom_series_succ _ (norm_eta_q_lt_one hy m), -ofReal_add]]
  linear_combination (norm := field) ((m + 1) * y)⁻¹ * h_key

/-- At `s = 1` the errors sum to `-2 π / y * log |∏ (1 - q^(j+1))|`, `q = exp (2 π i τ)`,
`τ = x + i y`; the errors are `meanError x y p 1` summed over `p : ℕ+ × ℤ`. -/
lemma New.tsum_meanError_one {x y : ℝ} (hy : 0 < y) :
    ∑' p : ℕ+ × ℤ, meanError x y p 1 =
      -2 * π / y * Real.log ‖∏' j : ℕ, (1 - eta_q j ⟨x, y⟩)‖ := by
  let c (m j : ℕ) : ℂ := eta_q m ⟨x, y⟩ ^ j.succ / ofReal m.succ
  obtain ⟨hc, h_prod⟩ := tprod_one_sub_eta_q (x := x) hy
  have h_rows : HasSum (fun m : ℕ+ ↦ ∑' n : ℤ, meanError x y (m, n) 1)
      (2 * π / y * (∑' m : ℕ, ∑' j : ℕ, c m j).re) :=
    pnatEquivNat.symm.hasSum_iff.1
      (((hasSum_re hc.prod.hasSum).mul_left _).congr_fun (tsum_meanError_row_one hy))
  rw [(summable_meanError hy (by simp)).tsum_prod, h_rows.tsum_eq, h_prod, norm_exp, Real.log_exp,
    neg_re]
  ring

/-- The part of `∑ |m τ + n|^(-2s)`, `τ = x + i y`, without a pole at `s = 1`. For `1 < s < 2` it
is the sum minus `betaFactor y s / (s - 1)` (`New.sub_one_mul_tsum_norm_mul_add_rpow`). -/
noncomputable def New.regularPart (x y s : ℝ) : ℝ :=
  2 * (∑' p : ℕ+ × ℤ, meanError x y p s + (2 * s - 1)⁻¹ + (riemannZeta₀ (2 * s)).re +
    betaFactor y s * (riemannZeta₀ (2 * s - 1)).re)

/-- The regular part of the sum is continuous from the right at `s = 1`. -/
lemma New.continuousWithinAt_regularPart {x y : ℝ} (hy : 0 < y) :
    ContinuousWithinAt (regularPart x y) (Ioi 1) 1 := by
  have h_error : ContinuousWithinAt (fun s : ℝ ↦ ∑' p : ℕ+ × ℤ, meanError x y p s) (Ioi 1) 1 :=
    (continuousOn_tsum_meanError hy 1 (by simp)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT one_lt_two)
  have h_beta : ContinuousAt (betaFactor y) 1 := (hasDerivAt_betaFactor hy).continuousAt
  have h_zeta : Continuous riemannZeta₀ := differentiable_riemannZeta₀.continuous
  unfold regularPart
  fun_prop (disch := norm_num)

lemma New.regularPart_one {x y : ℝ} (hy : 0 < y) :
    regularPart x y 1 = 2 * (-2 * π / y * Real.log ‖∏' j : ℕ, (1 - eta_q j ⟨x, y⟩)‖ + π ^ 2 / 6 +
      π / y * eulerMascheroniConstant) := by
  norm_num [regularPart, tsum_meanError_one hy, betaFactor_one, riemannZeta₀, riemannZeta_two, sq]

/-- Let `τ = x + iy` with `y > 0`, and let `1 < s < 2`. The sum `∑ |m τ + n|^(-2s)` over `ℤ²` is
`regularPart x y s + betaFactor y s / (s - 1)`, where
`betaFactor y s = √π Γ(s - 1/2) / Γ(s) * y^(1 - 2s)` and `regularPart` is the part without a pole at
`s = 1`; the equation is stated multiplied by `s - 1`. -/
lemma New.sub_one_mul_tsum_norm_mul_add_rpow {x y s : ℝ} (hy : 0 < y) (hs : s ∈ Ioo (1 : ℝ) 2) :
    (s - 1) * ∑' p : ℤ × ℤ, ‖p.1 * (⟨x, y⟩ : ℂ) + p.2‖ ^ (-2 * s) =
      (s - 1) * regularPart x y s + betaFactor y s := by
  -- Sum by rows: the row `0` is `2 ζ(2s)` (its term `n = 0` is `0 ^ (-2s) = 0`), and the rows
  -- `m` and `-m` are equal.
  obtain ⟨hs_one, hs_two⟩ := hs
  have hs_mem : s ∈ Icc 1 2 := ⟨hs_one.le, hs_two.le⟩
  let f (p : ℤ × ℤ) : ℝ := ‖p.1 * (⟨x, y⟩ : ℂ) + p.2‖ ^ (-2 * s)
  have hf : Summable f := summable_norm_mul_add_rpow hy (by linarith)
  have h_row_zero : ∑' n : ℤ, f (0, n) = 2 * ((2 * s - 1)⁻¹ + (riemannZeta₀ (2 * s)).re) := by
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat (fun n ↦ by simp [f]) (hf.prod_factor 0)]
    simp [f, (hasSum_pnat_rpow_neg (2 * s) (by linarith)).tsum_eq, (one_pos.trans hs_one).ne',
      mul_add]
  have h_rows_pos : HasSum (fun m : ℕ+ ↦ ∑' n : ℤ, f (m, n))
      (∑' p : ℕ+ × ℤ, meanError x y p s +
        betaFactor y s * ((2 * s - 1 - 1)⁻¹ + (riemannZeta₀ (2 * s - 1)).re)) := by
    have h_zeta : HasSum (fun m : ℕ+ ↦ (m : ℝ) ^ (-(2 * s - 1)))
        ((2 * s - 1 - 1)⁻¹ + (riemannZeta₀ (2 * s - 1)).re) := by
      exact_mod_cast hasSum_pnat_rpow_neg (2 * s - 1) (by linarith)
    rw [(summable_meanError hy hs_mem).tsum_prod]
    refine ((summable_meanError hy hs_mem).prod.hasSum.add
      (h_zeta.mul_left (betaFactor y s))).congr_fun fun m ↦ ?_
    simpa [f, shiftedTerm] using (hasSum_shiftedTerm hy hs_mem m).tsum_eq
  have h_even : Function.Even fun m : ℤ ↦ ∑' n : ℤ, f (m, n) :=
    fun m ↦ (tsum_comp_neg _).symm.trans (by simp [f, norm_neg_add])
  rw [hf.tsum_prod, tsum_int_eq_zero_add_two_mul_tsum_pnat h_even hf.prod, h_row_zero,
    h_rows_pos.tsum_eq, show 2 * s - 1 - 1 = 2 * (s - 1) by ring, regularPart, two_smul]
  field [sub_ne_zero.2 hs_one.ne']

/-- **Kronecker's first limit formula.** Let `L` be a lattice of area `A` and discriminant
`Δ = g₂³ - 27 g₃²`, and let `k > 0`. There is a real function `F` with (a) `F 1 = π k`, (b) right
derivative `F 1 * (2 γ - log (A / (k π²)) - (log |Δ|) / 6)` at `1`, `γ` being Euler's constant, and
(c) `F s = (s - 1) ∑ (|l|² / (k A))^(-s)` for `1 < s < 2`. The sum is over all `l` in the lattice;
the term `l = 0` is `0`, since `0 ^ (-s) = 0` in Lean. For `k = 1` this is the expansion
`∑ (|l|² / A)^(-s) = π / (s - 1) + π (2 γ - log (A |Δ|^(1/6) / π²)) + o(1)` as `s` decreases to
`1`. -/
lemma New.kronecker_limit (L : PeriodPair) (k : ℝ) (hk : 0 < k) :
    ∃ F : ℝ → ℝ,
      -- (a) the value at 1
      F 1 = π * k ∧
      -- (b) the right derivative at 1
      HasDerivWithinAt F
        (F 1 *
          (2 * eulerMascheroniConstant - Real.log (PeriodPair.area L / k / π ^ 2) -
            Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ / 6))
        (Ioi 1) 1 ∧
      -- (c) the series for 1 < s < 2
      ∀ s ∈ Ioo 1 2,
        HasSum (fun l : L.lattice ↦ (s - 1) * (‖l.val‖ ^ 2 / k / L.area) ^ (-s)) (F s) := by
  -- Write the lattice as `a (ℤ τ + ℤ)`, `τ = x + i y`. The sum `∑ |m τ + n|^(-2s)` is
  -- `T s + G s / (s - 1)`, with `T` right-continuous and `G` differentiable at `s = 1`. The value
  -- `T 1` involves `log |∏ (1 - q ^ n)|`, and so does the logarithm of the discriminant.
  obtain ⟨a, ⟨⟨x, y⟩, hy : 0 < y⟩, e, hL, ha, h_area⟩ := exists_lattice_eq_mul_tau L
  let T : ℝ → ℝ := regularPart x y
  let G : ℝ → ℝ := betaFactor y
  have hG_one : G 1 = π / y := betaFactor_one y
  refine ⟨fun s ↦ ((s - 1) * T s + G s) * (k * y) ^ s, ?_, ?_, fun s hs ↦ e.hasSum_iff.1 ?_⟩
  · simp [hG_one, field]
  · have hG : HasDerivAt G (-2 * π / y * (Real.log 2 + Real.log y)) 1 := hasDerivAt_betaFactor hy
    -- The slope of `(s - 1) * T s` at `1` is `T s`, so continuity of `T` gives the derivative.
    have hT_deriv : HasDerivWithinAt (fun s : ℝ ↦ (s - 1) * T s) (T 1) (Ioi 1) 1 := by
      rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
      refine tendsto_nhdsWithin_congr (fun s hs ↦ ?_) (continuousWithinAt_regularPart hy)
      simp [T, slope_def_field, sub_ne_zero.2 (mem_Ioi.1 hs).ne']
    have h_pow : HasDerivWithinAt (fun s : ℝ ↦ (k * y) ^ s)
        (Real.log (k * y) * 1 * (k * y) ^ (1 : ℝ)) (Ioi 1) 1 :=
      (hasDerivWithinAt_id 1 (Ioi 1)).const_rpow (mul_pos hk hy)
    let P : ℂ := ∏' j : ℕ, (1 - eta_q j ⟨x, y⟩)
    have hP : P ≠ 0 := eta_tprod_ne_zero hy
    have hT_one : T 1 = 2 * (-2 * π / y * Real.log ‖P‖ + π ^ 2 / 6 +
        π / y * eulerMascheroniConstant) := regularPart_one hy
    -- `g₂³ - 27 g₃² = (2 π / a)^12 * q * ∏ (1 - q^(j+1))^24` and `|q| = exp (-2 π y)`.
    have h_disc : Real.log ‖L.g₂ ^ 3 - 27 * L.g₃ ^ 2‖ =
        12 * (Real.log 2 + Real.log π - Real.log ‖a‖) - 2 * π * y + 24 * Real.log ‖P‖ := by
      rw [g₂_pow_three_sub_g₃_sq_eq_discriminant hL]
      norm_num [discriminant, ModularForm.eta, P, hP, norm_exp, qParam, Real.log_mul, log_div, ha]
      ring
    have h_log_area : Real.log (L.area / k / π ^ 2) =
        2 * Real.log ‖a‖ + Real.log y - Real.log k - 2 * Real.log π := by
      simp [h_area, Real.log_mul, log_div, ha, hy.ne', hk.ne']
    have h_deriv : HasDerivWithinAt (fun s : ℝ ↦ ((s - 1) * T s + G s) * (k * y) ^ s)
        ((T 1 + -2 * π / y * (Real.log 2 + Real.log y)) * (k * y) ^ (1 : ℝ) +
          ((1 - 1) * T 1 + G 1) * (Real.log (k * y) * 1 * (k * y) ^ (1 : ℝ))) (Ioi 1) 1 :=
      (hT_deriv.add hG.hasDerivWithinAt).mul h_pow
    refine h_deriv.congr_deriv ?_
    beta_reduce
    rw [hT_one, hG_one, h_disc, h_log_area, Real.log_mul hk.ne' hy.ne', rpow_one]
    field
  · let f (p : ℤ × ℤ) : ℝ := ‖p.1 * (⟨x, y⟩ : ℂ) + p.2‖ ^ (-2 * s)
    have hf : Summable f := summable_norm_mul_add_rpow hy (by linarith [hs.1])
    have h_total : (s - 1) * ∑' p : ℤ × ℤ, f p = (s - 1) * T s + G s :=
      sub_one_mul_tsum_norm_mul_add_rpow hy hs
    have h_sum : HasSum (fun p : ℤ × ℤ ↦ (s - 1) * f p * (k * y) ^ s)
        (((s - 1) * T s + G s) * (k * y) ^ s) := by
      simpa [h_total] using (hf.hasSum.mul_left (s - 1)).mul_right ((k * y) ^ s)
    -- The factor `‖a‖ ^ 2` cancels between `‖l‖ ^ 2` and the area, leaving `(k * y) ^ s`.
    refine h_sum.congr_fun fun p ↦ ?_
    simp [f, hL, h_area, hk, hy, mul_pow, div_rpow, mul_rpow, rpow_neg, rpow_mul, le_of_lt, field]

import Lib.Analytic.PolyaVinogradov

/-!
# Theta series of Dirichlet characters, Poisson summation, and `L(s, χ)` as a Mellin transform

For a parity `j ∈ {0, 1}`, the weight `w(z) = z ^ j e^(-π z²)` and coefficients `c(n)`, this file
studies the theta series `θ(u) = u ^ (1/2) ∑_{n ≥ 1} c(n) w(n u)`. It bounds `θ` and expresses its
Mellin transform through the Dirichlet series of `c`. For a Dirichlet character `χ ≠ 1` of parity
`j`, Poisson summation bounds the series near `0` and so gives the formula for `L(s, χ)` in
`re s > 0` (`hasMellin_thetaSeries_char`); if `χ` is also primitive, it gives the transformation
formula of `|θ|` (`norm_thetaSeries_inv`).

## Relation to the literature

Known result: the transformation formula and the Mellin transform of the theta series of a Dirichlet
character. Sources: Davenport, Multiplicative Number Theory; Montgomery–Vaughan, Multiplicative
Number Theory I, ch. 10. Form here: the transformation is proved in absolute value only, so no root
number appears.
-/

noncomputable section

open Complex MeasureTheory Set Real ZMod HurwitzZeta Filter ArithmeticFunction Moebius

namespace New

/-- The weight `w(z) = z ^ j e^(-π z²)` of parity `j ∈ {0, 1}`. -/
def gaussianMonomial (j : Fin 2) (z : ℝ) : ℝ := z ^ j.val * rexp (-π * z ^ 2)

/-- The series `∑_{n ≥ 1} c(n) w(n u)`. -/
def gaussianTheta (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ :=
  ∑' n : ℕ+, c n * gaussianMonomial j (n * u)

/-- The theta series `θ(u) = u ^ (1/2) ∑_{n ≥ 1} c(n) w(n u)`. -/
def thetaSeries (j : Fin 2) (c : ℕ → ℂ) (u : ℝ) : ℂ := √u * gaussianTheta j c u

/-- The Mellin transform `Γ_j(s) = ∫_0^∞ w(z) z ^ s dz / z` of the weight `w`. -/
def gaussianMellin (j : Fin 2) : ℂ → ℂ := mellin (gaussianMonomial j ·)

variable {j : Fin 2} {c : ℕ → ℂ} {q : ℕ} {t : ℝ} {s : ℂ} [NeZero q] {χ : DirichletCharacter ℂ q}

lemma measurable_gaussianTheta : Measurable (gaussianTheta j c) := by
  fun_prop [gaussianTheta, gaussianMonomial]

lemma measurable_thetaSeries : Measurable (thetaSeries j c) :=
  (measurable_ofReal.comp continuous_sqrt.measurable).mul measurable_gaussianTheta

/-- If a measurable function `f` satisfies `‖f(t)‖ ≤ D e^(-t)` for `t > 0`, then at every `s` with
`re s > 0` the Mellin integral of `f` converges absolutely and `mellin f` is differentiable at
`s`. -/
lemma mellinConvergent_and_differentiableAt {D : ℝ} {f : ℝ → ℂ}
    (h_bound : ∀ t : ℝ, 0 < t → ‖f t‖ ≤ D * rexp (-t)) (h_meas : Measurable f) (hs : 0 < s.re) :
    MellinConvergent f s ∧ DifferentiableAt ℂ (mellin f) s := by
  -- `f` decays exponentially at `∞` and is bounded on `(0, ∞)`.
  have h_bdd (x : ℝ) : ∀ᶠ t in nhdsWithin x (Ioi 0), ‖f t‖ ≤ |D| :=
    eventually_nhdsWithin_of_forall fun t (ht : 0 < t) ↦ by
      grw [h_bound t ht, le_abs_self D, exp_le_one_iff.2 (neg_nonpos.2 ht.le), mul_one]
  have h_top : f =O[atTop] fun t ↦ rexp (-1 * t) :=
    .of_bound D ((eventually_gt_atTop 0).mono fun t ht ↦ by simpa using h_bound t ht)
  have h_zero : f =O[nhdsWithin 0 (Ioi 0)] fun t ↦ t ^ (-0 : ℝ) :=
    .of_bound |D| (by simpa using h_bdd 0)
  have h_loc : LocallyIntegrableOn f (Ioi 0) := fun x _ ↦ (volume.finiteAt_nhdsWithin x _)
    |>.integrableAtFilter h_meas.stronglyMeasurable.stronglyMeasurableAtFilter ⟨|D|, h_bdd x⟩
  exact ⟨mellinConvergent_of_isBigO_rpow_exp one_pos h_loc h_top h_zero hs,
    mellin_differentiableAt_of_isBigO_rpow_exp one_pos h_loc h_top h_zero hs⟩

/-- If a measurable function `f` satisfies `‖f(t)‖ ≤ D e^(-t)` for `t > 0`, then its Mellin
transform is holomorphic in `re s > 0` and bounded on `1/2 ≤ re s ≤ 2`. -/
lemma mellin_differentiableOn_and_bounded {D : ℝ} {f : ℝ → ℂ}
    (h_bound : ∀ t : ℝ, 0 < t → ‖f t‖ ≤ D * rexp (-t)) (h_meas : Measurable f) :
    DifferentiableOn ℂ (mellin f) {z : ℂ | 0 < z.re} ∧
    ∃ G : ℝ, ∀ z : ℂ, z.re ∈ Icc 2⁻¹ 2 → ‖mellin f z‖ ≤ G := by
  -- In the strip the integrand is at most the sum of those at `z = 1/2` (which serves for
  -- `t ≤ 1`) and at `z = 2` (for `t ≥ 1`).
  obtain ⟨h_half, -⟩ := mellinConvergent_and_differentiableAt (s := 2⁻¹) h_bound h_meas (by simp)
  obtain ⟨h_two, -⟩ := mellinConvergent_and_differentiableAt (s := 2) h_bound h_meas (by simp)
  have h_integrand (z : ℂ) (hz : z.re ∈ Icc (2⁻¹ : ℝ) 2) (t : ℝ) (ht : 0 < t) :
      ‖(t : ℂ) ^ (z - 1) • f t‖ ≤
        ‖(t : ℂ) ^ ((2⁻¹ : ℂ) - 1) • f t‖ + ‖(t : ℂ) ^ ((2 : ℂ) - 1) • f t‖ := by
    have h_pow : t ^ (z.re - 1) ≤ t ^ ((2⁻¹ : ℝ) - 1) + t ^ ((2 : ℝ) - 1) := by
      obtain h | h := le_total t 1
      · exact le_add_of_le_of_nonneg
          (rpow_le_rpow_of_exponent_ge ht h (by linarith [hz.1])) (by positivity)
      · exact le_add_of_nonneg_of_le (by positivity)
          (rpow_le_rpow_of_exponent_le h (by linarith [hz.2]))
    simpa [norm_cpow_eq_rpow_re_of_pos ht, ← add_mul] using
      mul_le_mul_of_nonneg_right h_pow (norm_nonneg (f t))
  exact ⟨fun z hz ↦
      (mellinConvergent_and_differentiableAt h_bound h_meas hz).2.differentiableWithinAt,
    _, fun z hz ↦ norm_integral_le_of_norm_le (h_half.norm.add h_two.norm)
      (ae_restrict_of_forall_mem measurableSet_Ioi (h_integrand z hz))⟩

/-- For `t ≥ 0` the weight `w(t) = t ^ j e^(-π t²)` satisfies `|w(t)| ≤ 3 e^(-2t)`. -/
lemma norm_gaussianMonomial_le (ht : 0 ≤ t) : ‖gaussianMonomial j t‖ ≤ 3 * rexp (-t) ^ 2 := by
  have h_pow : t ^ j.val ≤ rexp t :=
    calc t ^ j.val ≤ t + 1 := by fin_cases j <;> simp [ht]
      _ ≤ rexp t := add_one_le_exp t
  -- As `π > 3`, this follows from `3 t² - 3 t + 1 = 3 (t - 1/2)² + 1/4 ≥ 0`.
  have h_exp : t + -π * t ^ 2 ≤ 1 + (-t + -t) := by
    nlinarith [pi_gt_three, sq_nonneg (t - 2⁻¹), sq_nonneg t]
  calc ‖gaussianMonomial j t‖ = t ^ j.val * rexp (-π * t ^ 2) := by
        simp [gaussianMonomial, abs_of_nonneg ht]
    _ ≤ rexp t * rexp (-π * t ^ 2) := by gcongr
    _ ≤ rexp (1 + (-t + -t)) := by grw [← Real.exp_add, h_exp]
    _ = rexp 1 * rexp (-t) ^ 2 := by rw [Real.exp_add, Real.exp_add, sq]
    _ ≤ 3 * rexp (-t) ^ 2 := by grw [exp_one_lt_three]

/-- If `|c(n)| ≤ 1` and `t > 0`, the series `∑_{n ≥ 1} c(n) w(n t)`, with
`w(z) = z ^ j e^(-π z²)`, converges and is at most `3 e^(-t) / t` in absolute value. -/
lemma summable_and_norm_gaussianTheta_le (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (ht : 0 < t) :
    (Summable fun n : ℕ+ ↦ c n * gaussianMonomial j (n * t)) ∧
      ‖gaussianTheta j c t‖ ≤ 3 * rexp (-t) / t := by
  -- By `norm_gaussianMonomial_le` the terms are bounded by those of the geometric series
  -- `∑ 3 r ^ n`, `r = e^(-2t)`.
  let r : ℝ := rexp (-t) ^ 2
  have hr : |r| < 1 := by simpa [r] using ht
  have h_geom : HasSum (fun n : ℕ+ ↦ 3 * r ^ (n : ℕ)) (3 * (1 - r)⁻¹ - 3) :=
    (hasSum_pnat_iff_hasSum_succ (f := fun n : ℕ ↦ 3 * r ^ n)).2 <| by
      simpa using (hasSum_nat_add_iff' 1).2 ((hasSum_geometric_of_abs_lt_one hr).mul_left 3)
  have h_term (n : ℕ+) : ‖c n * gaussianMonomial j (n * t)‖ ≤ 3 * r ^ (n : ℕ) := by
    grw [norm_mul, hc, norm_real, norm_gaussianMonomial_le (by positivity)]
    simp [r, ← Real.exp_nat_mul, field]
  -- As `t + 1 ≤ e^t`, we have `(t + e^(-t)) e^(-t) ≤ 1`.
  have h_mul_exp_le : t * rexp (-t) ≤ 1 - r := by
    nlinarith [add_one_le_exp t, exp_pos (-t), exp_le_one_iff.2 (neg_nonpos.2 ht.le),
      show rexp t * rexp (-t) = 1 by simp [← Real.exp_add]]
  have h_sum : 3 * (1 - r)⁻¹ - 3 ≤ 3 * rexp (-t) / t := by
    have h_one_sub : 0 < 1 - r := (mul_pos ht (exp_pos _)).trans_le h_mul_exp_le
    calc 3 * (1 - r)⁻¹ - 3 = 3 * r / (1 - r) := by field
      _ ≤ 3 * r / (t * rexp (-t)) := by gcongr
      _ = 3 * rexp (-t) / t := by simp [r, field]
  exact ⟨h_geom.summable.of_norm_bounded h_term, (tsum_of_norm_bounded h_geom h_term).trans h_sum⟩

/-- The absolute value of `θ(u) = u ^ (1/2) ∑_{n ≥ 1} c(n) w(n u)` is `u ^ (1/2)` times that of
the sum. -/
lemma norm_thetaSeries (u : ℝ) : ‖thetaSeries j c u‖ = √u * ‖gaussianTheta j c u‖ := by
  rw [thetaSeries, norm_mul, norm_real, norm_of_nonneg (sqrt_nonneg u)]

/-- The trivial bound: if `|c(n)| ≤ 1` and `t > 0`, then the theta series
`θ(t) = t ^ (1/2) ∑_{n ≥ 1} c(n) w(n t)` is at most `3 t ^ (-1/2) e^(-t)` in absolute value. -/
lemma norm_thetaSeries_le (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (ht : 0 < t) :
    ‖thetaSeries j c t‖ ≤ 3 * rexp (-t) / √t :=
  calc ‖thetaSeries j c t‖ ≤ √t * (3 * rexp (-t) / t) := by
        grw [norm_thetaSeries, (summable_and_norm_gaussianTheta_le hc ht).2]
    _ = 3 * rexp (-t) * (√t / t) := by ring
    _ = 3 * rexp (-t) / √t := by rw [sqrt_div_self', mul_one_div]

/-- For `|c(n)| ≤ 1` and `r > 0` the integral `∫_r^∞ |θ(u)| du / u` converges, by the trivial bound
on `θ`. -/
lemma integrableOn_norm_thetaSeries_div (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun u : ℝ ↦ ‖thetaSeries j c u‖ / u) (Ioi r) := by
  have h_majorant : IntegrableOn (fun u : ℝ ↦ 3 * rexp (-u) / √r / r) (Ioi r) :=
    (((integrableOn_exp_neg_Ioi r).const_mul 3).div_const √r).div_const r
  have h_le (u : ℝ) (hu : r < u) : ‖‖thetaSeries j c u‖ / u‖ ≤ 3 * rexp (-u) / √r / r := by
    have hu_pos : 0 < u := hr.trans hu
    grw [norm_of_nonneg (by positivity), norm_thetaSeries_le hc hu_pos]
    gcongr
  exact h_majorant.mono' (measurable_thetaSeries.norm.div measurable_id).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi h_le)

/-- For `t > 0` we have `t ^ (s - 1/2 - 1) θ(t) = t ^ (s - 1) ∑_{n ≥ 1} c(n) w(n t)`: the
integrands of the Mellin transforms of `θ` at `s - 1/2` and of the series at `s` agree. -/
lemma cpow_smul_thetaSeries (s : ℂ) (ht : 0 < t) :
    (t : ℂ) ^ (s - 2⁻¹ - 1) • thetaSeries j c t = (t : ℂ) ^ (s - 1) • gaussianTheta j c t := by
  have h_sqrt : (√t : ℂ) = t ^ (2⁻¹ : ℂ) := by simp [sqrt_eq_rpow, ofReal_cpow ht.le]
  rw [thetaSeries, h_sqrt, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ← cpow_add _ _ (ofReal_ne_zero.2 ht.ne')]
  ring_nf

/-- The Mellin transform of `θ(u) = u ^ (1/2) ∑_{n ≥ 1} c(n) w(n u)` at `s - 1/2` is that of the sum
at `s`. -/
lemma mellin_thetaSeries_sub_half (s : ℂ) :
    mellin (thetaSeries j c) (s - 2⁻¹) = mellin (gaussianTheta j c) s :=
  setIntegral_congr_fun measurableSet_Ioi fun _ ht ↦ cpow_smul_thetaSeries s ht

/-- By the substitution `u = t²`, the Mellin transform of `t ^ k F(t²)` at `s` is half that of
`F` at `(s + k) / 2`. -/
lemma mellin_pow_mul_comp_sq (F : ℝ → ℂ) (k : ℕ) (s : ℂ) :
    mellin (fun t : ℝ ↦ t ^ k * F (t ^ 2)) s = mellin F ((s + k) / 2) / 2 := by
  trans mellin (fun t : ℝ ↦ F (t ^ 2)) (s + k)
  · simpa using mellin_cpow_smul (fun t : ℝ ↦ F (t ^ 2)) s k
  · simpa [field] using mellin_comp_rpow F (s + k) 2

/-- For `re s > 0` the Mellin transform `Γ_j` of `w(z) = z ^ j e^(-π z²)` is
`Γ_j(s) = π ^ (-(s + j) / 2) Γ((s + j) / 2) / 2`. -/
lemma gaussianMellin_eq (hs : 0 < s.re) : gaussianMellin j s = Gammaℝ (s + j.val) / 2 := by
  -- `w(t) = t ^ j F(t²)` with `F(u) = e^(-π u)`, a series of Gaussians with a single term.
  let F (u : ℝ) : ℂ := rexp (-π * u)
  have h_re : 0 < (s + j.val).re := by simpa using hs.trans_le (by simp)
  have h_single : HasSum (fun _ : Unit ↦ Gammaℝ (s + j.val)) (mellin F ((s + j.val) / 2)) := by
    simpa using hasSum_mellin_pi_mul_sq (a := 1) (r := 1) (F := F) h_re (by simp [F]) .of_finite
  rw [(hasSum_unique _).unique h_single, ← mellin_pow_mul_comp_sq]
  simp [gaussianMellin, gaussianMonomial, F]

/-- Integration term by term: if `|c(n)| ≤ 1` and `re s > 1`, the Mellin transform of
`∑_{n ≥ 1} c(n) w(n u)` at `s` is `Γ_j(s) L(s, c)`, where `Γ_j` is the Mellin transform of the
weight `w(z) = z ^ j e^(-π z²)`. -/
lemma mellin_gaussianTheta (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (hs : 1 < s.re) :
    mellin (gaussianTheta j c) s = gaussianMellin j s * LSeries c s := by
  -- `gaussianTheta j c t = t ^ j F(t²)` with `F(u) = ∑ a(n) e^(-π n² u)`, `a(n) = c(n) n ^ j`, and
  -- the Mellin transform of `F` may be taken term by term.
  let a (n : ℕ+) : ℂ := c n * n ^ j.val
  let F (u : ℝ) : ℂ := ∑' n : ℕ+, a n * rexp (-π * n ^ 2 * u)
  have h_theta : gaussianTheta j c = fun t : ℝ ↦ t ^ j.val * F (t ^ 2) := funext fun t ↦ by
    simp [gaussianTheta, gaussianMonomial, F, a, ← tsum_mul_left, mul_pow, mul_assoc, mul_left_comm]
  have h_series (u : ℝ) (hu : 0 < u) : Summable fun n : ℕ+ ↦ a n * rexp (-π * n ^ 2 * u) :=
    ((summable_and_norm_gaussianTheta_le (j := j) hc (sqrt_pos.2 hu)).1.div_const
      (√u ^ j.val)).congr fun n ↦ by
        have h_sqrt : (√u : ℂ) ≠ 0 := ofReal_ne_zero.2 (sqrt_pos.2 hu).ne'
        simp [a, gaussianMonomial, mul_pow, mul_assoc, hu.le, field]
  have h_coeff : Summable fun n : ℕ+ ↦ ‖a n‖ / |(n : ℝ)| ^ (s + j.val).re :=
    (summable_pnat_iff_summable_nat.2 (summable_nat_rpow_inv.2 hs)).of_nonneg_of_le
      (fun _ ↦ by positivity) fun n ↦ by simp [a, rpow_add, field, hc]
  have h_re : 0 < (s + j.val).re := by simpa using (one_pos.trans hs).trans_le (by simp)
  have h_mellin : HasSum (fun n : ℕ+ ↦ Gammaℝ (s + j.val) * a n / |(n : ℝ)| ^ (s + j.val))
      (mellin F ((s + j.val) / 2)) :=
    hasSum_mellin_pi_mul_sq h_re (fun u hu ↦ by simpa [F] using (h_series u hu).hasSum) h_coeff
  have h_term (n : ℕ+) : Gammaℝ (s + j.val) * a n / |(n : ℝ)| ^ (s + j.val) / 2 =
      gaussianMellin j s * LSeries.term c s n := by
    simp [gaussianMellin_eq (one_pos.trans hs), a, cpow_add, field]
  calc mellin (gaussianTheta j c) s = mellin F ((s + j.val) / 2) / 2 := by
        rw [h_theta, mellin_pow_mul_comp_sq]
    _ = ∑' n : ℕ+, gaussianMellin j s * LSeries.term c s n := by
        rw [← h_mellin.tsum_eq, ← tsum_div_const, tsum_congr h_term]
    _ = gaussianMellin j s * LSeries c s := by
        rw [tsum_mul_left, tsum_pnat_eq_tsum_of_eq_zero (LSeries.term_zero c s), LSeries]

/-- Riemann's formula `∫_0^∞ θ(u) u ^ (s - 1/2) du / u = Γ_j(s) L(s, c)` for `re s > 1` and
`|c(n)| ≤ 1`, where `θ` is the theta series of `c` and `Γ_j` the Mellin transform of its weight
`w(z) = z ^ j e^(-π z²)`. -/
lemma mellin_thetaSeries (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (hs : 1 < s.re) :
    mellin (thetaSeries j c) (s - 2⁻¹) = gaussianMellin j s * LSeries c s := by
  rw [mellin_thetaSeries_sub_half, mellin_gaussianTheta hc hs]

/-- If `|c(n)| ≤ 1` for all `n`, then also `|c(n) μ(n)| ≤ 1`, where `μ` is the Möbius function. -/
lemma norm_mul_moebius_le_one (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (n : ℕ) : ‖c n * μ n‖ ≤ 1 := by
  grw [norm_mul, hc, one_mul, Complex.norm_intCast, ← Int.cast_abs, abs_moebius_le_one,
    Int.cast_one]

/-- Riemann's formula for `1 / L`: if `re s > 1`, then the theta series `θ` with coefficients
`χ(n) μ(n)` satisfies `∫_0^∞ θ(u) u ^ (s - 1/2) du / u = Γ_j(s) / L(s, χ)`, where `Γ_j` is the
Mellin transform of the weight `w(z) = z ^ j e^(-π z²)`. -/
lemma mellin_thetaSeries_moebius (χ : DirichletCharacter ℂ q) (hs : 1 < s.re) :
    mellin (thetaSeries j fun n : ℕ ↦ χ n * μ n) (s - 2⁻¹) =
      gaussianMellin j s / χ.LFunction s := by
  have h_inv : χ.LFunction s * LSeries (fun n : ℕ ↦ χ n * μ n) s = 1 := by
    rw [χ.LFunction_eq_LSeries hs]
    exact DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  rw [mellin_thetaSeries (norm_mul_moebius_le_one fun n ↦ χ.norm_le_one n) hs,
    eq_inv_of_mul_eq_one_right h_inv, div_eq_mul_inv]

omit [NeZero q] in
/-- If `Φ : ZMod q → ℂ` has parity `j` and vanishes at `0`, then the sum of `Φ(n) w(n t)` over `ℤ`,
where `w(z) = z ^ j e^(-π z²)`, is twice the sum over `n ≥ 1` that defines `gaussianTheta`. -/
lemma two_mul_gaussianTheta (t : ℝ) {Φ : ZMod q → ℂ} {S : ℂ}
    (h_parity : ∀ x : ZMod q, Φ (-x) = (-1) ^ j.val * Φ x) (h_zero : Φ 0 = 0)
    (h_sum : HasSum (fun n : ℤ ↦ Φ n * gaussianMonomial j (n * t)) S) :
    2 * gaussianTheta j (fun n : ℕ ↦ Φ n) t = S := by
  -- The terms are even in `n` and the one at `n = 0` vanishes.
  have h_even : Function.Even fun n : ℤ ↦ Φ n * gaussianMonomial j (n * t) := by
    fin_cases j <;> simp [Function.Even, gaussianMonomial, h_parity]
  rw [← h_sum.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat h_even h_sum.summable]
  simp [gaussianTheta, h_zero]

/-- Poisson summation for `w(z) = z ^ j e^(-π z²)`: for `t > 0` and real `a`,
`∑_{n ∈ ℤ} e^(2πi a n) w(n / t) = i ^ j t ∑_{n ∈ ℤ} w((n + a) t)`, both series being convergent. -/
lemma poisson_summation_gaussianMonomial (a : ℝ) (ht : 0 < t) : ∃ S : ℝ,
    HasSum (fun n : ℤ ↦ gaussianMonomial j ((n + a) * t)) S ∧
    HasSum (fun n : ℤ ↦ cexp (2 * π * I * a * n) * gaussianMonomial j (n * t⁻¹))
      (I ^ j.val * t * S) := by
  -- Up to a factor when `j = 1`, the two sums are the theta kernels of Mathlib at `t²` and
  -- `1 / t²`, and the functional equations of these kernels compare them.
  have h_sq : 0 < t ^ 2 := by positivity
  fin_cases j
  · have h_fe : (cosKernel a (t ^ 2)⁻¹ : ℂ) = t * evenKernel a (t ^ 2) := by
      simp [evenKernel_functional_equation, ← rpow_natCast_mul ht.le, ht.ne']
    refine ⟨evenKernel a (t ^ 2), (hasSum_int_evenKernel a h_sq).congr_fun fun n ↦ ?_, ?_⟩
    · simp [gaussianMonomial, mul_pow, mul_assoc]
    · simpa [gaussianMonomial, mul_pow, mul_assoc, h_fe] using
        hasSum_int_cosKernel a (inv_pos.2 h_sq)
  · have h_fe : I / t * sinKernel a (t ^ 2)⁻¹ = I * t * (t * oddKernel a (t ^ 2)) := by
      simp [oddKernel_functional_equation, ← rpow_natCast_mul ht.le, field, mul_div_cancel₀]
    refine ⟨t * oddKernel a (t ^ 2),
      ((hasSum_int_oddKernel a h_sq).mul_left t).congr_fun fun n ↦ ?_, ?_⟩
    · simp [gaussianMonomial, mul_pow, field]
    · -- Termwise `(I / t) (-I n) = n / t`, the factor in front of the Gaussian in `w(n / t)`.
      have h_dual := (hasSum_int_sinKernel a (inv_pos.2 h_sq)).mul_left (I / t)
      rw [h_fe] at h_dual
      simpa using h_dual.congr_fun fun n ↦ by simp [gaussianMonomial, mul_pow, mul_assoc, field]

/-- The Mellin transform `Γ_j` of the weight `w(z) = z ^ j e^(-π z²)` is holomorphic in
`re s > 0` and bounded on `1/2 ≤ re s ≤ 2`. -/
lemma gaussianMellin_differentiableOn_and_bdd :
    DifferentiableOn ℂ (gaussianMellin j) {z : ℂ | 0 < z.re} ∧
    ∃ G : ℝ, ∀ z : ℂ, z.re ∈ Icc 2⁻¹ 2 → ‖gaussianMellin j z‖ ≤ G := by
  have h_bound (t : ℝ) (ht : 0 < t) : ‖(gaussianMonomial j t : ℂ)‖ ≤ 3 * rexp (-t) := by
    grw [norm_real, norm_gaussianMonomial_le ht.le,
      pow_le_of_le_one (exp_nonneg _) (exp_le_one_iff.2 (neg_nonpos.2 ht.le)) two_ne_zero]
  exact mellin_differentiableOn_and_bounded h_bound (by fun_prop [gaussianMonomial])

/-- On a compact subset `K` of the half plane `re s > 0` the Mellin transform `Γ_j` of
`w(z) = z ^ j e^(-π z²)` is bounded away from zero in absolute value. -/
lemma exists_pos_le_norm_gaussianMellin {K : Set ℂ} (hK : IsCompact K)
    (h_re : ∀ s ∈ K, 0 < s.re) : ∃ c > (0 : ℝ), ∀ s ∈ K, c ≤ ‖gaussianMellin j s‖ := by
  -- `Γ_j` is continuous, and has no zero as `Gammaℝ` has none.
  refine hK.exists_forall_le'
    (gaussianMellin_differentiableOn_and_bdd.1.continuousOn.mono h_re).norm fun s hs ↦ ?_
  have h_re_add : 0 < (s + j.val).re := by simpa using (h_re s hs).trans_le (by simp)
  simp [gaussianMellin_eq (h_re s hs), Gammaℝ_ne_zero_of_re_pos h_re_add]

/-- A sum over `ℤ` may be taken class by class modulo `q`: if `∑_m w((m + a / q) q t) = S a` for
every class `a`, where `w` is `gaussianMonomial j`, then `∑_n Φ(n) w(n t) = ∑_a Φ(a) S a`. -/
lemma hasSum_mul_gaussianMonomial_of_classes (Φ : ZMod q → ℂ) {S : ZMod q → ℝ}
    (h_class : ∀ a : ZMod q,
      HasSum (fun m : ℤ ↦ gaussianMonomial j ((m + a.val / q) * (q * t))) (S a)) :
    HasSum (fun n : ℤ ↦ Φ n * gaussianMonomial j (n * t)) (∑ a : ZMod q, Φ a * S a) := by
  have h_range (a : ZMod q) : HasSum
      (fun n : ℤ ↦ if n = a then Φ n * gaussianMonomial j (n * t) else 0) (Φ a * S a) := by
    -- The class of `a` is the range of `m ↦ a + q m`.
    have h_inj : (fun m : ℤ ↦ ZMod.cast a + q * m).Injective := fun _ _ ↦ by simp [NeZero.ne q]
    have h_outside (n : ℤ) (hn : n ∉ range fun m : ℤ ↦ ZMod.cast a + q * m) :
        (if n = a then Φ n * gaussianMonomial j (n * t) else 0 : ℂ) = 0 := by
      simp_all [intCast_eq_iff, ne_comm]
    refine (h_inj.hasSum_iff h_outside).1
      (((hasSum_ofReal.2 (h_class a)).mul_left (Φ a)).congr_fun fun m ↦ ?_)
    have h_mod : ((ZMod.cast a + q * m : ℤ) : ZMod q) = a := by simp [natCast_self]
    have h_arg : ((ZMod.cast a + q * m : ℤ) : ℝ) * t = (m + a.val / q) * (q * t) := by
      have hq : (q : ℝ) ≠ 0 := NeZero.ne _
      simp [field]; ring
    rw [Function.comp_apply, ite_eq_left h_mod, h_mod, h_arg]
  simpa using hasSum_sum fun (a : ZMod q) (_ : a ∈ Finset.univ) ↦ h_range a

/-- If `∑_n e^(2πi a n / q) w(n / (q t)) = i ^ j q t S a` for every class `a` modulo `q`, where `w`
is `gaussianMonomial j`, then `∑_n 𝓕⁻ Φ(n) w(n / (q t)) = i ^ j t ∑_a Φ(a) S a`, as
`𝓕⁻ Φ(n) = q⁻¹ ∑_a Φ(a) e^(2πi a n / q)`. Here `n` runs over `ℤ` and `a` over `ZMod q`. -/
lemma hasSum_invDFT_mul_gaussianMonomial (Φ : ZMod q → ℂ) {S : ZMod q → ℝ}
    (h_dual : ∀ a : ZMod q,
      HasSum (fun n : ℤ ↦
          cexp (2 * π * I * (a.val / q : ℝ) * n) * gaussianMonomial j (n * (q * t)⁻¹))
        (I ^ j.val * (q * t : ℝ) * S a)) :
    HasSum (fun n : ℤ ↦ 𝓕⁻ Φ n * gaussianMonomial j (n * (q * t)⁻¹))
      (I ^ j.val * t * ∑ a : ZMod q, Φ a * S a) := by
  have h_char (a : ZMod q) (n : ℤ) :
      stdAddChar (a * (n : ZMod q)) = cexp (2 * π * I * (a.val / q : ℝ) * n) := by
    rw [← zsmul_eq_mul', AddChar.map_zsmul_eq_zpow, stdAddChar_apply, toCircle_apply, ← exp_int_mul]
    push_cast
    ring_nf
  have h_value : (∑ a : ZMod q, Φ a * (I ^ j.val * (q * t : ℝ) * S a)) / q =
      I ^ j.val * t * ∑ a : ZMod q, Φ a * S a := by
    have hq : (q : ℂ) ≠ 0 := NeZero.ne _
    simp [mul_left_comm (Φ _), ← Finset.mul_sum, field]
  rw [← h_value]
  refine ((hasSum_sum fun a _ ↦ (h_dual a).mul_left (Φ a)).div_const q).congr_fun fun n ↦ ?_
  simp only [invDFT_apply, h_char, smul_eq_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_div]
  exact Finset.sum_congr rfl fun a _ ↦ by ring

/-- For a Dirichlet character `χ ≠ 1` modulo `q` of parity `j ∈ {0, 1}`, primitive or not, Poisson
summation in the classes modulo `q` gives `t |∑ χ(n) w(n t)| = |∑ 𝓕⁻ χ(n) w(n / (q t))|` for
`t > 0`, where `w(z) = z ^ j e^(-π z²)`, the sums are over `n ≥ 1` (`gaussianTheta`) and
`𝓕⁻ χ(n) = q⁻¹ ∑_a χ(a) e^(2πi a n / q)`. -/
lemma gaussianTheta_poisson_summation (hχ_ne : χ ≠ 1) (hχ_parity : χ (-1) = (-1) ^ j.val)
    (ht : 0 < t) :
    t * ‖gaussianTheta j (fun n : ℕ ↦ χ n) t‖ =
      ‖gaussianTheta j (fun n : ℕ ↦ 𝓕⁻ χ n) (q * t)⁻¹‖ := by
  -- Apply `poisson_summation_gaussianMonomial` to each class `a` mod `q`, with shift `a / q` and
  -- scale `q t`, multiply by `χ(a)` and add up over `a`. The first sums give
  -- `∑_{n ∈ ℤ} χ(n) w(n t)`, the second `q ∑_{n ∈ ℤ} 𝓕⁻ χ(n) w(n / (q t))`.
  have h_parity (x : ZMod q) : χ (-x) = (-1) ^ j.val * χ x := by
    rw [← hχ_parity, ← map_mul, neg_one_mul]
  have h_poisson (a : ZMod q) : ∃ S : ℝ,
      HasSum (fun n : ℤ ↦ gaussianMonomial j ((n + a.val / q) * (q * t))) S ∧
      HasSum (fun n : ℤ ↦
          cexp (2 * π * I * (a.val / q : ℝ) * n) * gaussianMonomial j (n * (q * t)⁻¹))
        (I ^ j.val * (q * t : ℝ) * S) :=
    poisson_summation_gaussianMonomial (a.val / q) (mul_pos (Nat.cast_pos.2 (NeZero.pos q)) ht)
  choose S h_class h_dual using h_poisson
  -- Both `χ` and `𝓕⁻ χ` have parity `j` and vanish at `0`.
  have h_parity_dual (n : ZMod q) : 𝓕⁻ χ (-n) = (-1) ^ j.val * 𝓕⁻ χ n := by
    simp_rw [invDFT_apply', ← congrFun (dft_comp_neg χ) (-n), h_parity, dft_const_mul]
    ring
  have h_zero_dual : 𝓕⁻ χ 0 = 0 := by simp [invDFT_apply, χ.sum_eq_zero_of_ne_one hχ_ne]
  have h_sum : 2 * gaussianTheta j (fun n : ℕ ↦ χ n) t = ∑ a : ZMod q, χ a * S a :=
    two_mul_gaussianTheta t h_parity (χ.map_zero' (hχ_ne ∘ χ.level_one'))
      (hasSum_mul_gaussianMonomial_of_classes χ h_class)
  have h_sum_dual : 2 * gaussianTheta j (fun n : ℕ ↦ 𝓕⁻ χ n) (q * t)⁻¹ =
      I ^ j.val * t * ∑ a : ZMod q, χ a * S a :=
    two_mul_gaussianTheta _ h_parity_dual h_zero_dual
      (hasSum_invDFT_mul_gaussianMonomial χ h_dual)
  have h_eq : gaussianTheta j (fun n : ℕ ↦ 𝓕⁻ χ n) (q * t)⁻¹ =
      I ^ j.val * t * gaussianTheta j (fun n : ℕ ↦ χ n) t := by
    linear_combination h_sum_dual / 2 - I ^ j.val * t / 2 * h_sum
  rw [h_eq]
  simp [abs_of_pos ht]

/-- **Symmetry.** For primitive `χ ≠ 1` of conductor `q` with `χ(-1) = (-1) ^ j` and `t > 0` we have
`|θ_χ(t)| = |θ_χ(1 / (q t))|`, where `θ_χ(u) = u ^ (1/2) ∑_{n ≥ 1} χ(n) (n u) ^ j e^(-π n² u²)` is
`thetaSeries`. This is the functional equation of the theta series of a primitive character, in
absolute value. -/
theorem norm_thetaSeries_inv (hχ_ne : χ ≠ 1) (hχ_parity : χ (-1) = (-1) ^ j.val)
    (hχ : χ.IsPrimitive) (ht : 0 < t) :
    ‖thetaSeries j (fun n : ℕ ↦ χ n) (q * t)⁻¹‖ = ‖thetaSeries j (fun n : ℕ ↦ χ n) t‖ := by
  have hq : (0 : ℝ) < q := Nat.cast_pos.2 (NeZero.pos q)
  -- `q 𝓕⁻ χ` is a Gauss sum, of modulus `√q`, times the conjugate of `χ`, and `w` is real.
  have h_dual (u : ℝ) : √q * ‖gaussianTheta j (fun n : ℕ ↦ 𝓕⁻ χ n) u‖ =
      ‖gaussianTheta j (fun n : ℕ ↦ χ n) u‖ := by
    have h_coeff (n : ZMod q) : 𝓕⁻ χ n = (q : ℂ)⁻¹ * gaussSum χ stdAddChar * star (χ n) := by
      rw [invDFT_apply', hχ.fourierTransform_eq_inv_mul_gaussSum, neg_neg, smul_eq_mul,
        χ.star_apply', mul_comm (χ⁻¹ n), mul_assoc]
    have h_theta : gaussianTheta j (fun n : ℕ ↦ 𝓕⁻ χ n) u =
        (q : ℂ)⁻¹ * gaussSum χ stdAddChar * star (gaussianTheta j (fun n : ℕ ↦ χ n) u) := by
      simp [gaussianTheta, tsum_star, h_coeff, mul_assoc, ← tsum_mul_left]
    simp [h_theta, norm_gaussSum_of_isPrimitive hχ, field]
  rw [norm_thetaSeries, norm_thetaSeries, ← h_dual,
    ← gaussianTheta_poisson_summation hχ_ne hχ_parity ht, sqrt_inv, sqrt_mul hq.le]
  simp [field, sq_sqrt ht.le]

/-- For `χ ≠ 1` of parity `j ∈ {0, 1}` modulo `q` and `t > 0` the sum `∑_{n ≥ 1} χ(n) w(n t)`, with
`w(z) = z ^ j e^(-π z²)`, has absolute value at most `3 e q e^(-t)`: trivially for `t ≥ 1`, by
Poisson summation for `t ≤ 1`. The character need not be primitive. -/
lemma norm_gaussianTheta_char_le (hχ_ne : χ ≠ 1) (hχ_parity : χ (-1) = (-1) ^ j.val)
    (ht : 0 < t) : ‖gaussianTheta j (fun n : ℕ ↦ χ n) t‖ ≤ 3 * q * rexp 1 * rexp (-t) := by
  obtain h | h := le_total 1 t
  · calc ‖gaussianTheta j (fun n : ℕ ↦ χ n) t‖ ≤ 3 * rexp (-t) / t :=
        (summable_and_norm_gaussianTheta_le (fun n ↦ χ.norm_le_one n) ht).2
      _ ≤ 3 * q * rexp 1 * rexp (-t) := by
        grw [div_le_self (by positivity) h, ← NeZero.one_le (n := q)]
        bound
  -- For `t ≤ 1` pass to `𝓕⁻ χ`, an average of numbers of modulus at most `1`.
  have h_dft (n : ℕ) : ‖𝓕⁻ χ n‖ ≤ 1 := by
    grw [invDFT_apply, norm_smul,
      norm_sum_le_of_le (n := fun _ ↦ (1 : ℝ)) _ fun a _ ↦ by simp [χ.norm_le_one]]
    simp [NeZero.ne q]
  have h_pos : 0 < (q * t)⁻¹ := inv_pos.2 (mul_pos (Nat.cast_pos.2 (NeZero.pos q)) ht)
  refine le_of_mul_le_mul_left ?_ ht
  calc t * ‖gaussianTheta j (fun n : ℕ ↦ χ n) t‖
    _ = ‖gaussianTheta j (fun n : ℕ ↦ 𝓕⁻ χ n) (q * t)⁻¹‖ :=
      gaussianTheta_poisson_summation hχ_ne hχ_parity ht
    _ ≤ 3 * rexp (-(q * t)⁻¹) / (q * t)⁻¹ := (summable_and_norm_gaussianTheta_le h_dft h_pos).2
    _ ≤ 3 * rexp (1 - t) / (q * t)⁻¹ := by gcongr; linarith
    _ = t * (3 * q * rexp 1 * rexp (-t)) := by simp [sub_eq_add_neg, Real.exp_add, field]

/-- For `χ ≠ 1` of parity `j` and `re s > 0`, the Mellin transform of `∑_{n ≥ 1} χ(n) w(n u)` at `s`
is `Γ_j(s) L(s, χ)`, where `Γ_j` is the Mellin transform of `w(z) = z ^ j e^(-π z²)`. This extends
`mellin_gaussianTheta` by analytic continuation. -/
lemma mellin_gaussianTheta_char (hχ_ne : χ ≠ 1) (hχ_parity : χ (-1) = (-1) ^ j.val)
    (hs : 0 < s.re) :
    mellin (gaussianTheta j fun n : ℕ ↦ χ n) s = gaussianMellin j s * χ.LFunction s := by
  -- Both sides are holomorphic for `re s > 0` and agree for `re s > 1` by `mellin_gaussianTheta`.
  let f : ℂ → ℂ := mellin (gaussianTheta j fun n : ℕ ↦ χ n)
  let g (z : ℂ) : ℂ := gaussianMellin j z * χ.LFunction z
  have hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re} :=
    (mellin_differentiableOn_and_bounded
      (fun _ ↦ norm_gaussianTheta_char_le hχ_ne hχ_parity) measurable_gaussianTheta).1
  have hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re} :=
    gaussianMellin_differentiableOn_and_bdd.1.mul (by fun_prop)
  have h_near_two : f =ᶠ[nhds 2] g := .mono ((isOpen_re_gt 1).mem_nhds (by simp)) fun z hz ↦ by
    simp only [f, g, mellin_gaussianTheta (fun n ↦ χ.norm_le_one n) hz, χ.LFunction_eq_LSeries hz]
  exact (hf.analyticOnNhd (isOpen_re_gt 0)).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd (isOpen_re_gt 0)) (convex_halfSpace_re_gt 0).isPreconnected
    (by simp) h_near_two hs

/-- **Riemann's formula.** For `χ ≠ 1` with `χ(-1) = (-1) ^ j` and `re s > 0` the
identity `∫_0^∞ θ_χ(u) u ^ (s - 1/2) du / u = Γ_j(s) L(s, χ)` holds with absolute convergence
(`HasMellin`), where `θ_χ` is `thetaSeries` and `Γ_j` the Mellin transform of
`z ^ j e^(-π z²)`. -/
theorem hasMellin_thetaSeries_char (hχ_ne : χ ≠ 1) (hχ_parity : χ (-1) = (-1) ^ j.val)
    (hs : 0 < s.re) :
    HasMellin (thetaSeries j fun n : ℕ ↦ χ n) (s - 2⁻¹)
      (gaussianMellin j s * χ.LFunction s) := by
  have h_conv : MellinConvergent (gaussianTheta j fun n : ℕ ↦ χ n) s :=
    (mellinConvergent_and_differentiableAt (fun _ ↦ norm_gaussianTheta_char_le hχ_ne hχ_parity)
      measurable_gaussianTheta hs).1
  refine ⟨h_conv.congr_fun (fun _ ht ↦ (cpow_smul_thetaSeries s ht).symm) measurableSet_Ioi, ?_⟩
  rw [mellin_thetaSeries_sub_half, mellin_gaussianTheta_char hχ_ne hχ_parity hs]

/-- For `b, r > 0` with `1 / (b r) = r`, the map `u ↦ 1 / (b u)` takes the interval `(0, r)` onto
`(r, ∞)`. -/
lemma image_inv_const_mul_Ioo {b r : ℝ} (hb : 0 < b) (hr : 0 < r) (h_fix : (b * r)⁻¹ = r) :
    (fun u : ℝ ↦ (b * u)⁻¹) '' Ioo 0 r = Ioi r := by
  ext v
  refine ⟨?_, fun (hv : r < v) ↦ ?_⟩
  · rintro ⟨u, ⟨hu, hur⟩, rfl⟩
    exact h_fix.ge.trans_lt (inv_strictAnti₀ (by positivity) (by gcongr))
  have hv_pos : 0 < v := hr.trans hv
  exact ⟨(b * v)⁻¹, ⟨by positivity, (inv_strictAnti₀ (by positivity) (by gcongr)).trans_eq h_fix⟩,
    by field⟩

/-- The fold: for primitive `χ ≠ 1` of conductor `q` with `χ(-1) = (-1) ^ j`,
`∫_0^∞ |θ_χ(u)| du / u = 2 ∫_{q ^ (-1/2)}^∞ |θ_χ(u)| du / u`, where
`θ_χ(u) = u ^ (1/2) ∑_{n ≥ 1} χ(n) (n u) ^ j e^(-π n² u²)` is `thetaSeries`. -/
lemma integral_norm_thetaSeries_div (hχ_ne : χ ≠ 1) (hχ_parity : χ (-1) = (-1) ^ j.val)
    (hχ : χ.IsPrimitive) :
    ∫ u : ℝ in Ioi 0, ‖thetaSeries j (fun n : ℕ ↦ χ n) u‖ / u =
      2 * ∫ u : ℝ in Ioi (√q)⁻¹, ‖thetaSeries j (fun n : ℕ ↦ χ n) u‖ / u := by
  -- The map `u ↦ 1 / (q u)` has the fixed point `r = q ^ (-1/2)` and preserves `du / u` and
  -- `|θ_χ|`.
  let f (u : ℝ) : ℝ := ‖thetaSeries j (fun n : ℕ ↦ χ n) u‖ / u
  let r : ℝ := (√q)⁻¹
  have hq : (0 : ℝ) < q := Nat.cast_pos.2 (NeZero.pos q)
  have hr : 0 < r := by positivity
  have h_fix : (q * r)⁻¹ = r := by rw [← div_eq_mul_inv, div_sqrt]
  have h_int : IntegrableOn f (Ioi 0) := by
    refine (hasMellin_thetaSeries_char hχ_ne hχ_parity (s := 2⁻¹) (by simp)).1.norm.congr
      (ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : 0 < u) ↦ ?_)
    simp [f, cpow_neg_one, abs_of_pos hu, div_eq_inv_mul]
  have h_deriv (u : ℝ) (hu : u ∈ Ioo 0 r) :
      HasDerivWithinAt (fun u : ℝ ↦ (q * u)⁻¹) (-q / (q * u) ^ 2) (Ioo 0 r) u :=
    (hasDerivAt_const_mul _).hasDerivWithinAt.fun_inv (mul_pos hq hu.1).ne'
  have h_inj : InjOn (fun u : ℝ ↦ (q * u)⁻¹) (Ioo 0 r) := fun u _ v _ h ↦ by simp_all [hq.ne']
  have h_invariant (u : ℝ) (hu : u ∈ Ioo 0 r) : |-q / (q * u) ^ 2| • f (q * u)⁻¹ = f u := by
    have hu_pos : 0 < u := hu.1
    simp only [f, norm_thetaSeries_inv hχ_ne hχ_parity hχ hu_pos, neg_div, abs_neg, smul_eq_mul]
    rw [abs_of_pos (by positivity)]
    field
  have h_fold : ∫ u : ℝ in Ioi r, f u = ∫ u : ℝ in Ioc 0 r, f u := by
    rw [← image_inv_const_mul_Ioo hq hr h_fix,
      integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo h_deriv h_inj,
      setIntegral_congr_fun measurableSet_Ioo h_invariant, integral_Ioc_eq_integral_Ioo]
  calc ∫ u : ℝ in Ioi 0, f u = (∫ u : ℝ in Ioc 0 r, f u) + ∫ u : ℝ in Ioi r, f u := by
        rw [← setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
          (h_int.mono_set Ioc_subset_Ioi_self) (h_int.mono_set (Ioi_subset_Ioi hr.le)),
          Ioc_union_Ioi_eq_Ioi hr.le]
    _ = 2 * ∫ u : ℝ in Ioi r, f u := by rw [← h_fold, two_mul]

end New

end

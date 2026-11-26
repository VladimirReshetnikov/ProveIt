import Lib.Analytic.DirichletTheta
import Lib.Analytic.EntireLFunction

/-!
# A prime `d` in a class whose quadratic twists have no zero in a box

Fix a class modulo `N` whose primes are `≡ 7` modulo `8` and prime to `N`, and a box
`re s ≥ β = 1/2 + 9 δ`, `|im s| ≤ H`. A prime `d` of the class is bad (`IsBadPrime`) if some
`L(s, ξ (·/d))`, with `ξ` modulo `N`, has a zero in the box. The main estimate is the count
`zero_density_quadTwist`: there are `O(X ^ (1 - δ / 2))` bad primes up to `X`. Such a count also
follows from the large sieve inequality for real characters; the proof here needs only the
Pólya–Vinogradov inequality, because theta series keep all sums short.

1. For a primitive character `χ ≠ 1` of conductor `q ≤ T²` let `J(χ, T)` be the integral over
   `u ≥ 1 / T` of `|θ_χ(u)| + |θ_{μχ}(u)|` against `du / u` (`thetaTailIntegral`). If `χ` has parity
   `j`, the Mellin transform of `θ_χ` at `s - 1/2` is `Γ_j L`, and by the functional equation the
   integral of `|θ_χ(u)| du / u` over `u < q ^ (-1/2)` equals that over `u > q ^ (-1/2)`. The
   truncated transform `𝓜` of `θ_{μχ}` (`mollifier`) approximates `Γ_j / L` on `re s = 2`.
2. For large `T` a zero in the box forces `J(χ, T) > T ^ (2 δ)`
   (`eventually_rpow_lt_thetaTailIntegral`). Otherwise `Γ_j L 𝓜 - Γ_j²` is `≪ T ^ (4 δ)` on
   `re s = 1/2` and `≪ 1 / T` on `re s = 2`, so it is small at the zero by the three-lines theorem,
   while it equals `-Γ_j²` there.
3. In the mean over `v ≤ T²` the theta series with coefficients `αₙ (-v/n°)`, where `n°` is the odd
   part of `n`, are small (`sum_sq_thetaSeries_jacobiSym_le`): expand the square, bound the pairs
   with `(n n')°` a square trivially and the others by Pólya–Vinogradov. So the sum of the `J` is
   `≪ T ^ (2 + δ)`.
4. By reciprocity `(n/d) = (-d/n°)`, so 2 and 3 give the count, with `T² = N X`, after passing from
   `ξ` to the primitive character that induces it.
5. If all primes of an invertible class were bad, the sum of `log p / p` over the class would
   converge; it diverges, so some prime of the class is not bad
   (`exists_entireL_quadTwist_ne_zero`).

Notions from other files:
* `gaussianMonomial j` is the weight `w(z) = z ^ j e^(-π z²)` of parity `j`, and `gaussianMellin j`
  is its Mellin transform `Γ_j(s) = ∫_0^∞ w(z) z ^ s dz / z`.
* `thetaSeries j c u` is `θ_c(u) = u ^ (1/2) ∑_{n ≥ 1} c(n) w(n u)`.
* `quadTwist χ d` is the character `χ (·/d)` modulo `N d`, for `χ` modulo `N` and a prime `d`.

## Relation to the literature

Known result: zero density for quadratic twists by mean values over real characters. Sources:
Jutila, On mean values of Dirichlet polynomials with real characters, Acta Arith. 27 (1975);
Heath-Brown, A mean value estimate for real character sums, Acta Arith. 72 (1995). Form here: a weak
density bound for the twists of the characters of a fixed modulus, by a smoothed mean square of
Jacobi symbol sums.
-/

open ArithmeticFunction DirichletCharacter Complex Moebius Finset Real ZMod vonMangoldt LSeries
  Filter jacobiSym legendreSym MeasureTheory Nat NumberTheorySymbols

namespace New

variable {N : ℕ} [NeZero N] (j : Fin 2) {δ : ℝ}

section ThreeLines

open Set HadamardThreeLines

/-- The measure of cancellation `J(c, T) = ∫_{1/T}^∞ (|θ_c(u)| + |θ_{μc}(u)|) du / u` of a sequence
`c`, where `θ_c` is its theta series of parity `j`. -/
noncomputable def thetaTailIntegral (c : ℕ → ℂ) (T : ℝ) : ℝ :=
  ∫ u : ℝ in Ioi T⁻¹, (‖thetaSeries j c u‖ + ‖thetaSeries j (fun n : ℕ ↦ c n * μ n) u‖) / u

/-- The mollifier `𝓜(s) = ∫_{1/T}^∞ θ_{μc}(u) u ^ (s - 1/2) du / u`, where `θ_{μc}` is the theta
series with the coefficients `c(n) μ(n)`. For a character `c = χ` it is the truncated integral for
`Γ_j / L`. -/
noncomputable def mollifier (c : ℕ → ℂ) (T : ℝ) (s : ℂ) : ℂ :=
  ∫ u : ℝ in Ioi T⁻¹, (u : ℂ) ^ (s - 2⁻¹ - 1) • thetaSeries j (fun n : ℕ ↦ c n * μ n) u

variable {j} {c : ℕ → ℂ} {T : ℝ} {z : ℂ}

/-- For `|c(n)| ≤ 1` and `T > 0` the tail integral `J(c, T)` (`thetaTailIntegral`) is the sum of
the tail integrals of `|θ_c(u)| / u` and `|θ_{μc}(u)| / u`. -/
lemma thetaTailIntegral_eq_add (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (hT : 0 < T) :
    thetaTailIntegral j c T = (∫ u : ℝ in Ioi T⁻¹, ‖thetaSeries j c u‖ / u) +
      ∫ u : ℝ in Ioi T⁻¹, ‖thetaSeries j (fun n : ℕ ↦ c n * μ n) u‖ / u := by
  simp_rw [thetaTailIntegral, add_div]
  exact integral_add (integrableOn_norm_thetaSeries_div hc (inv_pos.2 hT))
    (integrableOn_norm_thetaSeries_div (norm_mul_moebius_le_one hc) (inv_pos.2 hT))

lemma integral_norm_thetaSeries_div_nonneg {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ ∫ u : ℝ in Ioi r, ‖thetaSeries j c u‖ / u :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu ↦ div_nonneg (norm_nonneg _) (hr.trans hu.out.le)

/-- For `|c(n)| ≤ 1` and `T > 0` the mollifier `𝓜` of `c`, the transform of the theta series of
`c μ` cut to `u > 1 / T`, is holomorphic in `re s > 0` and bounded on `1/2 ≤ re s ≤ 2`. -/
lemma mollifier_differentiableOn_and_bounded (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (hT : 0 < T) :
    DifferentiableOn ℂ (mollifier j c T) {z : ℂ | 0 < z.re} ∧
    ∃ G : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc 2⁻¹ 2 → ‖mollifier j c T z‖ ≤ G := by
  -- It is the Mellin transform of the series cut to `u > 1 / T`, which is `≪ e^(-u)`.
  let f : ℝ → ℂ := (Ioi T⁻¹).indicator (gaussianTheta j fun n : ℕ ↦ c n * μ n)
  have h_sub : Ioi T⁻¹ ⊆ Ioi 0 := Ioi_subset_Ioi (inv_pos.2 hT).le
  have h_mellin : mollifier j c T = mellin f := by
    ext s
    rw [mellin, ← indicator_smul, setIntegral_indicator measurableSet_Ioi, inter_eq_right.2 h_sub]
    exact setIntegral_congr_fun measurableSet_Ioi fun u hu ↦ cpow_smul_thetaSeries s (h_sub hu)
  have hf (u : ℝ) (hu : 0 < u) : ‖f u‖ ≤ 3 * T * rexp (-u) := by
    by_cases h_cut : u ∈ Ioi T⁻¹
    · calc ‖f u‖ ≤ 3 * rexp (-u) / u := by
            simpa only [f, indicator_of_mem h_cut] using
              (summable_and_norm_gaussianTheta_le (norm_mul_moebius_le_one hc) hu).2
        _ ≤ 3 * rexp (-u) / T⁻¹ := by gcongr; exact h_cut.out.le
        _ = 3 * T * rexp (-u) := by field
    · simpa [f, h_cut] using by positivity
  simpa only [h_mellin] using mellin_differentiableOn_and_bounded hf
    (measurable_gaussianTheta.indicator measurableSet_Ioi)

/-- On `re z = 1/2` we have `|∫_r^∞ θ(u) u ^ (z - 1/2) du / u| ≤ ∫_r^∞ |θ(u)| du / u` for `r ≥ 0`,
as `u ^ (z - 1/2)` has modulus `1`; here `θ` is the theta series of `c`. -/
lemma norm_integral_cpow_smul_thetaSeries_le (hz : z.re = 2⁻¹) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ u : ℝ in Ioi r, (u : ℂ) ^ (z - 2⁻¹ - 1) • thetaSeries j c u‖ ≤
      ∫ u : ℝ in Ioi r, ‖thetaSeries j c u‖ / u := by
  refine (norm_integral_le_integral_norm _).trans_eq
    (setIntegral_congr_fun measurableSet_Ioi fun u (hu : r < u) ↦ ?_)
  simp [norm_cpow_eq_rpow_re_of_pos (hr.trans_lt hu), hz, rpow_neg_one, div_eq_inv_mul]

/-- For `|c(n)| ≤ 1` and `T > 0`, on `re z = 1/2` the mollifier `𝓜` is at most the tail integral
`J(c, T)` in absolute value. -/
lemma norm_mollifier_le (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (hT : 0 < T) (hz : z.re = 2⁻¹) :
    ‖mollifier j c T z‖ ≤ thetaTailIntegral j c T := by
  rw [thetaTailIntegral_eq_add hc hT]
  exact le_add_of_nonneg_of_le (integral_norm_thetaSeries_div_nonneg (inv_pos.2 hT).le)
    (norm_integral_cpow_smul_thetaSeries_le hz (inv_pos.2 hT).le)

/-- For `|c(n)| ≤ 1`, `re z = 2` and `u > 0`, the trivial bound on the theta series `θ` of `c`
gives `|u ^ (z - 1/2) θ(u) / u| ≤ 3 e^(-u)`. -/
lemma norm_cpow_smul_thetaSeries_le (hc : ∀ n : ℕ, ‖c n‖ ≤ 1) (hz : z.re = 2) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ (z - 2⁻¹ - 1) • thetaSeries j c u‖ ≤ 3 * rexp (-u) := by
  have h_pow : ‖(u : ℂ) ^ (z - 2⁻¹ - 1)‖ = √u := by
    norm_num [norm_cpow_eq_rpow_re_of_pos hu, sqrt_eq_rpow, hz]
  grw [norm_smul, h_pow, norm_thetaSeries_le hc hu, mul_div_cancel₀ _ (sqrt_pos.2 hu).ne']

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- For a Dirichlet character `χ`, `T > 0` and `re z = 2` we have
`|Γ_j(z) L(z, χ) 𝓜(z) - Γ_j(z)²| ≤ 9 / T`. Here `Γ_j(s) = ∫_0^∞ w(x) x ^ s dx / x` is
`gaussianMellin`, the Mellin transform of the weight `w` of index `j`.
`𝓜(s) = ∫_{1/T}^∞ θ(u) u ^ (s - 1/2) du / u` is `mollifier`, with
`θ(u) = u ^ (1/2) ∑_{n ≥ 1} χ(n) μ(n) w(n u)`; it is the truncation at `1/T` of an integral for
`Γ_j / L`. -/
lemma norm_mul_mollifier_sub_le (hT : 0 < T) (hz : z.re = 2) :
    ‖gaussianMellin j z * χ.LFunction z * mollifier j (χ ·) T z - gaussianMellin j z ^ 2‖ ≤
      9 / T := by
  -- The difference `Γ_j / L - 𝓜` is the integral over `u ≤ 1 / T`.
  have hz_one : 1 < z.re := by norm_num [hz]
  have hχ (n : ℕ) : ‖χ n‖ ≤ 1 := χ.norm_le_one n
  have h_exp : IntegrableOn (fun u : ℝ ↦ 3 * rexp (-u)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).const_mul 3
  let F (u : ℝ) : ℂ := (u : ℂ) ^ (z - 2⁻¹ - 1) • thetaSeries j (fun n : ℕ ↦ χ n * μ n) u
  have hF (u : ℝ) (hu : 0 < u) : ‖F u‖ ≤ 3 * rexp (-u) :=
    norm_cpow_smul_thetaSeries_le (norm_mul_moebius_le_one hχ) hz hu
  have hF_int : IntegrableOn F (Ioi 0) := h_exp.mono'
    ((measurable_ofReal.pow_const _).smul measurable_thetaSeries).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi hF)
  have h_head : gaussianMellin j z / χ.LFunction z - mollifier j (χ ·) T z =
      ∫ u : ℝ in Ioc 0 T⁻¹, F u := by
    rw [← mellin_thetaSeries_moebius χ hz_one, mellin, mollifier, ← Ioi_sdiff_Ioi,
      setIntegral_sdiff measurableSet_Ioi hF_int (Ioi_subset_Ioi (inv_pos.2 hT).le)]
  have h_head_le : ‖∫ u : ℝ in Ioc 0 T⁻¹, F u‖ ≤ 3 * T⁻¹ := by
    refine (norm_setIntegral_le_of_norm_le_const (C := 3) measure_Ioc_lt_top fun u hu ↦ ?_).trans_eq
      (by simp [hT.le])
    grw [hF u hu.1, exp_le_one_iff.2 (neg_nonpos.2 hu.1.le), mul_one]
  -- By Riemann's formula and the trivial bound, `|Γ_j L| ≤ ∫_0^∞ 3 e^(-u) du = 3`.
  have h_prod : ‖gaussianMellin j z * χ.LFunction z‖ ≤ 3 :=
    calc _ = ‖mellin (thetaSeries j (χ ·)) (z - 2⁻¹)‖ := by
          rw [χ.LFunction_eq_LSeries hz_one, mellin_thetaSeries hχ hz_one]
      _ ≤ ∫ u : ℝ in Ioi 0, 3 * rexp (-u) := norm_integral_le_of_norm_le h_exp
        (ae_restrict_of_forall_mem measurableSet_Ioi fun _ ↦ norm_cpow_smul_thetaSeries_le hχ hz)
      _ = 3 := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  have hL : χ.LFunction z ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (.inr (ne_of_apply_ne re hz_one.ne')) hz_one.le
  calc _ = ‖gaussianMellin j z * χ.LFunction z *
        (mollifier j (χ ·) T z - gaussianMellin j z / χ.LFunction z)‖ := congrArg norm (by field)
    _ ≤ 3 * (3 * T⁻¹) := by grw [norm_mul, norm_sub_rev, h_head, h_prod, h_head_le]
    _ = 9 / T := by ring

/-- Let `χ ≠ 1` be primitive of parity `j` and conductor `q ≤ T²`. On `re z = 1/2` we have
`|Γ_j L| ≤ 2 J` for `T > 0`, where `Γ_j` is `gaussianMellin` and `J` is `thetaTailIntegral`: the
integral of `|θ_χ(u)| / u` over `u > 0` folds at `q ^ (-1/2) ≥ 1 / T`. -/
lemma norm_gaussianMellin_mul_LFunction_le (hχ : χ.IsPrimitive) (hχ_ne : χ ≠ 1)
    (h_parity : χ (-1) = (-1) ^ j.val) (hT : 0 < T) (hq : q ≤ T ^ 2) (hz : z.re = 2⁻¹) :
    ‖gaussianMellin j z * χ.LFunction z‖ ≤ 2 * thetaTailIntegral j (χ ·) T := by
  have hχ_le (n : ℕ) : ‖χ n‖ ≤ 1 := χ.norm_le_one n
  have h_fix : T⁻¹ ≤ (√q)⁻¹ := inv_anti₀ (by simp [NeZero.pos]) (sqrt_le_iff.2 ⟨hT.le, hq⟩)
  calc ‖gaussianMellin j z * χ.LFunction z‖ ≤ ∫ u : ℝ in Ioi 0, ‖thetaSeries j (χ ·) u‖ / u := by
        rw [← (hasMellin_thetaSeries_char hχ_ne h_parity (by norm_num [hz])).2]
        exact norm_integral_cpow_smul_thetaSeries_le hz le_rfl
    _ = 2 * ∫ u : ℝ in Ioi (√q)⁻¹, ‖thetaSeries j (χ ·) u‖ / u :=
      integral_norm_thetaSeries_div hχ_ne h_parity hχ
    _ ≤ 2 * ∫ u : ℝ in Ioi T⁻¹, ‖thetaSeries j (χ ·) u‖ / u := by
      gcongr
      exacts [ae_restrict_of_forall_mem measurableSet_Ioi fun u hu ↦ div_nonneg (norm_nonneg _)
        ((inv_pos.2 hT).trans hu).le, integrableOn_norm_thetaSeries_div hχ_le (inv_pos.2 hT)]
    _ ≤ 2 * thetaTailIntegral j (χ ·) T := by
      grw [thetaTailIntegral_eq_add hχ_le hT,
        ← le_add_of_nonneg_right (integral_norm_thetaSeries_div_nonneg (inv_pos.2 hT).le)]

variable (j) in
/-- For each parity `j` there is a constant `C` with the following property. Let `δ, T > 0`, and let
`χ ≠ 1` be a primitive character of conductor `q ≤ T²` with `χ(-1) = (-1)^j` and
`J(χ, T) ≤ T ^ (2 δ)`, where `J(χ, T) = ∫_{1/T}^∞ (|θ_χ(u)| + |θ_{μχ}(u)|) du / u`
(`thetaTailIntegral`) and `θ_c` is the parity-`j` theta series of `c`. Then every zero `s` of
`L(s, χ)` with `1/2 + 9 δ ≤ re s ≤ 1` satisfies `|Γ_j(s)|² ≤ C T ^ (-2 δ)`, where
`Γ_j(s) = ∫_0^∞ w(z) z ^ s dz / z` (`gaussianMellin`) is the Mellin transform of the parity-`j`
weight `w`. -/
theorem three_lines_bound_of_LFunction_eq_zero :
    ∃ C : ℝ, ∀ {δ T : ℝ} {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ}, 0 < δ →
      χ.IsPrimitive → χ ≠ 1 → χ (-1) = (-1) ^ j.val → 0 < T → q ≤ T ^ 2 →
      thetaTailIntegral j (χ ·) T ≤ T ^ (2 * δ) →
      χ.LFunction s = 0 → 1 / 2 + 9 * δ ≤ s.re → s.re ≤ 1 →
      ‖gaussianMellin j s‖ ^ 2 ≤ C * T ^ (-(2 * δ)) := by
  -- Apply the three-lines theorem on `1/2 ≤ re z ≤ 2` to `Ψ = Γ_j L 𝓜 - Γ_j²`, which is `-Γ_j²`
  -- at the zero, `≪ T ^ (4 δ)` on the left line and `≪ 1 / T` on the right line.
  obtain ⟨hΓ_diff, G, hG⟩ : DifferentiableOn ℂ (gaussianMellin j) {z : ℂ | 0 < z.re} ∧
      ∃ G : ℝ, ∀ z : ℂ, z.re ∈ Set.Icc 2⁻¹ 2 → ‖gaussianMellin j z‖ ≤ G :=
    gaussianMellin_differentiableOn_and_bdd
  set C : ℝ := 9 + G ^ 2
  refine ⟨C, fun {δ T q} _ {χ s} hδ hχ hχ_ne h_parity hT hq hJ h_zero h_re h_re_le ↦ ?_⟩
  have hT_one : 1 ≤ T := (one_le_sq_iff₀ hT.le).1 (hq.trans' (Nat.one_le_cast.2 NeZero.one_le))
  have hχ_le (n : ℕ) : ‖χ n‖ ≤ 1 := χ.norm_le_one n
  let Ψ (z : ℂ) : ℂ :=
    gaussianMellin j z * χ.LFunction z * mollifier j (χ ·) T z - gaussianMellin j z ^ 2
  have h_left (z : ℂ) (hz : z.re = 2⁻¹) : ‖Ψ z‖ ≤ C * T ^ (4 * δ) := by
    have h_sq : T ^ (2 * δ) * T ^ (2 * δ) = T ^ (4 * δ) := by rw [← rpow_add hT]; ring_nf
    have h_prod : ‖gaussianMellin j z * χ.LFunction z‖ ≤ 2 * T ^ (2 * δ) := by
      grw [norm_gaussianMellin_mul_LFunction_le hχ hχ_ne h_parity hT hq hz, hJ]
    have h𝓜 : ‖mollifier j (χ ·) T z‖ ≤ T ^ (2 * δ) := (norm_mollifier_le hχ_le hT hz).trans hJ
    calc ‖Ψ z‖
      _ ≤ 2 * T ^ (2 * δ) * T ^ (2 * δ) + G ^ 2 := by
        grw [norm_sub_le, norm_mul, norm_pow, hG z (by norm_num [hz]), h_prod, h𝓜]
      _ ≤ C * T ^ (4 * δ) := by
        nlinarith [sq_nonneg G, one_le_rpow hT_one (by positivity : 0 ≤ 4 * δ)]
  have h_right (z : ℂ) (hz : z.re = 2) : ‖Ψ z‖ ≤ C * T ^ (-1 : ℝ) := by
    grw [norm_mul_mollifier_sub_le hT hz, rpow_neg_one, div_eq_mul_inv,
      show 9 ≤ C from le_add_of_nonneg_right (sq_nonneg G)]
  -- `Γ_j`, `Γ_j L` and `𝓜` are holomorphic and bounded in the strip.
  obtain ⟨h𝓜_diff, G₂, hG₂⟩ := mollifier_differentiableOn_and_bounded (j := j) hχ_le hT
  obtain ⟨G₁, hG₁⟩ : ∃ G₁ : ℝ, ∀ z : ℂ,
      z.re ∈ Set.Icc 2⁻¹ 2 → ‖mellin (gaussianTheta j (χ ·)) z‖ ≤ G₁ :=
    (mellin_differentiableOn_and_bounded (fun _ ↦ norm_gaussianTheta_char_le hχ_ne h_parity)
      measurable_gaussianTheta).2
  have h_pos {x : ℝ} (hx : x ∈ Set.Icc 2⁻¹ 2) : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have h_diff : DifferentiableOn ℂ Ψ (closure (verticalStrip 2⁻¹ 2)) := by
    have hL_diff : Differentiable ℂ χ.LFunction := differentiable_LFunction hχ_ne
    have hΨ : DifferentiableOn ℂ Ψ {z : ℂ | 0 < z.re} := by fun_prop
    rw [verticalStrip, closure_preimage_re, closure_Ioo (by norm_num)]
    exact hΨ.mono fun z hz ↦ h_pos hz
  have h_bdd : BddAbove (norm ∘ Ψ '' verticalClosedStrip 2⁻¹ 2) := by
    refine ⟨G₁ * G₂ + G ^ 2, forall_mem_image.2 fun z hz ↦ ?_⟩
    change ‖Ψ z‖ ≤ G₁ * G₂ + G ^ 2
    have hG₁_nonneg : 0 ≤ G₁ := (norm_nonneg _).trans (hG₁ z hz)
    grw [norm_sub_le, norm_mul, norm_pow, ← mellin_gaussianTheta_char hχ_ne h_parity (h_pos hz),
      hG z hz, hG₁ z hz, hG₂ z hz]
  -- The line `re z = 2` has the weight `(re s - 1/2) / (3/2) ≥ 6 δ`.
  let weight : ℝ := (s.re - 2⁻¹) / (2 - 2⁻¹)
  have h_weight : 6 * δ ≤ weight := (le_div_iff₀ (by norm_num)).2 (by linarith)
  calc ‖gaussianMellin j s‖ ^ 2 = ‖Ψ s‖ := by simp [Ψ, h_zero]
    _ ≤ (C * T ^ (4 * δ)) ^ (1 - weight) * (C * T ^ (-1 : ℝ)) ^ weight :=
      norm_le_interp_of_mem_verticalClosedStrip' (by norm_num) ⟨by linarith, by linarith⟩
        h_diff.diffContOnCl h_bdd h_left h_right
    _ = C ^ (1 - weight + weight) * T ^ (4 * δ * (1 - weight) + -1 * weight) := by
      simp (disch := positivity) only [mul_rpow, rpow_add, rpow_mul]
      ring
    _ ≤ C * T ^ (-(2 * δ)) := by
      -- The exponent is `4 δ - weight (1 + 4 δ) ≤ 4 δ - 6 δ`.
      have h_exponent : 4 * δ * (1 - weight) + -1 * weight ≤ -(2 * δ) := by nlinarith [h_weight, hδ]
      rw [sub_add_cancel, rpow_one]
      gcongr

variable (j) in
/-- **Three lines.** Let `δ > 0`, let `T` be large in terms of `δ` and the height `H`, and let
`χ ≠ 1` be primitive of conductor `q ≤ T²`, with `χ(-1) = (-1) ^ j`. If `L(s, χ)` has a zero in the
box `re s ≥ 1/2 + 9 δ`, `|im s| ≤ H`, then the integral `J(χ, T)` of `(|θ_χ(u)| + |θ_{μχ}(u)|) / u`
over `u > 1 / T` (`thetaTailIntegral`) exceeds `T ^ (2 δ)`. -/
theorem eventually_rpow_lt_thetaTailIntegral (hδ : 0 < δ) (H : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} {s : ℂ},
      χ.IsPrimitive → χ ≠ 1 → χ (-1) = (-1) ^ j.val → q ≤ T ^ 2 →
      1 / 2 + 9 * δ ≤ s.re → |s.im| ≤ H → χ.LFunction s = 0 →
      T ^ (2 * δ) < thetaTailIntegral j (χ ·) T := by
  obtain ⟨C, hC⟩ := three_lines_bound_of_LFunction_eq_zero j -- `|Γ_j(s)|² ≤ C T ^ (-2 δ)`
  -- `|Γ_j|` has a positive lower bound on the rectangle `1/2 ≤ re s ≤ 1`, `|im s| ≤ H`.
  obtain ⟨c, hc_pos, hc⟩ :
      ∃ c > 0, ∀ s ∈ Set.Icc 2⁻¹ 1 ×ℂ Set.Icc (-H) H, c ≤ ‖gaussianMellin j s‖ :=
    exists_pos_le_norm_gaussianMellin (isCompact_Icc.reProdIm isCompact_Icc)
      fun s hs ↦ lt_of_lt_of_le (by norm_num) (mem_reProdIm.1 hs).1.1
  have h_lim : Tendsto (fun T : ℝ ↦ C * T ^ (-(2 * δ))) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop (by positivity : 0 < 2 * δ)).const_mul C
  filter_upwards [h_lim.eventually_lt_const (pow_pos hc_pos 2), eventually_gt_atTop 0]
    with T h_small hT q _ χ s hχ hχ_ne h_parity hq h_re h_im h_zero
  have h_re_le : s.re ≤ 1 :=
    le_of_not_ge fun hs ↦ χ.LFunction_ne_zero_of_one_le_re (.inl hχ_ne) hs h_zero
  by_contra! hJ
  refine h_small.not_ge ?_
  calc c ^ 2
    _ ≤ ‖gaussianMellin j s‖ ^ 2 := by grw [hc s ⟨⟨by linarith, h_re_le⟩, abs_le.1 h_im⟩]
    _ ≤ C * T ^ (-(2 * δ)) := hC hδ hχ hχ_ne h_parity hT hq hJ h_zero h_re h_re_le

end ThreeLines

lemma norm_jacobiSym_le_one (v : ℤ) (m : ℕ) : ‖(J(v | m) : ℂ)‖ ≤ 1 := by
  obtain h | h | h := trichotomy v m <;> simp [h]

lemma norm_mul_jacobiSym_le_one {α : ℕ → ℂ} (hα : ∀ n : ℕ, ‖α n‖ ≤ 1) (v n : ℕ) :
    ‖α n * J(-v | ordCompl[2] n)‖ ≤ 1 := by
  grw [norm_mul, hα, norm_jacobiSym_le_one, mul_one]

/-- For `b ≠ 0` the Jacobi symbol `(·/b)` is a Dirichlet character modulo `b`: it is built by
twisting with one Legendre symbol at a time. -/
lemma exists_dirichletCharacter_eq_jacobiSym (b : ℕ) :
    ∃ ψ : DirichletCharacter ℂ b, b ≠ 0 → ∀ v : ℤ, ψ v = J(v | b) := by
  induction b using induction_on_primes with
  | zero => simp
  | one => exact ⟨1, fun _ v ↦ by simp [Subsingleton.elim (v : ZMod 1) 1]⟩
  | prime_mul p b hp ih =>
    obtain ⟨ψ, hψ⟩ := ih
    have : Fact p.Prime := ⟨hp⟩
    rw [mul_comm p]
    refine ⟨quadTwist ψ p, fun hbp v ↦ ?_⟩
    have hb : b ≠ 0 := left_ne_zero_of_mul hbp
    rw [quadTwist_apply, hψ hb, to_jacobiSym, mul_right' _ hb hp.ne_zero, Int.cast_mul]

/-- If the odd number `m` is not a square, a character modulo `m` whose values are the Jacobi
symbols `(·/m)` is not principal. -/
lemma dirichletCharacter_jacobiSym_ne_one {m : ℕ} (h_odd : Odd m) (h_not_sq : ¬IsSquare m)
    {ψ : DirichletCharacter ℂ m} (hψ : ∀ v : ℤ, ψ v = J(v | m)) : ψ ≠ 1 := by
  have hm : m ≠ 0 := h_odd.pos.ne'
  have : NeZero m := ⟨hm⟩
  rintro rfl
  -- Write `m = c² a` with `a` squarefree. As `a ≠ 1`, it has a prime factor `p`, which is odd.
  obtain ⟨a, c, -, -, rfl, ha⟩ := Nat.sq_mul_squarefree_of_pos h_odd.pos
  have ha_ne : a ≠ 1 := fun h_eq ↦ h_not_sq ⟨c, by rw [h_eq, mul_one, sq]⟩
  obtain ⟨p, hp, b, rfl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ a := exists_prime_and_dvd ha_ne
  have : Fact p.Prime := ⟨hp⟩
  have hp_two : p ≠ 2 := h_odd.of_mul_right.of_mul_left.ne_two_of_dvd_nat dvd_rfl
  have h_coprime : b.Coprime p := (coprime_of_squarefree_mul ha).symm
  obtain ⟨hc, -, hb⟩ : c ≠ 0 ∧ p ≠ 0 ∧ b ≠ 0 := by simpa using hm
  obtain ⟨ψb, hψb⟩ := exists_dirichletCharacter_eq_jacobiSym b
  -- On units mod `m` we have `(u/c)² = 1`, so the twist of `(·/b)` by `p` would be principal.
  have h_dvd : b * p ∣ c ^ 2 * (p * b) := by simp [mul_comm]
  refine quadTwist_ne_one ψb p hp_two h_coprime ?_
  refine (changeLevel_eq_one_iff h_dvd).1 (MulChar.ext fun u ↦ ?_)
  let v : ℤ := u.1.cast
  have h_symbol : J(v | c) ^ 2 * (J(v | p) * J(v | b)) = 1 := by
    have h_unit : (J(v | c ^ 2 * (p * b)) : ℂ) = 1 := by simp [← hψ, v]
    rw [mul_right' _ (by simpa) (by simp [hb, hp.ne_zero]), mul_right' _ hp.ne_zero hb,
      jacobiSym.pow_right] at h_unit
    exact_mod_cast h_unit
  have h_sq : J(v | c) ^ 2 = 1 := by
    obtain h_c | h_c | h_c := trichotomy v c <;> simp [h_c] at h_symbol ⊢
  have h_twist : quadTwist ψb p v = 1 := by
    rw [h_sq, one_mul, mul_comm] at h_symbol
    rw [quadTwist_apply, hψb hb, to_jacobiSym]
    exact_mod_cast h_symbol
  rwa [changeLevel_eq_cast_of_dvd, ← intCast_cast, MulChar.one_apply_coe]

/-- If the odd number `m` is not a square, the symbol `(·/m)` is a non-principal character, so the
Pólya–Vinogradov inequality gives `|∑_{v ≤ X} (-v/m)| ≤ 2 √m (1 + log m)`. -/
lemma norm_sum_jacobiSym_le {m : ℕ} (h_odd : Odd m) (h_not_sq : ¬IsSquare m) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, (J(-v | m) : ℂ)‖ ≤ 2 * √m * (1 + Real.log m) := by
  have hm : m ≠ 0 := h_odd.pos.ne'
  have : NeZero m := ⟨hm⟩
  obtain ⟨ψ, hψ⟩ := exists_dirichletCharacter_eq_jacobiSym m
  -- We have `(-v/m) = (-1/m) (v/m)`, so a sign comes out of the sum.
  have h_neg (v : ℕ) : (J(-v | m) : ℂ) = ψ (-1) * ψ v := by simp [← hψ hm, ← map_mul]
  calc _ = ‖ψ (-1)‖ * ‖∑ v ∈ Ioc 0 X, ψ v‖ := by simp_rw [h_neg, ← mul_sum, norm_mul]
    _ ≤ 2 * √m * (1 + Real.log m) := by
      grw [ψ.norm_le_one, one_mul,
        polya_vinogradov (dirichletCharacter_jacobiSym_ne_one h_odd h_not_sq (hψ hm)) X]

/-- If the odd part `n°` of `n ≠ 0` is not a square, then, for `δ > 0`, the sums of `(-v/n°)` over
`v ≤ X` are at most `2 (1 + 2 / δ) n ^ (1/2 + δ/2)` in absolute value. -/
lemma norm_sum_jacobiSym_ordCompl_le (hδ : 0 < δ) {n : ℕ} (hn : n ≠ 0)
    (h_not_sq : ¬IsSquare (ordCompl[2] n)) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, (J(-v | ordCompl[2] n) : ℂ)‖ ≤ 2 * (1 + 2 / δ) * (n : ℝ) ^ (1 / 2 + δ / 2) := by
  have hn_pos : (0 : ℝ) < n := by positivity
  have h_odd : _root_.Odd (ordCompl[2] n) := coprime_two_left.1 (coprime_ordCompl prime_two hn)
  have h_log : 1 + Real.log n ≤ (1 + 2 / δ) * (n : ℝ) ^ (δ / 2) := by
    have h_one : 1 ≤ (n : ℝ) ^ (δ / 2) := one_le_rpow (mod_cast hn.bot_lt) (half_pos hδ).le
    have h_le : Real.log n ≤ (n : ℝ) ^ (δ / 2) / (δ / 2) := log_le_rpow_div hn_pos.le (half_pos hδ)
    exact (add_le_add h_one h_le).trans_eq (by field)
  have h_pos : 0 < ordCompl[2] n := h_odd.pos
  have h_le : ordCompl[2] n ≤ n := ordCompl_le n 2
  calc _ ≤ 2 * √n * (1 + Real.log n) := (norm_sum_jacobiSym_le h_odd h_not_sq X).trans (by gcongr)
    _ ≤ 2 * √n * ((1 + 2 / δ) * (n : ℝ) ^ (δ / 2)) := by grw [h_log]
    _ = _ := by rw [rpow_add hn_pos, sqrt_eq_rpow]; ring

/-- For every `A > 0` the weight `w(x) = x ^ j e^(-π x²)` (`gaussianMonomial`) is `≪_A x ^ (-A)`
for `x > 0`. -/
lemma exists_abs_gaussianMonomial_le_rpow {A : ℝ} (hA : 0 < A) :
    ∃ C > (0 : ℝ), ∀ x > (0 : ℝ), |gaussianMonomial j x| ≤ C * x ^ (-A) := by
  refine ⟨3 * A ^ A, by positivity, fun x hx ↦ (norm_gaussianMonomial_le hx.le).trans ?_⟩
  -- From `x / A ≤ e^(x / A)` we get `(x / A) ^ A ≤ e^x`.
  have h_pow : (x / A) ^ A ≤ rexp x := by
    grw [le_exp_of_log_le (log_le_self (div_pos hx hA).le), ← Real.exp_mul,
      div_mul_cancel₀ x hA.ne']
  calc 3 * rexp (-x) ^ 2 ≤ 3 * ((x / A) ^ A)⁻¹ := by
        grw [pow_le_of_le_one (exp_nonneg _) (by simp [hx.le]) two_ne_zero, Real.exp_neg, ← h_pow]
    _ = 3 * A ^ A * x ^ (-A) := by
      rw [div_rpow hx.le hA.le, inv_div, rpow_neg hx.le, div_eq_mul_inv, mul_assoc]

/-- For `A > 0`, `u > 0` and positive integers `n`, `m` we have
`u |w(n u)| |w(m u)| ≪_A u ^ (1 - 2 A) (n m) ^ (-A)`, with `w = gaussianMonomial j` the weight
`x ^ j e^(-π x²)`. -/
lemma exists_mul_abs_gaussianMonomial_mul_le {A : ℝ} (hA : 0 < A) :
    ∃ C > (0 : ℝ), ∀ u > (0 : ℝ), ∀ n m : ℕ+,
      u * |gaussianMonomial j (n * u)| * |gaussianMonomial j (m * u)| ≤
        C * u ^ (1 - 2 * A) * (n * m : ℝ) ^ (-A) := by
  obtain ⟨C, hC_pos, hC⟩ := exists_abs_gaussianMonomial_le_rpow j hA
  refine ⟨C ^ 2, by positivity, fun u hu n m ↦ ?_⟩
  calc u * |gaussianMonomial j (n * u)| * |gaussianMonomial j (m * u)|
    _ ≤ u * (C * (n * u) ^ (-A)) * (C * (m * u) ^ (-A)) := by
      grw [hC _ (by positivity), hC _ (by positivity)]
    _ = C ^ 2 * u ^ (1 - 2 * A) * (n * m : ℝ) ^ (-A) := by
      simp (disch := positivity) only [show 1 - 2 * A = 1 + -A + -A by ring, rpow_add, rpow_one,
        mul_rpow]
      ring

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- For `σ > 1/2` and a positive integer `k`, the terms `(k n m) ^ (-σ)` of the pairs `(n, m)` of
positive integers with `k n m` a square have a nonnegative summable majorant. -/
lemma exists_summable_ge_of_isSquare {σ : ℝ} (hσ : 1 / 2 < σ) (k : ℕ+) :
    ∃ W : ℕ+ × ℕ+ → ℝ, Summable W ∧ (∀ p : ℕ+ × ℕ+, 0 ≤ W p) ∧
      ∀ n m : ℕ+, IsSquare (k * (n * m) : ℕ) → (k * (n * m) : ℝ) ^ (-σ) ≤ W (n, m) := by
  -- Such a pair has `k n = a b²`, `m = a c²`, so `k n m = (a b c)²`. Let `W (n, m)` be the sum of
  -- `(a b c) ^ (-2 σ)` over the triples that give `(n, m)`.
  have h_zeta : Summable fun a : ℕ ↦ ‖(a : ℝ) ^ (2 * -σ)‖ :=
    (summable_nat_rpow.mpr (by linarith)).norm
  let f (x : ℕ × ℕ × ℕ) : ℝ := x.1 ^ (2 * -σ) * (x.2.1 ^ (2 * -σ) * x.2.2 ^ (2 * -σ))
  have hf : Summable f := summable_mul_of_summable_norm h_zeta (h_zeta.mul_norm h_zeta)
  have hf_nonneg (x : ℕ × ℕ × ℕ) : 0 ≤ f x := by positivity
  let pair (x : ℕ × ℕ × ℕ) : ℕ+ × ℕ+ := ((x.1 * x.2.1 ^ 2 / k).toPNat', (x.1 * x.2.2 ^ 2).toPNat')
  refine ⟨fun p ↦ ∑' x : pair ⁻¹' {p}, f x, (hf.hasSum.tsum_fiberwise pair).summable,
    fun p ↦ tsum_nonneg fun _ ↦ hf_nonneg _, fun n m ⟨r, hr⟩ ↦ ?_⟩
  obtain ⟨a, b, c, hn, hm⟩ : ∃ a b c : ℕ, k * n = a * b ^ 2 ∧ m = a * c ^ 2 := by
    -- With `g = gcd(k n, r)`, `k n = b g` and `r = c g` we get `b m = c² g`, so `b ∣ g`.
    obtain ⟨g, b, c, hg, h_cop, hn, rfl⟩ :
        ∃ g b c : ℕ, 0 < g ∧ b.Coprime c ∧ k * n = b * g ∧ r = c * g :=
      exists_coprime' (by simp : 0 < gcd (k * n) r)
    have h_bm : b * m = c ^ 2 * g := Nat.mul_left_cancel hg (by grind)
    obtain ⟨a, rfl⟩ : b ∣ g := (h_cop.pow_right 2).dvd_mul_left.mp ⟨m, h_bm.symm⟩
    exact ⟨a, b, c, by grind, Nat.mul_left_cancel (Nat.pos_of_mul_pos_right hg) (by grind)⟩
  have h_eq : (k * (n * m) : ℝ) ^ (-σ) = f (a, b, c) := by
    rify at hn hm
    have h_sq : (k * (n * m) : ℝ) = (a * (b * c)) ^ 2 := by grind
    simp (disch := positivity) only [f, h_sq, ← mul_rpow, ← rpow_two, ← rpow_mul]
  exact h_eq.trans_le
    ((hf.subtype _).le_tsum ⟨(a, b, c), by simp [pair, ← hn, ← hm]⟩ fun x _ ↦ hf_nonneg x)

/-- For `σ > 1/2`, the terms `(n m) ^ (-σ)` of the pairs `(n, m)` of positive integers for which
the odd part `ordCompl[2] (n m)` is a square, that is `n m = l²` or `2 l²`, have a nonnegative
summable majorant. -/
lemma exists_summable_ge_of_isSquare_ordCompl {σ : ℝ} (hσ : 1 / 2 < σ) :
    ∃ W : ℕ+ × ℕ+ → ℝ, Summable W ∧ (∀ p : ℕ+ × ℕ+, 0 ≤ W p) ∧
      ∀ n m : ℕ+, IsSquare (ordCompl[2] (n * m : ℕ)) → (n * m : ℝ) ^ (-σ) ≤ W (n, m) := by
  choose W hW hW_nonneg hW_ge using exists_summable_ge_of_isSquare hσ
  refine ⟨fun p ↦ W 1 p + 2 ^ σ * W 2 p, (hW 1).add ((hW 2).mul_left _),
    fun p ↦ add_nonneg (hW_nonneg 1 p) (mul_nonneg (by positivity) (hW_nonneg 2 p)),
    fun n m ⟨l, hl⟩ ↦ ?_⟩
  have h_eq : 2 ^ (n * m : ℕ).factorization 2 * (l * l) = n * m := by
    simp only [← hl, ordProj_mul_ordCompl_eq_self]
  -- According to the parity of the exponent of `2`, `n m` or `2 n m` is a square.
  obtain ⟨e, he | he⟩ := ((n * m : ℕ).factorization 2).even_or_odd'
  · rw [he, pow_mul'] at h_eq
    have h_sq : IsSquare ((1 : ℕ+) * (n * m) : ℕ) :=
      ⟨2 ^ e * l, by simp [← h_eq, sq, mul_mul_mul_comm]⟩
    exact le_add_of_le_of_nonneg (by simpa using hW_ge 1 n m h_sq)
      (mul_nonneg (by positivity) (hW_nonneg 2 _))
  · rw [he, pow_succ, pow_mul'] at h_eq
    have h_sq : IsSquare ((2 : ℕ+) * (n * m) : ℕ) :=
      ⟨2 ^ (e + 1) * l, by simp [← h_eq, pow_succ, mul_assoc, mul_left_comm]⟩
    have h_two : (2 ^ (-σ) * (n * m : ℝ) ^ (-σ)) ≤ W 2 (n, m) := by
      simpa [mul_rpow] using hW_ge 2 n m h_sq
    rw [rpow_neg zero_le_two, inv_mul_le_iff₀ (by positivity)] at h_two
    exact le_add_of_nonneg_of_le (hW_nonneg 1 _) h_two

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let `w = gaussianMonomial j` be the weight `z ^ j e^(-π z²)` and `n°` the odd part of `n`. For
`δ > 0` there is a summable `M`, depending only on `δ` and `j`, such that for `T > 0` and
`u ≥ 1 / T` we have `u |w(n u)| |w(m u)| |∑_{v ≤ T²} (-v/(n m)°)| ≤ M (n, m) T² u ^ (-2 δ)`. This
bounds the term of the pair `(n, m)` in the expanded mean square. -/
lemma exists_summable_mul_norm_sum_jacobiSym_le (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ+ × ℕ+ → ℝ, Summable M ∧ ∀ T > (0 : ℝ), ∀ u ≥ T⁻¹, ∀ n m : ℕ+,
      u * |gaussianMonomial j (n * u)| * |gaussianMonomial j (m * u)| *
          ‖∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, (J(-v | ordCompl[2] (n * m : ℕ)) : ℂ)‖ ≤
        M (n, m) * (T ^ 2 * u ^ (-2 * δ)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ :=
    exists_mul_abs_gaussianMonomial_mul_le j (A := 1 / 2 + δ) (by positivity)
  obtain ⟨C₂, hC₂_pos, hC₂⟩ :=
    exists_mul_abs_gaussianMonomial_mul_le j (A := 3 / 2 + δ) (by positivity)
  obtain ⟨W, hW, hW_nonneg, hW_ge⟩ :=
    exists_summable_ge_of_isSquare_ordCompl (σ := 1 / 2 + δ) (by linarith)
  have h_zeta : Summable fun n : ℕ+ ↦ ‖(n : ℝ) ^ (-1 - δ / 2)‖ :=
    summable_pnat_iff_summable_nat.2 (summable_nat_rpow.2 (by linarith)).norm
  let C₃ : ℝ := C₂ * (2 * (1 + 2 / δ))
  refine ⟨fun p ↦ C₁ * W p + C₃ * ((p.1 : ℝ) ^ (-1 - δ / 2) * (p.2 : ℝ) ^ (-1 - δ / 2)),
    (hW.mul_left C₁).add ((summable_mul_of_summable_norm h_zeta h_zeta).mul_left C₃),
    fun T hT u hu n m ↦ ?_⟩
  have hu_pos : 0 < u := (inv_pos.2 hT).trans_le hu
  have hW_pair : 0 ≤ W (n, m) := hW_nonneg _
  by_cases h_sq : IsSquare (ordCompl[2] (n * m : ℕ))
  · -- The sum over `v` is at most `T²`.
    have h_triv : ‖∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, (J(-v | ordCompl[2] (n * m : ℕ)) : ℂ)‖ ≤ T ^ 2 := by
      grw [norm_sum_le_of_le _ fun _ _ ↦ norm_jacobiSym_le_one _ _]
      simpa using floor_le (sq_nonneg T)
    calc _
      _ ≤ C₁ * u ^ (1 - 2 * (1 / 2 + δ)) * W (n, m) * T ^ 2 := by
        grw [hC₁ u hu_pos n m, hW_ge n m h_sq, h_triv]
      _ = C₁ * W (n, m) * (T ^ 2 * u ^ (-2 * δ)) := by ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) (by positivity)
  · -- Pólya–Vinogradov bounds the sum over `v`, and the spare factor `u⁻²` is at most `T²`.
    have hu_sq : u ^ (-2 : ℝ) ≤ T ^ 2 := by
      grw [rpow_neg hu_pos.le, rpow_two, ← hu.le, inv_pow, inv_inv]
    calc _
      _ ≤ C₂ * u ^ (1 - 2 * (3 / 2 + δ)) * (n * m : ℝ) ^ (-(3 / 2 + δ)) *
          (2 * (1 + 2 / δ) * (n * m : ℝ) ^ (1 / 2 + δ / 2)) := by
        grw [hC₂ u hu_pos n m, norm_sum_jacobiSym_ordCompl_le hδ (by positivity) h_sq, Nat.cast_mul]
      _ = C₃ * ((n * m : ℝ) ^ (-(3 / 2 + δ)) * (n * m : ℝ) ^ (1 / 2 + δ / 2)) *
          (u ^ (-2 : ℝ) * u ^ (-2 * δ)) := by
        rw [← rpow_add hu_pos, show -2 + -2 * δ = 1 - 2 * (3 / 2 + δ) by ring]
        ring
      _ ≤ C₃ * ((n : ℝ) ^ (-1 - δ / 2) * (m : ℝ) ^ (-1 - δ / 2)) * (T ^ 2 * u ^ (-2 * δ)) := by
        grw [hu_sq, ← rpow_add (by positivity), show -(3 / 2 + δ) + (1 / 2 + δ / 2) = -1 - δ / 2
          by ring, mul_rpow (by positivity) (by positivity)]
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

/-- **Mean value.** Let `n°` be the odd part of `n`, `w(z) = z ^ j e^(-π z²)` and `δ > 0`. For
`T > 0`, `u ≥ 1 / T` and `|αₙ| ≤ 1`, the theta series `θ_v(u) = u ^ (1/2) ∑ₙ αₙ (-v/n°) w(n u)`
(`thetaSeries`) satisfy `∑_{1 ≤ v ≤ T²} |θ_v(u)|² ≪_δ T² u ^ (-2 δ)`. This is a form of an estimate
of Elliott.

It replaces Heath-Brown's quadratic large sieve: here the coefficients are bounded by `1`, the
weight is fixed, and the effective length `1 / u` of the sums is at most `T`, the square root of the
range of `v`. -/
theorem sum_sq_thetaSeries_jacobiSym_le (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T > (0 : ℝ), ∀ u ≥ T⁻¹, ∀ α : ℕ → ℂ, (∀ n : ℕ, ‖α n‖ ≤ 1) →
      ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, ‖thetaSeries j (fun n : ℕ ↦ α n * J(-v | ordCompl[2] n)) u‖ ^ 2 ≤
        C * (T ^ 2 * u ^ (-2 * δ)) := by
  -- Expand the square into a sum over pairs `(n, m)` with the inner sum `∑_v (-v / (n m)°)`.
  obtain ⟨M, hM, hM_ge⟩ := exists_summable_mul_norm_sum_jacobiSym_le j hδ
  refine ⟨∑' p, M p, fun T hT u hu α hα ↦ ?_⟩
  have hu_pos : 0 < u := (inv_pos.2 hT).trans_le hu
  let a (v : ℕ) (n : ℕ+) : ℂ := √u * (α n * J(-v | ordCompl[2] n) * gaussianMonomial j (n * u))
  let θ (v : ℕ) : ℂ := thetaSeries j (fun n : ℕ ↦ α n * J(-v | ordCompl[2] n)) u
  have ha (v : ℕ) : HasSum (a v) (θ v) := (summable_and_norm_gaussianTheta_le (j := j)
    (norm_mul_jacobiSym_le_one hα v) hu_pos).1.hasSum.mul_left (√u : ℂ)
  have h_expand : HasSum (fun p : ℕ+ × ℕ+ ↦ ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, a v p.1 * star (a v p.2))
      (∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, θ v * star (θ v)) :=
    hasSum_sum fun v _ ↦ (ha v).mul (g := star (a v)) (ha v).star
      (summable_mul_of_summable_norm (ha v).summable.norm (ha v).summable.star.norm)
  have h_pair (n m : ℕ+) (v : ℕ) : a v n * star (a v m) =
      α n * star (α m) * (u * gaussianMonomial j (n * u) * gaussianMonomial j (m * u) : ℝ) *
        J(-v | ordCompl[2] (n * m : ℕ)) := by
    have h_sqrt : (√u : ℂ) * √u = u := mod_cast mul_self_sqrt hu_pos.le
    rw [ordCompl_mul, mul_right' _ (ordCompl_pos 2 n.ne_zero).ne' (ordCompl_pos 2 m.ne_zero).ne']
    simp only [a, star_mul', star_intCast, star_def, conj_ofReal, ofReal_mul, Int.cast_mul]
    linear_combination α n * (starRingEnd ℂ) (α m) * gaussianMonomial j (n * u) *
      gaussianMonomial j (m * u) * J(-v | ordCompl[2] n) * J(-v | ordCompl[2] m) * h_sqrt
  calc ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, ‖θ v‖ ^ 2
    _ ≤ ‖∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, θ v * star (θ v)‖ := by
      simp_rw [star_def, mul_conj']
      exact mod_cast le_norm_self _
    _ ≤ _ := h_expand.norm_le_of_bounded (hM.hasSum.mul_right _) fun (n, m) ↦ by
      calc ‖∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, a v n * star (a v m)‖
        _ = ‖α n‖ * ‖α m‖ * (u * |gaussianMonomial j (n * u)| * |gaussianMonomial j (m * u)|) *
            ‖∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, (J(-v | ordCompl[2] (n * m : ℕ)) : ℂ)‖ := by
          rw [sum_congr rfl fun v _ ↦ h_pair n m v, ← mul_sum]
          simp [abs_of_pos hu_pos]
        _ ≤ M (n, m) * (T ^ 2 * u ^ (-2 * δ)) := by
          grw [hα, hα, one_mul, one_mul, hM_ge T hT u hu n m]

/-- For `|αₙ| ≤ 1` let `θ_v(u) = u ^ (1/2) ∑_{n ≥ 1} αₙ (-v/n°) w(n u)` be the `thetaSeries` with
the weight `w` of index `j`. Here `(-v/n°)` is the Jacobi symbol and `n°` is the odd part of `n`.
For `δ > 0` there is a `C` such that for all `T > 0` and all such `α` we have `∑_{0 < v ≤ T²}
∫_{1/T}^∞ |θ_v(u)| du / u ≤ C T ^ (2 + δ)`, the sum being over all `v`, prime or not: by
Cauchy–Schwarz and the mean value estimate, `∑_{v ≤ T²} |θ_v(u)| ≪ T² u ^ (-δ)` for `u ≥ 1 / T`. -/
lemma sum_integral_norm_thetaSeries_div_le (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T > (0 : ℝ), ∀ α : ℕ → ℂ, (∀ n : ℕ, ‖α n‖ ≤ 1) →
      ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊,
          ∫ u : ℝ in Set.Ioi T⁻¹, ‖thetaSeries j (fun n : ℕ ↦ α n * J(-v | ordCompl[2] n)) u‖ / u ≤
        C * T ^ (2 + δ) := by
  obtain ⟨C, hC⟩ := sum_sq_thetaSeries_jacobiSym_le j hδ
  refine ⟨√C / δ, fun T hT α hα ↦ ?_⟩
  let θ (v : ℕ) : ℝ → ℂ := thetaSeries j fun n : ℕ ↦ α n * J(-v | ordCompl[2] n)
  have h_int (v : ℕ) : IntegrableOn (fun u ↦ ‖θ v u‖ / u) (Set.Ioi T⁻¹) :=
    integrableOn_norm_thetaSeries_div (norm_mul_jacobiSym_le_one hα v) (inv_pos.2 hT)
  have h_mean (u : ℝ) (hu : T⁻¹ < u) :
      ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, ‖θ v u‖ ≤ √C * T ^ 2 * u ^ (-δ) := by
    have hu_pos : 0 < u := (inv_pos.2 hT).trans hu
    calc ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, ‖θ v u‖
      _ ≤ √(T ^ 2 * (C * (T ^ 2 * u ^ (-2 * δ)))) := by
        grw [le_sqrt_of_sq_le sq_sum_le_card_mul_sum_sq, Nat.card_Ioc, Nat.sub_zero,
          floor_le (sq_nonneg T), hC T hT u hu.le α hα]
      _ = √C * T ^ 2 * u ^ (-δ) := by
        rw [mul_left_comm, sqrt_mul' _ (by positivity), mul_assoc]
        rw [show T ^ 2 * (T ^ 2 * u ^ (-2 * δ)) = (T ^ 2 * u ^ (-δ)) ^ 2 by
          simp [field, mul_pow, ← rpow_mul_natCast hu_pos.le, mul_comm δ], sqrt_sq (by positivity)]
  calc ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, ∫ u : ℝ in Set.Ioi T⁻¹, ‖θ v u‖ / u
    _ = ∫ u : ℝ in Set.Ioi T⁻¹, ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, ‖θ v u‖ / u :=
      (integral_finsetSum _ fun v _ ↦ h_int v).symm
    _ ≤ ∫ u : ℝ in Set.Ioi T⁻¹, √C * T ^ 2 * u ^ (-δ - 1) := by
      refine setIntegral_mono_on (integrable_finsetSum _ fun v _ ↦ h_int v)
        ((integrableOn_Ioi_rpow_of_lt (by linarith) (inv_pos.2 hT)).const_mul _) measurableSet_Ioi
        fun u (hu : T⁻¹ < u) ↦ ?_
      have hu_pos : 0 < u := (inv_pos.2 hT).trans hu
      grw [← sum_div, h_mean u hu, rpow_sub_one hu_pos.ne', mul_div_assoc]
    _ = √C / δ * T ^ (2 + δ) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) (inv_pos.2 hT)]
      simp [field, inv_rpow hT.le, rpow_neg hT.le, rpow_add hT]

/-- For `δ, T > 0` and `|αₙ| ≤ 1`, the sum over `v ≤ T²` of `thetaTailIntegral` (the integral over
`u > 1 / T` of `|θ_c(u)| + |θ_{μc}(u)|` against `du / u`) for the coefficients `cₙ = αₙ (-v/n°)` is
`≪_δ T ^ (2 + δ)`, where `n°` is the odd part of `n`. -/
lemma sum_thetaTailIntegral_le (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ T > (0 : ℝ), ∀ α : ℕ → ℂ, (∀ n : ℕ, ‖α n‖ ≤ 1) →
      ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, thetaTailIntegral j (fun n : ℕ ↦ α n * J(-v | ordCompl[2] n)) T ≤
        C * T ^ (2 + δ) := by
  obtain ⟨C, hC⟩ := sum_integral_norm_thetaSeries_div_le j hδ
  refine ⟨C + C, fun T hT α hα ↦ ?_⟩
  -- The coefficients of `θ_{μc}` are those of `θ_c` with `α` replaced by `α μ`.
  simp_rw [thetaTailIntegral_eq_add (norm_mul_jacobiSym_le_one hα _) hT, mul_right_comm (α _),
    sum_add_distrib, add_mul]
  exact add_le_add (hC T hT α hα) (hC T hT _ (norm_mul_moebius_le_one hα))

/-- For a prime `d ≡ 7 mod 8` and `n ≠ 0`, `(2/d) = 1` and reciprocity give `(n/d) = (-d/n°)`, with
`n°` the odd part of `n`. -/
lemma legendreSym_eq_jacobiSym_ordCompl {d : ℕ} [Fact d.Prime] (h8 : d % 8 = 7) {n : ℕ}
    (hn : n ≠ 0) : legendreSym d n = J(-d | ordCompl[2] n) := by
  obtain ⟨k, m, hm, rfl⟩ := exists_eq_two_pow_mul_odd hn
  have hd : Odd d := odd_iff.2 (by omega)
  have h_two : J(2 | d) = 1 := by
    rw [jacobiSym.at_two hd, χ₈_nat_mod_eight, h8]
    rfl
  calc legendreSym d (2 ^ k * m : ℕ)
    _ = J(m | d) := by simp [to_jacobiSym, mul_left, pow_left, h_two]
    _ = J(-1 | m) * J(d | m) := by
      rw [quadratic_reciprocity' hm hd, qrSign, χ₄_nat_three_mod_four (by omega)]
    _ = J(-d | ordCompl[2] (2 ^ k * m)) := by
      rw [ordCompl_pow_mul_of_not_dvd k prime_two hm.not_two_dvd_nat, ← mul_left, neg_one_mul]

/-- The twist `quadTwist ψ d` of a primitive character `ψ` mod `M` by the Legendre symbol of an odd
prime `d` that does not divide `M` is primitive. -/
lemma isPrimitive_quadTwist {M d : ℕ} [NeZero M] [Fact d.Prime] {ψ : DirichletCharacter ℂ M}
    (hψ : ψ.IsPrimitive) (h2 : d ≠ 2) (hM : M.Coprime d) : (quadTwist ψ d).IsPrimitive := by
  -- Dividing the twist by one factor leaves the other, so `M` divides `n d` and `d` divides `n M`,
  -- where `n` is the conductor of the twist.
  let ε : DirichletCharacter ℂ d := (chiK d).ringHomComp (algebraMap ℤ ℂ)
  have h_twist (χ : DirichletCharacter ℂ M) :
      quadTwist χ d = χ.changeLevel ⟨d, rfl⟩ * ε.changeLevel (by simp) := rfl
  have hε_ne : ε ≠ 1 := fun h ↦ quadTwist_ne_one 1 d h2 hM (by simp [h_twist, h])
  have hε : ε.conductor = d := ((dvd_prime Fact.out).1 ε.conductor_dvd_level).resolve_left
    (mt eq_one_iff_conductor_eq_one.2 hε_ne)
  have h_dvd (χ : DirichletCharacter ℂ (M * d)) :
      (quadTwist ψ d * χ⁻¹).conductor ∣ (quadTwist ψ d).conductor * χ.conductor := by
    grw [conductor_mul_dvd_lcm_conductor, Nat.lcm_dvd_mul, conductor_inv]
  have hψ_cond : ψ.conductor = M := hψ
  have hMn : M ∣ (quadTwist ψ d).conductor * d := by
    simpa [h_twist, conductor_changeLevel, hε, hψ_cond] using h_dvd (ε.changeLevel (by simp))
  have hdn : d ∣ (quadTwist ψ d).conductor * M := by
    simpa [h_twist, conductor_changeLevel, mul_comm, hε, hψ_cond]
      using h_dvd (ψ.changeLevel ⟨d, rfl⟩)
  exact (quadTwist ψ d).conductor_dvd_level.antisymm
    (hM.mul_dvd_of_dvd_of_dvd (hM.dvd_mul_right.mp hMn) (hM.symm.dvd_mul_right.mp hdn))

/-- The number `d` is a prime, and the `L`-function of the twist `ψ (·/d)` (`quadTwist ψ d`) has a
zero in the box `re s ≥ β`, `|im s| ≤ H`. -/
structure IsPrimeWithTwistZero (ψ : DirichletCharacter ℂ N) (β H : ℝ) (d : ℕ) : Prop where
  /-- The number `d` is prime. -/
  [prime : Fact d.Prime]
  /-- The function `L(s, ψ (·/d))` vanishes at a point of the box. -/
  exists_zero : ∃ s : ℂ, β ≤ s.re ∧ |s.im| ≤ H ∧ (quadTwist ψ d).LFunction s = 0

open scoped Classical in
/-- Let `ψ` be primitive modulo `M`, `δ > 0` and `H` real. Then only `O(T ^ (2 - δ))` primes
`d ≡ 7 mod 8` with `M d ≤ T²` and prime to `M` have a twist `ψ (·/d)` whose `L`-function has a zero
in the box `re s ≥ 1/2 + 9 δ`, `|im s| ≤ H` (`IsPrimeWithTwistZero`): each has
`thetaTailIntegral > T ^ (2 δ)`, and the sum of these integrals is `≪ T ^ (2 + δ)`. -/
lemma exists_card_zero_quadTwist_le {δ : ℝ} (hδ : 0 < δ) (H : ℝ) {M : ℕ} [NeZero M]
    {ψ : DirichletCharacter ℂ M} (hψ : ψ.IsPrimitive) :
    ∃ C : ℝ, ∀ᶠ T : ℝ in atTop,
      #{d ∈ Ioc 0 ⌊T ^ 2⌋₊ | d % 8 = 7 ∧ M.Coprime d ∧ M * d ≤ T ^ 2 ∧
        IsPrimeWithTwistZero ψ (1 / 2 + 9 * δ) H d} ≤ C * T ^ (2 - δ) := by
  -- The parity `j` of the twists does not depend on `d`: it is opposite to that of `ψ`.
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, ψ (-1) = -(-1) ^ j.val := ψ.even_or_odd.elim
    (fun h ↦ ⟨1, h.trans (by norm_num)⟩) fun h ↦ ⟨0, h.trans (by norm_num)⟩
  obtain ⟨C, hC⟩ := sum_thetaTailIntegral_le j hδ
  refine ⟨C, ?_⟩
  filter_upwards [eventually_rpow_lt_thetaTailIntegral j hδ H, eventually_gt_atTop 0]
    with T h_lines hT
  let F (v : ℕ) : ℝ := thetaTailIntegral j (fun n : ℕ ↦ ψ n * J(-v | ordCompl[2] n)) T
  have h_large (d : ℕ) (h8 : d % 8 = 7) (hM : M.Coprime d) (hd : M * d ≤ T ^ 2)
      (h_twist : IsPrimeWithTwistZero ψ (1 / 2 + 9 * δ) H d) : T ^ (2 * δ) < F d := by
    have : Fact d.Prime := h_twist.prime
    obtain ⟨s, h_re, h_im, h_zero⟩ := h_twist.exists_zero
    have h_par : quadTwist ψ d (-1) = (-1) ^ j.val := by
      simpa [hj, legendreSym.at_neg_one (show d ≠ 2 by omega),
        χ₄_nat_three_mod_four (show d % 4 = 3 by omega)] using quadTwist_apply ψ d (-1)
    have h_coeff (n : ℕ+) : quadTwist ψ d n = ψ n * J(-d | ordCompl[2] (n : ℕ)) := by
      simpa [legendreSym_eq_jacobiSym_ordCompl h8 n.ne_zero] using quadTwist_apply ψ d (n : ℕ)
    simpa only [F, thetaTailIntegral, thetaSeries, gaussianTheta, h_coeff] using
      h_lines (isPrimitive_quadTwist hψ (by omega) hM) (quadTwist_ne_one ψ d (by omega) hM)
        h_par (mod_cast hd) h_re h_im h_zero
  have hF (v : ℕ) : 0 ≤ F v := setIntegral_nonneg measurableSet_Ioi fun u hu ↦
    div_nonneg (by positivity) ((inv_pos.2 hT).trans hu).le
  -- The number of these primes times `T ^ (2 δ)` is at most `∑ F v`.
  refine le_of_mul_le_mul_right ?_ (rpow_pos_of_pos hT (2 * δ))
  let S : Finset ℕ := {d ∈ Ioc 0 ⌊T ^ 2⌋₊ | d % 8 = 7 ∧ M.Coprime d ∧ M * d ≤ T ^ 2 ∧
    IsPrimeWithTwistZero ψ (1 / 2 + 9 * δ) H d}
  calc #S * T ^ (2 * δ)
    _ ≤ ∑ d ∈ S, F d := by
      simpa using card_nsmul_le_sum S F _ fun d hd_mem ↦
        have ⟨_, h8, hM, hd, h_twist⟩ := mem_filter.1 hd_mem
        (h_large d h8 hM hd h_twist).le
    _ ≤ ∑ v ∈ Ioc 0 ⌊T ^ 2⌋₊, F v :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun v _ _ ↦ hF v
    _ ≤ C * T ^ (2 + δ) := hC T hT _ fun n ↦ ψ.norm_le_one n
    _ = C * T ^ (2 - δ) * T ^ (2 * δ) := by
      rw [mul_assoc, ← rpow_add hT]
      ring_nf

/-- A prime `d` of the class `a` modulo `N` is bad if some `L(s, ξ (·/d))`, with `ξ` modulo `N`, has
a zero in the box `re s ≥ β`, `|im s| ≤ H`. -/
def IsBadPrime (a : ZMod N) (β H : ℝ) (d : ℕ) : Prop :=
  (d : ZMod N) = a ∧ ∃ ξ : DirichletCharacter ℂ N, IsPrimeWithTwistZero ξ β H d

open scoped Classical in
/-- **Bad primes are rare.** Let `β = 1/2 + 9 δ` with `δ > 0`, and let `a` be a class modulo `N` all
of whose primes are `≡ 7 mod 8` and prime to `N` (this holds if `8 ∣ N` and `a ≡ 7 mod 8` is prime
to `N`). The number of primes `d ≤ X` of the class that are bad (`IsBadPrime`: some `L(s, ξ (·/d))`
with `ξ` modulo `N` has a zero with `re s ≥ β`, `|im s| ≤ H`) is `O(X ^ (1 - δ / 2))`. -/
lemma zero_density_quadTwist {N : ℕ} [NeZero N] {δ : ℝ} (hδ : 0 < δ) (H : ℝ) {a : ZMod N}
    (h_class : ∀ d : ℕ, d.Prime → (d : ZMod N) = a → d % 8 = 7 ∧ N.Coprime d) :
    (fun X : ℕ ↦ (#{d ∈ Ioc 0 X | IsBadPrime a (1 / 2 + 9 * δ) H d} : ℝ)) =O[atTop]
      fun X : ℕ ↦ (X : ℝ) ^ (1 - δ / 2) := by
  -- Take `T² = N X`, pass from each `ξ` to the primitive character that induces it, and sum.
  have hN : (0 : ℝ) < N := Nat.cast_pos.2 (NeZero.pos N)
  have h_exists (ξ : DirichletCharacter ℂ N) :
      ∃ (M : ℕ) (hMN : M ∣ N) (ψ : DirichletCharacter ℂ M),
        NeZero M ∧ ψ.IsPrimitive ∧ changeLevel hMN ψ = ξ :=
    exists_isPrimitive_changeLevel_eq ξ
  choose M hMN ψ hM hψ h_induced using h_exists
  let S (ξ : DirichletCharacter ℂ N) (T : ℝ) : Finset ℕ :=
    {d ∈ Ioc 0 ⌊T ^ 2⌋₊ | d % 8 = 7 ∧ (M ξ).Coprime d ∧ M ξ * d ≤ T ^ 2 ∧
      IsPrimeWithTwistZero (ψ ξ) (1 / 2 + 9 * δ) H d}
  have h_card (ξ : DirichletCharacter ℂ N) :
      ∃ C : ℝ, ∀ᶠ T : ℝ in atTop, #(S ξ T) ≤ C * T ^ (2 - δ) :=
    exists_card_zero_quadTwist_le hδ H (hψ ξ)
  choose C hC using h_card
  have h_tendsto : Tendsto (fun X : ℕ ↦ √(N * X)) atTop atTop :=
    tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.const_mul_atTop hN)
  refine .of_bound ((∑ ξ, C ξ) * N ^ (1 - δ / 2)) ?_
  -- The bounds for all `ξ` hold at `T = √(N X)` once `X` is large.
  filter_upwards [h_tendsto.eventually (eventually_all.2 hC)] with X hX
  set T : ℝ := √(N * X)
  have hT : T ^ 2 = N * X := sq_sqrt (by positivity)
  have h_pow : T ^ (2 - δ) = N ^ (1 - δ / 2) * X ^ (1 - δ / 2) := by
    rw [← mul_rpow hN.le X.cast_nonneg, ← hT, ← rpow_natCast_mul (sqrt_nonneg _), Nat.cast_ofNat,
      mul_one_sub, mul_div_cancel₀ δ two_ne_zero]
  suffices h_subset : {d ∈ Ioc 0 X | IsBadPrime a (1 / 2 + 9 * δ) H d} ⊆ univ.biUnion (S · T) by
    rw [Real.norm_natCast, norm_of_nonneg (by positivity), mul_assoc, ← h_pow, sum_mul]
    calc (#{d ∈ Ioc 0 X | IsBadPrime a (1 / 2 + 9 * δ) H d} : ℝ)
      _ ≤ ∑ ξ, (#(S ξ T) : ℝ) := mod_cast (card_le_card h_subset).trans card_biUnion_le
      _ ≤ ∑ ξ, C ξ * T ^ (2 - δ) := sum_le_sum fun ξ _ ↦ hX ξ
  intro d hd
  obtain ⟨hd_mem, hd_class, ξ, h_twist⟩ := mem_filter.1 hd
  have hd_prime : Fact d.Prime := h_twist.prime
  obtain ⟨s, h_re, h_im, h_zero⟩ := h_twist.exists_zero
  obtain ⟨hd_pos, hd_le⟩ := mem_Ioc.1 hd_mem
  obtain ⟨h8, h_coprime⟩ := h_class d hd_prime.out hd_class
  have h_coprime' : (M ξ).Coprime d := h_coprime.of_dvd_left (hMN ξ)
  have h_cond : M ξ * d ≤ N * X := Nat.mul_le_mul (le_of_dvd (NeZero.pos N) (hMN ξ)) hd_le
  -- The `L`-functions of the two twists differ by Euler factors, which do not vanish at `s`.
  have h_level : quadTwist ξ d =
      (quadTwist (ψ ξ) d).changeLevel (Nat.mul_dvd_mul_right (hMN ξ) d) := by
    conv_lhs => rw [← h_induced ξ]
    simp [quadTwist, ← changeLevel_trans]
  have h_zero' : (quadTwist (ψ ξ) d).LFunction s = 0 := by
    rw [h_level, LFunction_changeLevel _ _ (.inl (quadTwist_ne_one _ d (by omega) h_coprime'))]
      at h_zero
    exact (mul_eq_zero.1 h_zero).resolve_right (prod_euler_factor_ne_zero _ (by linarith))
  have h_cond' : (M ξ : ℝ) * d ≤ T ^ 2 :=
    (mod_cast h_cond : (M ξ : ℝ) * d ≤ N * X).trans hT.ge
  refine mem_biUnion.2 ⟨ξ, mem_univ ξ, mem_filter.2 ⟨mem_Ioc.2 ⟨hd_pos, ?_⟩,
    h8, h_coprime', h_cond', ⟨s, h_re, h_im, h_zero'⟩⟩⟩
  rw [hT, ← Nat.cast_mul, floor_natCast]
  exact (Nat.le_mul_of_pos_left d (NeZero.pos _)).trans h_cond

/-- **Choice of the prime.** Let `β > 1/2`, `H` real and `a` an invertible class mod `N` all of
whose primes are `≡ 7 mod 8` and prime to `N`. For some prime `d` of the class no `L(s, ξ (·/d))`,
`ξ` mod `N`, vanishes in `β ≤ re s`, `|im s| ≤ H`. Here `quadTwist ξ d` is `ξ (·/d)`, and
`entireL` is `L`, as the twists are not principal.

The bound on bad primes is played against the divergence of `∑ log p / p` over the class
(Dirichlet), so the prime number theorem for progressions is not needed. -/
lemma exists_entireL_quadTwist_ne_zero {N : ℕ} [NeZero N] {β : ℝ} (H : ℝ) {a : ZMod N}
    (hβ : 1 / 2 < β) (ha : IsUnit a)
    (h_class : ∀ d : Primes, ((d : ℕ) : ZMod N) = a → (d : ℕ) % 8 = 7 ∧ N.Coprime d) :
    ∃ d : Primes, ((d : ℕ) : ZMod N) = a ∧ ∀ (ξ : DirichletCharacter ℂ N) (s : ℂ),
      β ≤ s.re → |s.im| ≤ H → entireL (quadTwist ξ d) s ≠ 0 := by
  classical
  -- We may assume `β < 1`, as a smaller `β` gives a larger box.
  wlog hβ_lt : β < 1 generalizing β with h_lt_one
  · obtain ⟨d, hd, h_ne⟩ := h_lt_one (β := 3 / 4) (by norm_num) (by norm_num)
    exact ⟨d, hd, fun ξ s h_re ↦ h_ne ξ s (by linarith)⟩
  obtain ⟨δ, rfl⟩ : ∃ δ, β = 1 / 2 + 9 * δ := ⟨(β - 1 / 2) / 9, by ring⟩
  have hδ : 0 < δ := by linarith
  -- If every prime of the class were bad, only `O(X ^ (1 - δ / 2))` of them would be at most `X`,
  -- so `∑ log d / d` over the class would converge.
  by_contra! h_all
  have h_bad (d : Primes) (hd_class : ((d : ℕ) : ZMod N) = a) :
      IsBadPrime a (1 / 2 + 9 * δ) H d := by
    obtain ⟨ξ, s, h_re, h_im, h_zero⟩ := h_all d hd_class
    obtain ⟨h8, h_coprime⟩ := h_class d hd_class
    rw [entireL, ite_eq_right (quadTwist_ne_one ξ _ (by omega) h_coprime)] at h_zero
    exact ⟨hd_class, ξ, ⟨s, h_re, h_im, h_zero⟩⟩
  let f (n : ℕ) : ℂ := if n.Prime ∧ n = a then 1 else 0
  have h_count : (fun X ↦ ∑ n ∈ Icc 1 X, ‖f n‖) =O[atTop] fun X : ℕ ↦ (X : ℝ) ^ (1 - δ / 2) := by
    refine .trans (.of_norm_le fun X ↦ ?_)
      (zero_density_quadTwist hδ H fun d hd ↦ h_class ⟨d, hd⟩)
    simp only [f, apply_ite norm, norm_one, norm_zero, sum_boole, Real.norm_natCast, Nat.cast_le]
    -- Every prime of the class is bad, so it is counted by `zero_density_quadTwist`.
    refine card_le_card fun d hd ↦ ?_
    obtain ⟨hd_mem, hd_prime, hd_class⟩ := mem_filter.1 hd
    exact mem_filter.2 ⟨by simpa [Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero] using hd_mem,
      h_bad ⟨d, hd_prime⟩ hd_class⟩
  have h_conv : LSeriesSummable f (1 - δ / 2 / 2) :=
    LSeriesSummable_of_sum_norm_bigO h_count (by linarith) (by simpa)
  have h_log : LSeriesSummable (logMul f) 1 := LSeriesSummable_logMul_of_lt_re
    (h_conv.abscissaOfAbsConv_le.trans_lt (mod_cast by simpa))
  -- The terms `Λ(p) / p` of the divergent series are those of this one, as `Λ(p) = log p`.
  refine not_summable_residueClass_prime_div ha (h_log.norm.of_norm_bounded fun n ↦ ?_)
  show ‖(if n.Prime then residueClass a n else 0) / n‖ ≤ ‖term (logMul f) 1 n‖
  simp +contextual [f, Set.indicator, term, apply_ite, ite_and, ← natCast_log,
    vonMangoldt_apply_prime]

end New

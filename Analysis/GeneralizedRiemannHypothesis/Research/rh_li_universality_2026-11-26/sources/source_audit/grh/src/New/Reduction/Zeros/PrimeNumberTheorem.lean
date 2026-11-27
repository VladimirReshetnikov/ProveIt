import Lib.Analytic.PrimeNumberTheorem.Tauberian
import Lib.Analytic.PrimeNumberTheorem.ZeroFreeRegion
import New.Reduction.Zeros.PrimeError

/-!
# The prime number theorem for the remainders `R_q`

Let `d` be a prime and `q ≥ 1`. The remainder `R_q(y)` is an integral of the error `𝓔_q(t)` in the
weighted count (`primeRemainder_eq_integral_countError_sub`), so it varies slowly. For odd `d` prime
to `q` its absolute value is at most `(log y) ^ (-B)` for all large `y`, for every natural number
`B`; so it tends to `0`, which characterises the constant `c_q` in its definition.

Notions from other files:
* `lambdaKResidueClass d q n` is `λ(n) = Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q`, and `0` for other
  `n`.
* `entireL ψ` is `L(s, ψ)`, multiplied by `s - 1` if `ψ` is principal; `quadTwist ψ d` is the
  product of `ψ` and the Legendre symbol `(·/d)`.
* `logDerivMean d q` is the function `G_q` that continues `∑ λ(n) n ^ (-s) - s / (φ(q) (s - 1))`
  when `d` is odd and prime to `q`.
* `primeRemainder d q y` is `R_q(y) = ∑_{n ≤ y} λ(n) (1/n - 1/y) - log y / φ(q) - c_q` with
  `c_q = re G_q(1)`.

## Relation to the literature

Known result: Prime number theorem in arithmetic progressions with an error term that saves every
power of the logarithm. It is a case of the Siegel–Walfisz theorem. Source: Montgomery and Vaughan,
Multiplicative Number Theory I, 2007, Cor. 11.19. Form here: the modulus is fixed, and the count is
the smoothed sum `∑_{n ≤ y} λ(n) (1/n - 1/y)` over the prime powers `n ≡ 1` mod `q`; for `d ≡ 3` mod
`4` the primes that split in `ℚ(√-d)` have weight zero.
-/

open ArithmeticFunction.vonMangoldt Complex Filter Finset MeasureTheory Nat Real Topology

namespace New

variable {d : ℕ} [Fact d.Prime] {q : ℕ} [NeZero q]

/-- Chebyshev's bound with a round constant: `∑_{n ≤ z} Λ(n) ≤ 6 z` for `z ≥ 0`. -/
lemma sum_Icc_vonMangoldt_le_six_mul {z : ℝ} (hz : 0 ≤ z) : ∑ n ∈ Icc 0 ⌊z⌋₊, Λ n ≤ 6 * z :=
  calc ∑ n ∈ Icc 0 ⌊z⌋₊, Λ n = Chebyshev.psi z := (Chebyshev.psi_eq_sum_Icc z).symm
    _ ≤ (Real.log 4 + 4) * z := Chebyshev.psi_le_const_mul_self hz
    _ ≤ 6 * z := by gcongr; linarith [log_four_eq, log_two_lt_d9]

variable (d q) in
/-- The error `𝓔_q(t) = ∑_{n ≤ t} λ(n) - t / φ(q)` in the count with the weights
`λ = lambdaKResidueClass d q`, that is `λ(n) = Λ(n) (1 - (n/d))` for `n ≡ 1` mod `q` and `λ(n) = 0`
otherwise. -/
noncomputable def countError (t : ℝ) : ℝ := ∑ n ∈ Icc 0 ⌊t⌋₊, lambdaKResidueClass d q n - t / φ q

/-- Let `d` be a prime and `q ≠ 0`, and let `λ(n) = lambdaKResidueClass d q n` be `Λ(n) (1 - (n/d))`
for `n ≡ 1` mod `q` and `0` otherwise. The error `𝓔_q(t) = countError d q t`, that is
`∑_{n ≤ t} λ(n) - t / φ(q)`, satisfies `|𝓔_q(t)| ≤ 13 t` for `t ≥ 0`, by Chebyshev's bound. -/
lemma abs_countError_le {t : ℝ} (ht : 0 ≤ t) : |countError d q t| ≤ 13 * t := by
  have h_sum : ∑ n ∈ Icc 0 ⌊t⌋₊, lambdaKResidueClass d q n ≤ 2 * (6 * t) := by
    grw [lambdaKResidueClass_le_two_mul_vonMangoldt, ← mul_sum, sum_Icc_vonMangoldt_le_six_mul ht]
  grw [countError, abs_sub, abs_of_nonneg (sum_nonneg fun n _ ↦ lambdaKResidueClass_nonneg d q n),
    abs_of_nonneg (by positivity), h_sum,
    div_le_self ht (mod_cast totient_pos.2 (NeZero.pos q) : (1 : ℝ) ≤ φ q)]
  linarith

omit [NeZero q] in
/-- Let `d` be a prime and let `λ(n) = lambdaKResidueClass d q n` be `Λ(n) (1 - (n/d))` for `n ≡ 1`
mod `q` and `0` otherwise. For the error `𝓔_q(t) = countError d q t`, that is
`∑_{n ≤ t} λ(n) - t / φ(q)`, the function `𝓔_q(t) t⁻²` is integrable on every interval `[y, z]` with
`1 ≤ y ≤ z`. -/
lemma intervalIntegrable_countError_div_sq {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    IntervalIntegrable (fun t : ℝ ↦ countError d q t / t ^ 2) volume y z := by
  have h_ne (t : ℝ) (ht : t ∈ Set.Icc y z) : t ^ 2 ≠ 0 := by positivity [hy.trans ht.1]
  have h_sum : IntegrableOn (fun t : ℝ ↦ (t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, lambdaKResidueClass d q n)
      (Set.Icc y z) := integrableOn_mul_sum_Icc _ (zero_le_one.trans hy)
    (ContinuousOn.integrableOn_Icc (by fun_prop (disch := assumption)))
  have h_main : IntegrableOn (fun t : ℝ ↦ t / φ q / t ^ 2) (Set.Icc y z) :=
    ContinuousOn.integrableOn_Icc (by fun_prop (disch := assumption))
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hyz]
  exact (h_sum.sub h_main).congr (.of_forall fun t ↦ by simp [countError, field])

/-- For `y ≥ 1` the remainder `R_q = primeRemainder d q`, that is `R_q(y) = ∑_{n ≤ y} λ(n) (1/n -
1/y) - log y / φ(q) - c_q` with `c_q = re G_q(1)`, equals `∫₁^y 𝓔_q(t) t⁻² dt - c_q`, where
`𝓔_q(t) = countError d q t` is `∑_{n ≤ t} λ(n) - t / φ(q)`. -/
lemma primeRemainder_eq_integral_countError_sub {y : ℝ} (hy : 1 ≤ y) :
    primeRemainder d q y = (∫ t in 1..y, countError d q t / t ^ 2) - re (logDerivMean d q 1) := by
  have h_sq_ne (t : ℝ) (ht : t ∈ Set.Icc 1 y) : t ^ 2 ≠ 0 := by positivity [ht.1]
  have h_zero : lambdaKResidueClass d q 0 = 0 := by simp [lambdaKResidueClass, residueClass]
  have h_abel : ∑ n ∈ Icc 0 ⌊y⌋₊, lambdaKResidueClass d q n / n =
      (∑ n ∈ Icc 0 ⌊y⌋₊, lambdaKResidueClass d q n) / y +
        ∫ t in Set.Ioc 1 y, (∑ n ∈ Icc 0 ⌊t⌋₊, lambdaKResidueClass d q n) / t ^ 2 := by
    have h_int : IntegrableOn (deriv fun t : ℝ ↦ t⁻¹) (Set.Icc 1 y) := by
      rw [deriv_inv']
      exact ContinuousOn.integrableOn_Icc (by fun_prop (disch := assumption))
    simpa only [deriv_inv', neg_mul, integral_neg, sub_neg_eq_add, ← div_eq_inv_mul] using
      sum_mul_eq_sub_integral_mul₀ (lambdaKResidueClass d q) h_zero y
        (fun t ht ↦ differentiableAt_inv (by positivity [ht.1])) h_int
  have h_log : ∫ t in 1..y, t / φ q / t ^ 2 = y.log / φ q := by
    rw [← div_one y, ← integral_one_div_of_pos one_pos (by linarith), div_one,
      ← intervalIntegral.integral_div]
    exact intervalIntegral.integral_congr fun t _ ↦ by field
  have h_count : ∫ t in 1..y, countError d q t / t ^ 2 =
      (∫ t in 1..y, (∑ n ∈ Icc 0 ⌊t⌋₊, lambdaKResidueClass d q n) / t ^ 2) - y.log / φ q := by
    rw [← h_log, eq_sub_iff_add_eq,
      ← intervalIntegral.integral_add (intervalIntegrable_countError_div_sq le_rfl hy)
        (ContinuousOn.intervalIntegrable_of_Icc hy (by fun_prop (disch := assumption)))]
    simp only [countError, sub_div, sub_add_cancel]
  have h_sum (r : ℕ) : lambdaKSum d q r y =
      (∑ n ∈ Icc 0 ⌊y⌋₊, lambdaKResidueClass d q n / n * n ^ r) / y ^ r := by
    simp [lambdaKSum, Icc_eq_cons_Ioc (Nat.zero_le _), ← Icc_add_one_left_eq_Ioc]
  have h_div_mul_cancel (n : ℕ) : lambdaKResidueClass d q n / n * n = lambdaKResidueClass d q n :=
    div_mul_cancel_of_imp (by simp +contextual [h_zero])
  rw [primeRemainder, h_count, intervalIntegral.integral_of_le hy, h_sum, h_sum]
  simp only [pow_zero, mul_one, div_one, pow_one, h_div_mul_cancel, h_abel]
  ring

/-- Let `d` be a prime and `q ≠ 0`, and let `λ(n) = lambdaKResidueClass d q n` be `Λ(n) (1 - (n/d))`
for `n ≡ 1` mod `q` and `0` otherwise. The remainder `R_q = primeRemainder d q`, that is
`R_q(y) = ∑_{n ≤ y} λ(n) (1/n - 1/y) - log y / φ(q) - c_q`, varies slowly:
`|R_q(z) - R_q(y)| ≤ 13 (z - y) / y` for `1 ≤ y ≤ z`. -/
lemma abs_primeRemainder_sub_le {y z : ℝ} (hy : 1 ≤ y) (hyz : y ≤ z) :
    |primeRemainder d q z - primeRemainder d q y| ≤ 13 * ((z - y) / y) := by
  -- The difference is the integral over `[y, z]` of `𝓔_q(t) t⁻²`, which is at most `13 / y` there.
  have h_bound (t : ℝ) (ht : t ∈ Set.uIoc y z) : ‖countError d q t / t ^ 2‖ ≤ 13 / y := by
    obtain ⟨hyt, -⟩ : y < t ∧ t ≤ z := by rwa [Set.uIoc_of_le hyz] at ht
    have ht_pos : 0 < t := by linarith
    calc ‖countError d q t / t ^ 2‖ ≤ 13 * t / t ^ 2 := by
          grw [norm_eq_abs, abs_div, abs_countError_le ht_pos.le, abs_of_pos (pow_pos ht_pos 2)]
      _ ≤ 13 / y := by grw [hyt]; simp [field]
  calc |primeRemainder d q z - primeRemainder d q y| = ‖∫ t in y..z, countError d q t / t ^ 2‖ := by
        rw [primeRemainder_eq_integral_countError_sub hy,
          primeRemainder_eq_integral_countError_sub (hy.trans hyz),
          sub_sub_sub_cancel_right, intervalIntegral.integral_interval_sub_left
            (intervalIntegrable_countError_div_sq le_rfl (hy.trans hyz))
            (intervalIntegrable_countError_div_sq le_rfl hy), norm_eq_abs]
    _ ≤ 13 / y * |z - y| := intervalIntegral.norm_integral_le_of_norm_le_const h_bound
    _ = 13 * ((z - y) / y) := by rw [abs_of_nonneg (sub_nonneg.2 hyz)]; ring

/-- Let `d` be a prime and `q ≠ 0`. In the variable `v = log y` the remainder
`R_q = primeRemainder d q` is Lipschitz: `|R_q(e^v) - R_q(e^u)| ≤ 26 (v - u)` for
`0 ≤ u ≤ v ≤ u + 1`. -/
lemma abs_primeRemainder_exp_sub_le {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvu : v ≤ u + 1) :
    |primeRemainder d q (rexp v) - primeRemainder d q (rexp u)| ≤ 26 * (v - u) := by
  have h_abs : |v - u| = v - u := abs_of_nonneg (sub_nonneg.2 huv)
  have h_exp : rexp (v - u) - 1 ≤ 2 * (v - u) := by
    linarith [abs_le.1 (abs_exp_sub_one_le (x := v - u) (by linarith))]
  calc |primeRemainder d q (rexp v) - primeRemainder d q (rexp u)| ≤ 13 *
         ((rexp v - rexp u) / rexp u) :=
        abs_primeRemainder_sub_le (one_le_exp hu) (exp_le_exp.2 huv)
    _ = 13 * (rexp (v - u) - 1) := by simp [Real.exp_sub, field]
    _ ≤ 26 * (v - u) := by linarith

/-- For a character `ψ` mod `q` let `L_ψ = entireL ψ` be `L(s, ψ)`, times `s - 1` if `ψ` is
principal, and let `ψ' = quadTwist ψ d` be `ψ (·/d)`. The function `logDerivMean d q`, that is
`(∑_ψ (logDeriv L_ψ' - logDeriv L_ψ) - 1) / φ(q)`, is analytic at every point where no `L_ψ` and no
`L_ψ'` vanishes. -/
lemma analyticAt_logDerivMean {s : ℂ} (h_char : ∀ ψ : DirichletCharacter ℂ q, entireL ψ s ≠ 0)
    (h_twist : ∀ ψ : DirichletCharacter ℂ q, entireL (quadTwist ψ d) s ≠ 0) :
    AnalyticAt ℂ (logDerivMean d q) s := by
  unfold logDerivMean
  fun_prop (disch := simp only [h_char, h_twist, ne_eq, not_false_eq_true]) [logDeriv]

/-- For a character `ψ` mod `q` let `L_ψ = entireL ψ` be `L(s, ψ)`, times `s - 1` if `ψ` is
principal, and let `ψ' = quadTwist ψ d` be `ψ (·/d)`. If all `logDeriv L_ψ` and `logDeriv L_ψ'` have
norm at most `C` at `s`, then `logDerivMean d q = (∑_ψ (logDeriv L_ψ' - logDeriv L_ψ) - 1) / φ(q)`
has norm at most `2 C N + 1` at `s`, where `N` is the number of characters mod `q`. -/
lemma norm_logDerivMean_le {s : ℂ} {C : ℝ}
    (h_char : ∀ ψ : DirichletCharacter ℂ q, ‖logDeriv (entireL ψ) s‖ ≤ C)
    (h_twist : ∀ ψ : DirichletCharacter ℂ q, ‖logDeriv (entireL (quadTwist ψ d)) s‖ ≤ C) :
    ‖logDerivMean d q s‖ ≤ Fintype.card (DirichletCharacter ℂ q) * (2 * C) + 1 := by
  have h_sum : ‖∑ ψ : DirichletCharacter ℂ q, (logDeriv (entireL (quadTwist ψ d)) s -
      logDeriv (entireL ψ) s)‖ ≤ Fintype.card (DirichletCharacter ℂ q) * (2 * C) :=
    (norm_sum_le_of_le univ fun ψ _ ↦ norm_sub_le_of_le (h_twist ψ) (h_char ψ)).trans_eq
      (by simp [← two_mul])
  rw [logDerivMean, norm_div, Complex.norm_natCast]
  exact (div_le_self (norm_nonneg _) (mod_cast totient_pos.2 (NeZero.pos q))).trans
    (norm_sub_le_of_le h_sum norm_one.le)

/-- Let `d` be a prime and `q ≠ 0`. Let `G_q = logDerivMean d q` be the mean over the characters `ψ`
mod `q` of the logarithmic derivatives of `L(s, ψ (·/d)) / L(s, ψ)`, less `1 / φ(q)`; here the
`L`-function of a principal character is multiplied by `s - 1`. For all large `l` the function
`G_q(s) / s` is holomorphic and of norm at most `l²⁶` on `re s ≥ 1 - l⁻²⁶`, `|s| ≤ e^l`. -/
lemma eventually_norm_logDerivMean_div_le : ∀ᶠ l : ℝ in atTop, ∀ s : ℂ,
    1 - 1 / l ^ 26 ≤ s.re → ‖s‖ ≤ rexp l →
      DifferentiableAt ℂ (fun z : ℂ ↦ logDerivMean d q z / z) s ∧
        ‖logDerivMean d q s / s‖ ≤ l ^ 26 := by
  -- The region lies in the zero-free regions `re s ≥ 1 - l⁻²⁵` of the finitely many `L`-functions;
  -- the exponent `26` in place of `25` absorbs the constants.
  set N : ℝ := (Fintype.card (DirichletCharacter ℂ q) : ℝ)
  have h_char : ∀ᶠ l : ℝ in atTop, ∀ (ψ : DirichletCharacter ℂ q) (s : ℂ),
      1 - 1 / l ^ 25 ≤ s.re → ‖s‖ ≤ rexp l →
        entireL ψ s ≠ 0 ∧ ‖logDeriv (entireL ψ) s‖ ≤ 2 * l ^ 25 :=
    eventually_all.2 eventually_norm_logDeriv_entireL_le
  have h_twist : ∀ᶠ l : ℝ in atTop, ∀ (ψ : DirichletCharacter ℂ q) (s : ℂ),
      1 - 1 / l ^ 25 ≤ s.re → ‖s‖ ≤ rexp l →
        entireL (quadTwist ψ d) s ≠ 0 ∧ ‖logDeriv (entireL (quadTwist ψ d)) s‖ ≤ 2 * l ^ 25 :=
    eventually_all.2 fun ψ ↦ eventually_norm_logDeriv_entireL_le (quadTwist ψ d)
  filter_upwards [h_char, h_twist, eventually_ge_atTop (8 * N + 2)]
    with l hl_char hl_twist hl s h_re h_norm
  have hl_two : 2 ≤ l := by linarith [show 0 ≤ N from Nat.cast_nonneg _]
  have hl_one : 1 ≤ l := one_le_two.trans hl_two
  have h_re' : 1 - 1 / l ^ 25 ≤ s.re := by
    linarith [one_div_pow_le_one_div_pow_of_le hl_one (show 25 ≤ 26 by norm_num)]
  have h_half : 1 / 2 ≤ s.re := by
    have h_pow : 2 ≤ l ^ 25 := hl_two.trans (le_self_pow₀ hl_one (by simp))
    linarith [one_div_le_one_div_of_le two_pos h_pow]
  obtain ⟨h_char_ne, h_char_le⟩ := forall_and.1 fun ψ ↦ hl_char ψ s h_re' h_norm
  obtain ⟨h_twist_ne, h_twist_le⟩ := forall_and.1 fun ψ ↦ hl_twist ψ s h_re' h_norm
  constructor
  · exact (analyticAt_logDerivMean h_char_ne h_twist_ne).differentiableAt.fun_div
      differentiableAt_id (ne_zero_of_re_pos (by linarith))
  · calc ‖logDerivMean d q s / s‖ ≤ (N * (2 * (2 * l ^ 25)) + 1) / (1 / 2) := by
          grw [norm_div, norm_logDerivMean_le h_char_le h_twist_le, ← re_le_norm s, ← h_half]
      _ ≤ (8 * N + 2) * l ^ 25 := by linarith [one_le_pow₀ hl_one (n := 25)]
      _ ≤ l ^ 26 := by grw [hl, pow_succ' l 25]

/-- **Prime number theorem** in the class `1` mod `q`, with weights `λ(n) = Λ(n) (1 - (n/d))`. Let
`d` be an odd prime and `q` prime to `d`. For every natural number `B` the remainder
`primeRemainder d q`, that is `R_q(y) = ∑_{n ≤ y, n ≡ 1} λ(n) (1/n - 1/y) - log y / φ(q) - c_q`,
satisfies `|R_q(y)| ≤ (log y) ^ (-B)` for all large `y`, by a Tauberian theorem applied to the
Laplace transform of `v ↦ R_q(e ^ v)`; it also follows from the Siegel–Walfisz theorem. -/
theorem eventually_abs_primeRemainder_le (hd : d ≠ 2) (h_cop : q.Coprime d) (B : ℕ) :
    ∀ᶠ y : ℝ in atTop, |primeRemainder d q y| ≤ 1 / y.log ^ B := by
  -- Apply the Tauberian theorem to `v ↦ R_q(e^v)` and `F(s) = logDerivMean d q s / s`.
  let F : ℂ → ℂ := fun s ↦ logDerivMean d q s / s
  have h_transform (s : ℂ) (hs : 2 < s.re) : (F s - F 1) / (s - 1) =
      ∫ v : ℝ in Set.Ioi 0, (primeRemainder d q (rexp v) : ℂ) * cexp ((1 - s) * v) := by
    simp [F, integral_primeRemainder hd h_cop hs, ofReal_re_logDerivMean_one hd h_cop]
  have h_bound : ∀ᶠ v : ℝ in atTop, |primeRemainder d q (rexp v)| ≤ 1 / v ^ B :=
    eventually_abs_le_inv_pow_of_transform (by fun_prop [primeRemainder, lambdaKSum])
      (fun u v ↦ abs_primeRemainder_exp_sub_le) h_transform eventually_norm_logDerivMean_div_le B
  filter_upwards [tendsto_log_atTop.eventually h_bound, eventually_gt_atTop 0] with y hy hy_pos
  rwa [Real.exp_log hy_pos] at hy

/-- For an odd prime `d` and `q` prime to `d` the remainder `primeRemainder d q` tends to `0` at
infinity. Thus the constant `c_q = re (logDerivMean d q 1)` subtracted in it is the limit of
`∑_{n ≤ y, n ≡ 1 mod q} Λ(n) (1 - (n/d)) (1/n - 1/y) - log y / φ(q)`. -/
theorem tendsto_primeRemainder (hd : d ≠ 2) (h_cop : q.Coprime d) :
    Tendsto (primeRemainder d q) atTop (𝓝 0) := by
  have h_le : ∀ᶠ y : ℝ in atTop, ‖primeRemainder d q y‖ ≤ 1 / y.log := by
    simpa only [pow_one, Real.norm_eq_abs] using eventually_abs_primeRemainder_le hd h_cop 1
  exact squeeze_zero_norm' h_le (tendsto_log_atTop.const_div_atTop 1)

end New

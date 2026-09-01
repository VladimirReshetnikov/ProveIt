import FabiusFunction.HeineTransformation

/-!
# Basic hypergeometric series `ᵣφₛ` and their convergence

The basic hypergeometric series with numerator parameters `a₁, …, a_r` and
denominator parameters `b₁, …, b_s` is

`ᵣφₛ(a; b; q, z) = ∑_{n≥0} (a₁,…,a_r;q)_n / ((q, b₁,…,b_s;q)_n) · ((-1)^n q^{\binom n2})^{1+s-r} z^n`.

Its terms are dominated, uniformly in the parameters, by
`K · (‖q‖^{\binom n2})^{1+s-r} ‖z‖^n` (`QPochhammerInfiniteBounds`), so

* for `r ≤ s` the series converges absolutely for **every** `z`, because of
  the superexponentially small factor `‖q‖^{\binom n2}`;
* for `r = s + 1` it converges absolutely in the unit disc `‖z‖ < 1`.

`₂φ₁` of `HeineTransformation` is the case `r = 2`, `s = 1`.

## Main declarations

* `basicHypergeometricTerm`, `basicHypergeometric`: the terms and the sum.
* `norm_basicHypergeometricTerm_le`: the uniform geometric domination.
* `summable_basicHypergeometricTerm_of_le`: absolute convergence for all `z`
  when `r ≤ s`.
* `summable_basicHypergeometricTerm_of_eq`: absolute convergence for
  `‖z‖ < 1` when `r = s + 1`.
* `twoPhiOneTerm_eq_basicHypergeometricTerm`: `₂φ₁` is the case `r = 2`, `s = 1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- The `n`-th term of `ᵣφₛ(a; b; q, z)`. -/
noncomputable def basicHypergeometricTerm {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜)
    (q z : 𝕜) (n : ℕ) : 𝕜 :=
  (∏ i, finiteQPochhammerIn (as i) q n) /
      (finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (bs j) q n) *
    ((-1) ^ n * q ^ n.choose 2) ^ ((1 + s : ℤ) - r) * z ^ n

/-- The basic hypergeometric series `ᵣφₛ(a; b; q, z)`. -/
noncomputable def basicHypergeometric {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜) (q z : 𝕜) :
    𝕜 :=
  ∑' n : ℕ, basicHypergeometricTerm as bs q z n

omit [CompleteSpace 𝕜] in
/-- `(-‖a‖;‖q‖)_∞ ≥ 0`. -/
theorem qPochhammerInfIn_neg_norm_nonneg {q : 𝕜} (hq : ‖q‖ < 1) (a : 𝕜) :
    0 ≤ qPochhammerInfIn (-‖a‖) ‖q‖ :=
  (norm_nonneg _).trans (norm_finiteQPochhammerIn_le a hq 0)

omit [CompleteSpace 𝕜] in
/-- `₂φ₁` is the case `r = 2`, `s = 1`. -/
theorem twoPhiOneTerm_eq_basicHypergeometricTerm (a b c q z : 𝕜) (n : ℕ) :
    twoPhiOneTerm a b c q z n = basicHypergeometricTerm ![a, b] ![c] q z n := by
  simp [twoPhiOneTerm, basicHypergeometricTerm, Fin.prod_univ_succ]

/-- **Uniform domination of the terms** of `ᵣφₛ` for `r ≤ s + 1`: with
`K = ∏ᵢ (-‖aᵢ‖;‖q‖)_∞ · (-‖q‖;‖q‖)_∞/‖(q;q)_∞‖ · ∏ⱼ (-‖bⱼ‖;‖q‖)_∞/‖(bⱼ;q)_∞‖`,
`‖term n‖ ≤ K · (‖q‖^{\binom n2})^{s+1-r} · ‖z‖^n`. -/
theorem norm_basicHypergeometricTerm_le {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜) {q : 𝕜}
    (hq : ‖q‖ < 1) (hbs : ∀ j, qPochhammerInfIn (bs j) q ≠ 0) (hrs : r ≤ s + 1) (z : 𝕜)
    (n : ℕ) :
    ‖basicHypergeometricTerm as bs q z n‖ ≤
      (∏ i, qPochhammerInfIn (-‖as i‖) ‖q‖) *
          (qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ *
            ∏ j, qPochhammerInfIn (-‖bs j‖) ‖q‖ / ‖qPochhammerInfIn (bs j) q‖) *
        (‖q‖ ^ n.choose 2) ^ (s + 1 - r) * ‖z‖ ^ n := by
  have he : ((1 + s : ℤ) - r) = ((s + 1 - r : ℕ) : ℤ) := by omega
  have hKq0 : 0 ≤ qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ :=
    div_nonneg (qPochhammerInfIn_neg_norm_nonneg hq q) (norm_nonneg _)
  have hA : ‖∏ i, finiteQPochhammerIn (as i) q n‖ ≤ ∏ i, qPochhammerInfIn (-‖as i‖) ‖q‖ := by
    rw [norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ =>
      norm_finiteQPochhammerIn_le (as i) hq n
  have hQB : ‖(finiteQPochhammerIn q q n * ∏ j, finiteQPochhammerIn (bs j) q n)⁻¹‖ ≤
      qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ *
        ∏ j, qPochhammerInfIn (-‖bs j‖) ‖q‖ / ‖qPochhammerInfIn (bs j) q‖ := by
    rw [norm_inv, norm_mul, norm_prod, mul_inv, ← Finset.prod_inv_distrib]
    exact mul_le_mul (inv_norm_finiteQPochhammerIn_le q hq (qPochhammerInfIn_self_ne_zero hq) n)
      (Finset.prod_le_prod (fun j _ => inv_nonneg.mpr (norm_nonneg _)) fun j _ =>
        inv_norm_finiteQPochhammerIn_le (bs j) hq (hbs j) n)
      (Finset.prod_nonneg fun j _ => inv_nonneg.mpr (norm_nonneg _)) hKq0
  have hpow : ‖((-1 : 𝕜) ^ n * q ^ n.choose 2) ^ (s + 1 - r)‖ =
      (‖q‖ ^ n.choose 2) ^ (s + 1 - r) := by
    rw [norm_pow, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_pow]
  rw [basicHypergeometricTerm, he, zpow_natCast, div_eq_mul_inv, norm_mul, norm_mul, norm_mul,
    hpow, norm_pow]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul hA hQB (norm_nonneg _)
      (Finset.prod_nonneg fun i _ => qPochhammerInfIn_neg_norm_nonneg hq (as i)))
    (by positivity)) (by positivity)

/-- **Absolute convergence for every `z`** when `r ≤ s`. -/
theorem summable_basicHypergeometricTerm_of_le {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜)
    {q : 𝕜} (hq : ‖q‖ < 1) (hbs : ∀ j, qPochhammerInfIn (bs j) q ≠ 0) (hrs : r ≤ s) (z : 𝕜) :
    Summable (basicHypergeometricTerm as bs q z) := by
  set K : ℝ := (∏ i, qPochhammerInfIn (-‖as i‖) ‖q‖) *
    (qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ *
      ∏ j, qPochhammerInfIn (-‖bs j‖) ‖q‖ / ‖qPochhammerInfIn (bs j) q‖) with hK
  have hK0 : 0 ≤ K :=
    mul_nonneg (Finset.prod_nonneg fun i _ => qPochhammerInfIn_neg_norm_nonneg hq (as i))
      (mul_nonneg (div_nonneg (qPochhammerInfIn_neg_norm_nonneg hq q) (norm_nonneg _))
        (Finset.prod_nonneg fun j _ =>
          div_nonneg (qPochhammerInfIn_neg_norm_nonneg hq (bs j)) (norm_nonneg _)))
  refine ((summable_pow_choose_two_mul_pow (norm_nonneg q) hq (norm_nonneg z)).mul_left K)
    |>.of_norm_bounded fun n => ?_
  refine (norm_basicHypergeometricTerm_le as bs hq hbs (by omega) z n).trans ?_
  rw [← hK, mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) n))
    hK0
  exact pow_le_of_le_one (pow_nonneg (norm_nonneg q) _) (pow_le_one₀ (norm_nonneg q) hq.le)
    (by omega)

/-- **Absolute convergence in the unit disc** when `r = s + 1`. -/
theorem summable_basicHypergeometricTerm_of_eq {r s : ℕ} (as : Fin r → 𝕜) (bs : Fin s → 𝕜)
    {q : 𝕜} (hq : ‖q‖ < 1) (hbs : ∀ j, qPochhammerInfIn (bs j) q ≠ 0) (hrs : r = s + 1) {z : 𝕜}
    (hz : ‖z‖ < 1) : Summable (basicHypergeometricTerm as bs q z) := by
  set K : ℝ := (∏ i, qPochhammerInfIn (-‖as i‖) ‖q‖) *
    (qPochhammerInfIn (-‖q‖) ‖q‖ / ‖qPochhammerInfIn q q‖ *
      ∏ j, qPochhammerInfIn (-‖bs j‖) ‖q‖ / ‖qPochhammerInfIn (bs j) q‖) with hK
  refine ((summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left K).of_norm_bounded
    fun n => ?_
  refine (norm_basicHypergeometricTerm_le as bs hq hbs (by omega) z n).trans ?_
  rw [← hK, show s + 1 - r = 0 by omega, pow_zero, mul_one]

end Fabius

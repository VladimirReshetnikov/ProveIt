/-
# Bernoulli coefficients and the operator `β(ad_A)` (Section 5.3)

This file defines the coefficients `b⁺ₙ` of the series `β(z) = z/(1 - e^{-z})
= ∑ₙ b⁺ₙ zⁿ` of the accompanying article (`docs/combined`, equation (5.8) and
Proposition 5.3) by the recursion of Proposition 5.3,

  `b⁺₀ = 1`,  `b⁺ₙ = -∑_{j=1}^{n} (-1)^j/(j+1)! · b⁺_{n-j}`  (n ≥ 1),

which says precisely that `β(z) φ(z) = 1` for `φ(z) = (1 - e^{-z})/z =
∑ⱼ (-1)^j/(j+1)! z^j` (the coefficients of `φ` are `phiCoeff` of `BCH.Duhamel`).
It proves:

* `sum_antidiagonal_phiCoeff_bplus`: the Cauchy product identity
  `∑_{j+k=n} φⱼ b⁺ₖ = δ_{n,0}`;
* `abs_bplus_le_one`: `|b⁺ₙ| ≤ 1`, so that `β(T) = ∑ₙ b⁺ₙ Tⁿ` converges for `‖T‖ < 1`;
* `betaAd 𝕂 A = ∑ₙ b⁺ₙ ad_Aⁿ`, the operator `β(ad_A)`, and `phiAd_mul_betaAd`,
  `betaAd_mul_phiAd`: `φ(ad_A) β(ad_A) = β(ad_A) φ(ad_A) = 1` for `‖A‖ < 1/2`.
-/
import BCH.Duhamel

open NormedSpace Finset Finset.Nat

namespace BCH

section Coefficients

/-- The coefficients `(-1)^j/(j+1)!` of `φ(z) = (1 - e^{-z})/z`, as rational numbers. -/
noncomputable def phiCoeffQ (j : ℕ) : ℚ := (-1 : ℚ) ^ j * ((j + 1).factorial : ℚ)⁻¹

/-- The coefficients `b⁺ₙ = B⁺ₙ/n!` of `β(z) = z/(1 - e^{-z})`, defined by the recursion of
Proposition 5.3: `b⁺₀ = 1` and `b⁺_{n+1} = -∑_{j=0}^{n} φ_{j+1} b⁺_{n-j}`. -/
noncomputable def bplus : ℕ → ℚ
  | 0 => 1
  | n + 1 => -∑ j ∈ range (n + 1), phiCoeffQ (j + 1) * bplus (n - j)
termination_by n => n
decreasing_by all_goals simp_wf

@[simp] lemma bplus_zero : bplus 0 = 1 := by simp [bplus]

lemma bplus_succ (n : ℕ) :
    bplus (n + 1) = -∑ j ∈ range (n + 1), phiCoeffQ (j + 1) * bplus (n - j) := by
  rw [bplus]

@[simp] lemma phiCoeffQ_zero : phiCoeffQ 0 = 1 := by simp [phiCoeffQ]

/-- **Proposition 5.3** as the Cauchy product identity `φ(z) β(z) = 1`:
`∑_{j+k=n} φⱼ b⁺ₖ = δ_{n,0}`. -/
theorem sum_antidiagonal_phiCoeffQ_bplus (n : ℕ) :
    ∑ p ∈ antidiagonal n, phiCoeffQ p.1 * bplus p.2 = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Finset.Nat.sum_antidiagonal_succ, phiCoeffQ_zero, one_mul, bplus_succ, if_neg (Nat.succ_ne_zero n)]
    have h : ∑ p ∈ antidiagonal n, phiCoeffQ (p.1 + 1) * bplus p.2 =
        ∑ j ∈ range (n + 1), phiCoeffQ (j + 1) * bplus (n - j) := by
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => phiCoeffQ (i + 1) * bplus j)]
    rw [h]; ring

/-- The symmetric form of the Cauchy product identity. -/
theorem sum_antidiagonal_phiCoeffQ_bplus' (n : ℕ) :
    ∑ p ∈ antidiagonal n, phiCoeffQ p.2 * bplus p.1 = if n = 0 then 1 else 0 := by
  rw [← Finset.Nat.sum_antidiagonal_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  exact sum_antidiagonal_phiCoeffQ_bplus n

lemma two_pow_le_factorial_succ_succ (j : ℕ) : 2 ^ (j + 1) ≤ (j + 2).factorial := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [pow_succ, Nat.factorial_succ (j + 2)]
    calc 2 ^ (j + 1) * 2 ≤ (j + 2).factorial * 2 := Nat.mul_le_mul_right 2 ih
      _ ≤ (j + 2).factorial * (j + 2 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (j + 2 + 1) * (j + 2).factorial := by ring

lemma abs_phiCoeffQ_succ_le (j : ℕ) : |phiCoeffQ (j + 1)| ≤ (2 : ℚ)⁻¹ ^ (j + 1) := by
  rw [phiCoeffQ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_inv, Nat.abs_cast,
    inv_pow]
  have h := two_pow_le_factorial_succ_succ j
  have h' : ((2 : ℚ) ^ (j + 1)) ≤ ((j + 1 + 1).factorial : ℚ) := by exact_mod_cast h
  exact inv_anti₀ (by positivity) h'

lemma sum_inv_two_pow_eq (m : ℕ) : ∑ j ∈ range m, (2 : ℚ)⁻¹ ^ (j + 1) = 1 - (2 : ℚ)⁻¹ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih]
    ring

lemma sum_inv_two_pow_le (m : ℕ) : ∑ j ∈ range m, (2 : ℚ)⁻¹ ^ (j + 1) ≤ 1 := by
  rw [sum_inv_two_pow_eq]
  have : (0 : ℚ) ≤ (2 : ℚ)⁻¹ ^ m := by positivity
  linarith

/-- The coefficients of `β` are bounded by one: `|b⁺ₙ| ≤ 1`. -/
theorem abs_bplus_le_one : ∀ n : ℕ, |bplus n| ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp
    | succ n =>
      rw [bplus_succ, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun j hj => ?_).trans (sum_inv_two_pow_le (n + 1))
      rw [abs_mul]
      calc |phiCoeffQ (j + 1)| * |bplus (n - j)|
          ≤ (2 : ℚ)⁻¹ ^ (j + 1) * 1 :=
            mul_le_mul (abs_phiCoeffQ_succ_le j) (ih (n - j) (by omega)) (abs_nonneg _)
              (by positivity)
        _ = (2 : ℚ)⁻¹ ^ (j + 1) := mul_one _

end Coefficients

section Operator

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The operator `β(ad_A) = ∑ₙ b⁺ₙ ad_Aⁿ`. -/
noncomputable def betaAd (A : 𝔸) : 𝔸 →L[𝕂] 𝔸 := ∑' n : ℕ, ((bplus n : ℚ) : 𝕂) • ad 𝕂 A ^ n

variable {𝕂}

omit [CompleteSpace 𝔸] in
lemma phiCoeff_eq_cast (n : ℕ) : phiCoeff 𝕂 n = ((phiCoeffQ n : ℚ) : 𝕂) := by
  rw [phiCoeff, phiCoeffQ]; push_cast; ring

omit [CompleteSpace 𝔸] in
lemma summable_norm_betaAd_term {A : 𝔸} (hA : ‖A‖ < 1 / 2) :
    Summable fun n : ℕ => ‖((bplus n : ℚ) : 𝕂) • ad 𝕂 A ^ n‖ := by
  have h2A : 2 * ‖A‖ < 1 := by linarith
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (summable_geometric_of_lt_one (by positivity) h2A)
  rw [norm_smul]
  calc ‖((bplus n : ℚ) : 𝕂)‖ * ‖ad 𝕂 A ^ n‖ ≤ 1 * (2 * ‖A‖) ^ n := by
        refine mul_le_mul ?_ (norm_ad_pow_le A n) (norm_nonneg _) zero_le_one
        rw [← RCLike.ofReal_ratCast, RCLike.norm_ofReal, ← Rat.cast_abs]
        exact_mod_cast abs_bplus_le_one n
    _ = (2 * ‖A‖) ^ n := one_mul _

lemma summable_betaAd_term {A : 𝔸} (hA : ‖A‖ < 1 / 2) :
    Summable fun n : ℕ => ((bplus n : ℚ) : 𝕂) • ad 𝕂 A ^ n :=
  Summable.of_norm (f := fun n : ℕ => ((bplus n : ℚ) : 𝕂) • ad 𝕂 A ^ n)
    (summable_norm_betaAd_term hA)

/-- `β(ad_A) H = ∑ₙ b⁺ₙ ad_Aⁿ H`. -/
theorem betaAd_apply {A : 𝔸} (hA : ‖A‖ < 1 / 2) (H : 𝔸) :
    betaAd 𝕂 A H = ∑' n : ℕ, ((bplus n : ℚ) : 𝕂) • (ad 𝕂 A ^ n) H := by
  rw [betaAd, ← ContinuousLinearMap.apply_apply (𝕜 := 𝕂) H,
    ContinuousLinearMap.map_tsum _ (summable_betaAd_term hA)]
  simp only [ContinuousLinearMap.apply_apply, smul_apply]

/-- The Cauchy product of the series `φ(ad_A)` and `β(ad_A)` is the identity. -/
theorem phiAd_mul_betaAd {A : 𝔸} (hA : ‖A‖ < 1 / 2) : phiAd 𝕂 A * betaAd 𝕂 A = 1 := by
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n : ℕ => phiCoeff 𝕂 n • ad 𝕂 A ^ n)
    (g := fun n : ℕ => ((bplus n : ℚ) : 𝕂) • ad 𝕂 A ^ n)
    (summable_norm_phiAd_term A) (summable_norm_betaAd_term hA)
  rw [phiAd, betaAd, hprod]
  have hterm : ∀ n : ℕ, ∑ p ∈ antidiagonal n,
      (phiCoeff 𝕂 p.1 • ad 𝕂 A ^ p.1) * (((bplus p.2 : ℚ) : 𝕂) • ad 𝕂 A ^ p.2) =
      if n = 0 then (1 : 𝔸 →L[𝕂] 𝔸) else 0 := by
    intro n
    have h : ∀ p ∈ antidiagonal n,
        (phiCoeff 𝕂 p.1 • ad 𝕂 A ^ p.1) * (((bplus p.2 : ℚ) : 𝕂) • ad 𝕂 A ^ p.2) =
        ((phiCoeffQ p.1 * bplus p.2 : ℚ) : 𝕂) • ad 𝕂 A ^ n := by
      intro p hp
      rw [mem_antidiagonal] at hp
      rw [smul_mul_smul_comm, ← pow_add, hp, phiCoeff_eq_cast, Rat.cast_mul]
    rw [sum_congr rfl h, ← Finset.sum_smul, ← Rat.cast_sum, sum_antidiagonal_phiCoeffQ_bplus]
    split_ifs with hn
    · subst hn; simp
    · simp
  simp only [hterm]
  exact (hasSum_ite_eq (0 : ℕ) (1 : 𝔸 →L[𝕂] 𝔸)).tsum_eq

/-- The Cauchy product of the series `β(ad_A)` and `φ(ad_A)` is the identity. -/
theorem betaAd_mul_phiAd {A : 𝔸} (hA : ‖A‖ < 1 / 2) : betaAd 𝕂 A * phiAd 𝕂 A = 1 := by
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := fun n : ℕ => ((bplus n : ℚ) : 𝕂) • ad 𝕂 A ^ n)
    (g := fun n : ℕ => phiCoeff 𝕂 n • ad 𝕂 A ^ n)
    (summable_norm_betaAd_term hA) (summable_norm_phiAd_term A)
  rw [phiAd, betaAd, hprod]
  have hterm : ∀ n : ℕ, ∑ p ∈ antidiagonal n,
      (((bplus p.1 : ℚ) : 𝕂) • ad 𝕂 A ^ p.1) * (phiCoeff 𝕂 p.2 • ad 𝕂 A ^ p.2) =
      if n = 0 then (1 : 𝔸 →L[𝕂] 𝔸) else 0 := by
    intro n
    have h : ∀ p ∈ antidiagonal n,
        (((bplus p.1 : ℚ) : 𝕂) • ad 𝕂 A ^ p.1) * (phiCoeff 𝕂 p.2 • ad 𝕂 A ^ p.2) =
        ((phiCoeffQ p.2 * bplus p.1 : ℚ) : 𝕂) • ad 𝕂 A ^ n := by
      intro p hp
      rw [mem_antidiagonal] at hp
      rw [smul_mul_smul_comm, ← pow_add, hp, phiCoeff_eq_cast, Rat.cast_mul, mul_comm]
    rw [sum_congr rfl h, ← Finset.sum_smul, ← Rat.cast_sum, sum_antidiagonal_phiCoeffQ_bplus']
    split_ifs with hn
    · subst hn; simp
    · simp
  simp only [hterm]
  exact (hasSum_ite_eq (0 : ℕ) (1 : 𝔸 →L[𝕂] 𝔸)).tsum_eq

theorem phiAd_betaAd_apply {A : 𝔸} (hA : ‖A‖ < 1 / 2) (x : 𝔸) :
    phiAd 𝕂 A (betaAd 𝕂 A x) = x := by
  rw [← mul_apply_eq_comp, phiAd_mul_betaAd hA, one_apply_eq_self]

theorem betaAd_phiAd_apply {A : 𝔸} (hA : ‖A‖ < 1 / 2) (x : 𝔸) :
    betaAd 𝕂 A (phiAd 𝕂 A x) = x := by
  rw [← mul_apply_eq_comp, betaAd_mul_phiAd hA, one_apply_eq_self]

end Operator

end BCH

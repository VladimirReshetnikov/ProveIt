import ExponentialIdentities.TwoBaseIntegerExponent.HigherDifference
import ExponentialIdentities.TwoBaseIntegerExponent.Localization
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Nat.Choose.Sum

open Set Finset Function Polynomial
open fwdDiff

namespace LeanProofs.TwoBaseIntegerExponent

noncomputable section

/-!
Scratch formalization of the exact polynomial-approximation mechanism in report 8.
The production version should split the lattice-clearing and approximation-floor APIs if desired.
-/

/-- A pointwise error bound on the `r + 1` equally spaced samples controls the
`r`-th forward difference by `2^r E`. -/
theorem abs_iterated_fwdDiff_le_two_pow_mul
    (e : ℝ → ℝ) (r : ℕ) (x h E : ℝ)
    (herr : ∀ k : ℕ, k ≤ r → |e (x + (k : ℝ) * h)| ≤ E) :
    |Δ_[h]^[r] e x| ≤ (2 : ℝ) ^ r * E := by
  rw [fwdDiff_iter_eq_sum_shift]
  calc
    |∑ k ∈ Finset.range (r + 1),
        ((-1 : ℤ) ^ (r - k) * r.choose k) • e (x + k • h)|
        ≤ ∑ k ∈ Finset.range (r + 1),
            |(((-1 : ℤ) ^ (r - k) * r.choose k) • e (x + k • h))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * E := by
      gcongr with k hk
      have hk' : k ≤ r := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have he := herr k hk'
      rw [abs_zsmul]
      norm_num [abs_mul, abs_pow]
      simpa [nsmul_eq_mul] using
        (mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ r.choose k))
    _ = (2 : ℝ) ^ r * E := by
      rw [← Finset.sum_mul]
      congr 1
      exact_mod_cast Nat.sum_range_choose r

/-- A polynomial of degree `< r` has zero `r`-th forward difference for every real step.
Mathlib's primitive theorem is stated for step one; the affine composition below transports it
to the arbitrary-step form needed by the report. -/
theorem Polynomial.fwdDiff_iter_eq_zero_of_natDegree_lt
    (P : ℝ[X]) (r : ℕ) (hdeg : P.natDegree < r) (x h : ℝ) :
    Δ_[h]^[r] P.eval x = 0 := by
  let Q : ℝ[X] := P.comp (C x + C h * X)
  have haff : (C x + C h * X : ℝ[X]).natDegree ≤ 1 := by
    calc
      (C x + C h * X : ℝ[X]).natDegree
          ≤ max (C x : ℝ[X]).natDegree (C h * X : ℝ[X]).natDegree := natDegree_add_le _ _
      _ ≤ 1 := by
        apply max_le
        · simpa using natDegree_C_le x
        · calc
            (C h * X : ℝ[X]).natDegree ≤ (C h : ℝ[X]).natDegree + X.natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 1 := by
              simpa using Nat.add_le_add_right (Polynomial.natDegree_C_le h) 1
  have hQdeg : Q.natDegree < r := by
    refine lt_of_le_of_lt ?_ hdeg
    calc
      Q.natDegree ≤ P.natDegree * (C x + C h * X : ℝ[X]).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ P.natDegree * 1 := Nat.mul_le_mul_left _ haff
      _ = P.natDegree := Nat.mul_one _
  have hzero : Δ_[(1 : ℝ)]^[r] Q.eval 0 = 0 := by
    exact congr_fun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hQdeg) 0
  have hQeval (k : ℕ) : Q.eval (0 + k • (1 : ℝ)) = P.eval (x + k • h) := by
    simp only [Q, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X, zero_add, nsmul_eq_mul, mul_one]
    congr 1
    ring
  rw [fwdDiff_iter_eq_sum_shift] at hzero ⊢
  simp_rw [hQeval] at hzero
  exact hzero

/-- The exact finite-difference approximation floor used in report 8.  This factored form is
definitionally close to the proof: derivative coefficient, mesh width, endpoint curvature,
and the `2^r` triangle-inequality loss. -/
def polynomialApproximationFloor (alpha : ℝ) (d : ℕ) : ℝ :=
  |fallingRpowCoeff alpha (d + 1)| *
      (1 / (d + 1 : ℝ)) ^ (d + 1) *
      (2 : ℝ) ^ (alpha - (d + 1 : ℝ)) /
      (2 : ℝ) ^ (d + 1)

/-! ## Exact denominator clearing -/

/-- Dense degree-at-most-`d` evaluation with integer coefficients, viewed in `ℝ`. -/
def denseIntegerPolynomialEval {d : ℕ} (a : Fin (d + 1) → ℤ) (t : ℝ) : ℝ :=
  ∑ k, (a k : ℝ) * t ^ (k : ℕ)

/-- The integer obtained after clearing the denominator of a dense polynomial at `m/q`. -/
def clearedDenseIntegerPolynomialEval {d : ℕ}
    (a : Fin (d + 1) → ℤ) (m q : ℤ) : ℤ :=
  ∑ k, a k * m ^ (k : ℕ) * q ^ (d - (k : ℕ))

/-- Exact clearing identity for an integer-coefficient polynomial of degree at most `d`. -/
theorem pow_mul_denseIntegerPolynomialEval_div
    {d : ℕ} (a : Fin (d + 1) → ℤ) (m q : ℤ) (hq : q ≠ 0) :
    (q : ℝ) ^ d * denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ)) =
      (clearedDenseIntegerPolynomialEval a m q : ℤ) := by
  rw [denseIntegerPolynomialEval, clearedDenseIntegerPolynomialEval]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  have hk : (k : ℕ) ≤ d := by omega
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  rw [div_pow]
  field_simp
  have hpow : (q : ℝ) ^ (k : ℕ) * (q : ℝ) ^ (d - (k : ℕ)) = (q : ℝ) ^ d := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  calc
    (q : ℝ) ^ d * (a k : ℝ) * (m : ℝ) ^ (k : ℕ) =
        (a k : ℝ) * (m : ℝ) ^ (k : ℕ) * (q : ℝ) ^ d := by ring
    _ = (a k : ℝ) * (m : ℝ) ^ (k : ℕ) *
        ((q : ℝ) ^ (k : ℕ) * (q : ℝ) ^ (d - (k : ℕ))) := by rw [hpow]
    _ = (a k : ℝ) * (m : ℝ) ^ (k : ℕ) * (q : ℝ) ^ (k : ℕ) *
        (q : ℝ) ^ (d - (k : ℕ)) := by ring

/-- Exact numerator identity behind the normalized polynomial lattice.  If
`p(t) = H⁻¹ ∑ aₖtᵏ`, then the left side is `H q^d (n - s p(m/q))` and the
right side is an integer. -/
theorem normalizedPolynomialResidual_clearing
    {d : ℕ} (a : Fin (d + 1) → ℤ) (H s n m q : ℤ) (hH : H ≠ 0) (hq : q ≠ 0) :
    (H : ℝ) * (q : ℝ) ^ d *
        ((n : ℝ) - (s : ℝ) *
          ((1 / (H : ℝ)) * denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ)))) =
      (H * q ^ d * n - s * clearedDenseIntegerPolynomialEval a m q : ℤ) := by
  have hHreal : (H : ℝ) ≠ 0 := by exact_mod_cast hH
  have hclear := pow_mul_denseIntegerPolynomialEval_div a m q hq
  rw [Int.cast_sub, Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_pow]
  calc
    (H : ℝ) * (q : ℝ) ^ d *
        ((n : ℝ) - (s : ℝ) *
          (1 / (H : ℝ) * denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ)))) =
      (H : ℝ) * (q : ℝ) ^ d * (n : ℝ) -
        (s : ℝ) * ((q : ℝ) ^ d *
          denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ))) := by
      field_simp
    _ = (H : ℝ) * (q : ℝ) ^ d * (n : ℝ) -
        (s : ℝ) * (clearedDenseIntegerPolynomialEval a m q : ℤ) := by rw [hclear]

/-- A nonzero real integer has absolute value at least one. -/
theorem one_le_abs_of_mem_intCast_of_ne_zero {x : ℝ}
    (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (hne : x ≠ 0) : 1 ≤ |x| := by
  obtain ⟨z, rfl⟩ := hx
  exact_mod_cast Int.one_le_abs (by exact_mod_cast hne)

/-- Resolution lemma: an integer-valued scaled residual of absolute value `< 1` vanishes. -/
theorem eq_zero_of_mem_intCast_of_abs_lt_one {x : ℝ}
    (hx : x ∈ Set.range ((↑) : ℤ → ℝ)) (hsmall : |x| < 1) : x = 0 := by
  by_contra hne
  exact (not_lt_of_ge (one_le_abs_of_mem_intCast_of_ne_zero hx hne)) hsmall

/-- The exact lattice-resolution consequence of the clearing identity. -/
theorem normalizedPolynomialResidual_eq_zero_of_abs_scaled_lt_one
    {d : ℕ} (a : Fin (d + 1) → ℤ) (H s n m q : ℤ) (hH : H ≠ 0) (hq : q ≠ 0)
    (hsmall :
      |(H : ℝ) * (q : ℝ) ^ d *
        ((n : ℝ) - (s : ℝ) *
          ((1 / (H : ℝ)) * denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ))))| < 1) :
    (n : ℝ) = (s : ℝ) *
      ((1 / (H : ℝ)) * denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ))) := by
  let R : ℝ := (n : ℝ) - (s : ℝ) *
    ((1 / (H : ℝ)) * denseIntegerPolynomialEval a ((m : ℝ) / (q : ℝ)))
  have hint : (H : ℝ) * (q : ℝ) ^ d * R ∈ Set.range ((↑) : ℤ → ℝ) := by
    refine ⟨H * q ^ d * n - s * clearedDenseIntegerPolynomialEval a m q, ?_⟩
    exact (normalizedPolynomialResidual_clearing a H s n m q hH hq).symm
  have hz : (H : ℝ) * (q : ℝ) ^ d * R = 0 :=
    eq_zero_of_mem_intCast_of_abs_lt_one hint hsmall
  have hHR : (H : ℝ) ≠ 0 := by exact_mod_cast hH
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hscale : (H : ℝ) * (q : ℝ) ^ d ≠ 0 := mul_ne_zero hHR (pow_ne_zero _ hqR)
  have : R = 0 := (mul_eq_zero.mp hz).resolve_left hscale
  exact sub_eq_zero.mp this

/-! ## The all-degree normalization tax -/

/-- A rational lower factor for each factor in the falling coefficient when
`3/2 < alpha < 8/5`. -/
def fallingCoefficientLowerFactor (k : ℕ) : ℝ :=
  if k = 0 then 3 / 2 else if k = 1 then 1 / 2 else (k : ℝ) - 8 / 5

def fallingCoefficientLower (d : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (d + 1), fallingCoefficientLowerFactor k

theorem fallingCoefficientLowerFactor_nonneg (k : ℕ) :
    0 ≤ fallingCoefficientLowerFactor k := by
  by_cases hk0 : k = 0
  · simp [fallingCoefficientLowerFactor, hk0]
    norm_num
  by_cases hk1 : k = 1
  · simp [fallingCoefficientLowerFactor, hk0, hk1]
  have hk2 : 2 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ (k : ℕ) := by exact_mod_cast hk2
  simp only [fallingCoefficientLowerFactor, hk0, hk1, if_false]
  norm_num
  linarith

theorem fallingCoefficientLowerFactor_pos (k : ℕ) :
    0 < fallingCoefficientLowerFactor k := by
  by_cases hk0 : k = 0
  · subst k
    norm_num [fallingCoefficientLowerFactor]
  by_cases hk1 : k = 1
  · subst k
    norm_num [fallingCoefficientLowerFactor]
  have hk2 : 2 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ (k : ℕ) := by exact_mod_cast hk2
  simp only [fallingCoefficientLowerFactor, hk0, hk1, if_false]
  norm_num
  linarith

theorem fallingCoefficientLower_pos (d : ℕ) : 0 < fallingCoefficientLower d := by
  rw [fallingCoefficientLower]
  exact Finset.prod_pos fun k _hk ↦ fallingCoefficientLowerFactor_pos k

theorem fallingCoefficientLower_le_abs_fallingRpowCoeff
    (alpha : ℝ) (d : ℕ) (hlower : (3 / 2 : ℝ) ≤ alpha)
    (hupper : alpha ≤ (8 / 5 : ℝ)) :
    fallingCoefficientLower d ≤ |fallingRpowCoeff alpha (d + 1)| := by
  rw [fallingCoefficientLower, fallingRpowCoeff, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro k _hk
    exact fallingCoefficientLowerFactor_nonneg k
  intro k hk
  have hklt : k < d + 1 := Finset.mem_range.mp hk
  by_cases hk0 : k = 0
  · subst k
    simp only [fallingCoefficientLowerFactor, if_pos, Nat.cast_zero, sub_zero,
      abs_of_nonneg (by linarith : 0 ≤ alpha)]
    exact hlower
  by_cases hk1 : k = 1
  · subst k
    simp only [fallingCoefficientLowerFactor, one_ne_zero, if_false, if_pos, Nat.cast_one,
      abs_of_nonneg (by linarith : 0 ≤ alpha - 1)]
    linarith
  have hk2 : 2 ≤ k := by omega
  have hkR : (2 : ℝ) ≤ (k : ℕ) := by exact_mod_cast hk2
  rw [abs_of_nonpos (by linarith : alpha - (k : ℕ) ≤ 0)]
  simp only [fallingCoefficientLowerFactor, hk0, hk1, if_false]
  linarith

/-- Report 8's simplified value `L_d = 3^4 2^(4d) c_d`. -/
def normalizationTax (alpha : ℝ) (d : ℕ) : ℝ :=
  81 * (2 : ℝ) ^ (alpha - 2) *
    ((4 : ℝ) ^ d * |fallingRpowCoeff alpha (d + 1)|) /
      (d + 1 : ℝ) ^ (d + 1)

def rationalNormalizationTaxLower (d : ℕ) : ℝ :=
  81 * (1 / 2 : ℝ) *
    ((4 : ℝ) ^ d * fallingCoefficientLower d) /
      (d + 1 : ℝ) ^ (d + 1)

theorem half_lt_two_rpow_sub_two (alpha : ℝ) (halpha : 1 < alpha) :
    (1 / 2 : ℝ) < (2 : ℝ) ^ (alpha - 2) := by
  have h := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (by linarith : (-1 : ℝ) < alpha - 2)
  norm_num at h ⊢
  exact h

theorem rationalNormalizationTaxLower_lt
    (alpha : ℝ) (d : ℕ) (halpha : 1 < alpha)
    (hlower : (3 / 2 : ℝ) ≤ alpha) (hupper : alpha ≤ (8 / 5 : ℝ)) :
    rationalNormalizationTaxLower d < normalizationTax alpha d := by
  have hrpow := half_lt_two_rpow_sub_two alpha halpha
  have hfall := fallingCoefficientLower_le_abs_fallingRpowCoeff alpha d hlower hupper
  have hfallpos := fallingCoefficientLower_pos d
  have hfourpos : 0 < (4 : ℝ) ^ d := by positivity
  have hdenpos : 0 < (d + 1 : ℝ) ^ (d + 1) := by positivity
  rw [rationalNormalizationTaxLower, normalizationTax, div_lt_div_iff_of_pos_right hdenpos]
  have hinnerpos : 0 < (4 : ℝ) ^ d * fallingCoefficientLower d :=
    mul_pos hfourpos hfallpos
  calc
    81 * (1 / 2 : ℝ) * ((4 : ℝ) ^ d * fallingCoefficientLower d) <
        81 * (2 : ℝ) ^ (alpha - 2) *
          ((4 : ℝ) ^ d * fallingCoefficientLower d) := by
      gcongr
    _ ≤ 81 * (2 : ℝ) ^ (alpha - 2) *
          ((4 : ℝ) ^ d * |fallingRpowCoeff alpha (d + 1)|) := by
      gcongr

theorem one_lt_normalizationTax_of_le_nine
    (alpha : ℝ) (d : ℕ) (hd : 1 ≤ d) (hd9 : d ≤ 9)
    (halpha : 1 < alpha) (hlower : (3 / 2 : ℝ) ≤ alpha)
    (hupper : alpha ≤ (8 / 5 : ℝ)) :
    1 < normalizationTax alpha d := by
  have hrat : 1 < rationalNormalizationTaxLower d := by
    interval_cases d <;>
      norm_num [rationalNormalizationTaxLower, fallingCoefficientLower,
        fallingCoefficientLowerFactor, Finset.prod_range_succ]
  exact hrat.trans (rationalNormalizationTaxLower_lt alpha d halpha hlower hupper)

theorem one_third_lt_nat_div_succ_pow (n : ℕ) (hn : 1 ≤ n) :
    (1 / 3 : ℝ) < ((n : ℝ) / (n + 1 : ℝ)) ^ n := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  let A : ℝ := ((n : ℝ) / (n + 1 : ℝ)) ^ n
  let B : ℝ := (1 + (n : ℝ)⁻¹) ^ n
  have hB : B < 3 := (Real.one_add_inv_pow_le_exp (n := n)).trans_lt Real.exp_one_lt_three
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hprod : A * B = 1 := by
    dsimp [A, B]
    rw [← mul_pow]
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hns0 : (n + 1 : ℝ) ≠ 0 := by positivity
    congr 1
    field_simp
    ring
  by_contra hnot
  have hA : A ≤ (1 / 3 : ℝ) := le_of_not_gt hnot
  have : A * B < 1 := calc
    A * B ≤ (1 / 3 : ℝ) * B := mul_le_mul_of_nonneg_right hA hBpos.le
    _ < (1 / 3 : ℝ) * 3 := mul_lt_mul_of_pos_left hB (by norm_num)
    _ = 1 := by norm_num
  linarith [hprod]

def normalizationTaxRatio (alpha : ℝ) (d : ℕ) : ℝ :=
  4 * ((d + 1 : ℝ) - alpha) * (d + 1 : ℝ) ^ (d + 1) /
    (d + 2 : ℝ) ^ (d + 2)

theorem normalizationTaxRatio_eq (alpha : ℝ) (d : ℕ) :
    normalizationTaxRatio alpha d =
      (4 * ((d + 1 : ℝ) - alpha) / (d + 2 : ℝ)) *
        (((d + 1 : ℝ) / (d + 2 : ℝ)) ^ (d + 1)) := by
  rw [normalizationTaxRatio, div_pow]
  have hden : (d + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem one_lt_normalizationTaxRatio
    (alpha : ℝ) (d : ℕ) (hd : 9 ≤ d) (hupper : alpha ≤ (8 / 5 : ℝ)) :
    1 < normalizationTaxRatio alpha d := by
  rw [normalizationTaxRatio_eq]
  have hden : (0 : ℝ) < (d + 2 : ℝ) := by positivity
  have hdR : (9 : ℝ) ≤ (d : ℕ) := by exact_mod_cast hd
  have hfirst :
      (3 : ℝ) < 4 * ((d + 1 : ℝ) - alpha) / (d + 2 : ℝ) := by
    rw [lt_div_iff₀ hden]
    push_cast
    linarith
  have hsecond :
      (1 / 3 : ℝ) < ((d + 1 : ℝ) / (d + 2 : ℝ)) ^ (d + 1) := by
    convert one_third_lt_nat_div_succ_pow (d + 1) (by omega) using 1 <;>
      push_cast <;> ring
  calc
    (1 : ℝ) = 3 * (1 / 3 : ℝ) := by norm_num
    _ < (4 * ((d + 1 : ℝ) - alpha) / (d + 2 : ℝ)) * (1 / 3 : ℝ) :=
      mul_lt_mul_of_pos_right hfirst (by norm_num)
    _ < (4 * ((d + 1 : ℝ) - alpha) / (d + 2 : ℝ)) *
        (((d + 1 : ℝ) / (d + 2 : ℝ)) ^ (d + 1)) :=
      mul_lt_mul_of_pos_left hsecond (by linarith)

theorem normalizationTax_succ
    (alpha : ℝ) (d : ℕ) (hd : 1 ≤ d) (hupper : alpha < 2) :
    normalizationTax alpha (d + 1) =
      normalizationTax alpha d * normalizationTaxRatio alpha d := by
  have hneg : alpha - (d + 1 : ℝ) < 0 := by
    have hdR : (2 : ℝ) ≤ (d + 1 : ℕ) := by exact_mod_cast (show 2 ≤ d + 1 by omega)
    push_cast at hdR
    linarith
  have habs : |alpha - (d + 1 : ℝ)| = (d + 1 : ℝ) - alpha := by
    rw [abs_of_neg hneg]
    ring
  have hden1 : (d + 1 : ℝ) ≠ 0 := by positivity
  have hden2 : (d + 2 : ℝ) ≠ 0 := by positivity
  rw [normalizationTax, normalizationTax, normalizationTaxRatio]
  rw [show d + 1 + 1 = (d + 1) + 1 by omega, fallingRpowCoeff_succ,
    abs_mul, pow_succ (4 : ℝ)]
  push_cast
  rw [habs]
  field_simp
  ring

theorem normalizationTax_lt_succ
    (alpha : ℝ) (d : ℕ) (hd : 9 ≤ d)
    (halpha : 1 < alpha) (hlower : (3 / 2 : ℝ) ≤ alpha)
    (hupper : alpha ≤ (8 / 5 : ℝ)) :
    normalizationTax alpha d < normalizationTax alpha (d + 1) := by
  rw [normalizationTax_succ alpha d (by omega) (by linarith)]
  have habspos : 0 < |fallingRpowCoeff alpha (d + 1)| :=
    (fallingCoefficientLower_pos d).trans_le
      (fallingCoefficientLower_le_abs_fallingRpowCoeff alpha d hlower hupper)
  have htaxpos : 0 < normalizationTax alpha d := by
    rw [normalizationTax]
    exact div_pos (mul_pos (mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) _))
      (mul_pos (by positivity) habspos)) (by positivity)
  nlinarith [one_lt_normalizationTaxRatio alpha d hd hupper]

theorem one_lt_normalizationTax
    (alpha : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (halpha : 1 < alpha) (hlower : (3 / 2 : ℝ) ≤ alpha)
    (hupper : alpha ≤ (8 / 5 : ℝ)) :
    1 < normalizationTax alpha d := by
  by_cases hd9 : d ≤ 9
  · exact one_lt_normalizationTax_of_le_nine alpha d hd hd9 halpha hlower hupper
  have h9d : 9 ≤ d := by omega
  refine Nat.le_induction
    (one_lt_normalizationTax_of_le_nine alpha 9 (by omega) (by omega)
      halpha hlower hupper) ?_ d h9d
  intro n hn ih
  exact ih.trans (normalizationTax_lt_succ alpha n hn halpha hlower hupper)

theorem three_halves_lt_logThreeDivLogTwo :
    (3 / 2 : ℝ) < logThreeDivLogTwo := by
  have hpow : (2 : ℝ) ^ (3 / 2 : ℝ) < 3 := by
    apply (pow_lt_pow_iff_left₀ (Real.rpow_nonneg (by norm_num) _)
      (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (2 : ℕ) ≠ 0)).mp
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [Real.rpow_natCast]
  rw [logThreeDivLogTwo]
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ (3 / 2 : ℝ)) hpow
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)] at hlog
  exact hlog

theorem one_lt_normalizationTax_logThreeDivLogTwo (d : ℕ) (hd : 1 ≤ d) :
    1 < normalizationTax logThreeDivLogTwo d :=
  one_lt_normalizationTax logThreeDivLogTwo d hd one_lt_logThreeDivLogTwo
    three_halves_lt_logThreeDivLogTwo.le logThreeDivLogTwo_lt_eight_fifths.le

/-- The simplified tax is exactly the `T=4` lattice scale times the finite-difference floor. -/
theorem normalizationTax_eq_four_scale_floor (alpha : ℝ) (d : ℕ) :
    normalizationTax alpha d =
      81 * (2 : ℝ) ^ (4 * d) * polynomialApproximationFloor alpha d := by
  rw [normalizationTax, polynomialApproximationFloor]
  push_cast
  rw [one_div, inv_pow, div_eq_mul_inv]
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  have hdpos : (0 : ℝ) < (d + 1 : ℝ) := by positivity
  have hcombine :
      (2 : ℝ) ^ (4 * d) * (2 : ℝ) ^ (alpha - ((d : ℝ) + 1)) =
        (2 : ℝ) ^ (alpha - 2) * (4 : ℝ) ^ d * (2 : ℝ) ^ (d + 1) := by
    rw [← Real.rpow_natCast]
    rw [show (4 : ℝ) ^ d = (2 : ℝ) ^ (2 * d) by
      rw [pow_mul]; norm_num]
    rw [← Real.rpow_natCast, ← Real.rpow_natCast]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    push_cast
    ring
  field_simp
  calc
    (2 : ℝ) ^ (alpha - 2) * (4 : ℝ) ^ d *
        |fallingRpowCoeff alpha (d + 1)| * (2 : ℝ) ^ (d + 1) =
      |fallingRpowCoeff alpha (d + 1)| *
        ((2 : ℝ) ^ (alpha - 2) * (4 : ℝ) ^ d * (2 : ℝ) ^ (d + 1)) := by ring
    _ = |fallingRpowCoeff alpha (d + 1)| *
        ((2 : ℝ) ^ (4 * d) * (2 : ℝ) ^ (alpha - ((d : ℝ) + 1))) := by rw [hcombine]
    _ = |fallingRpowCoeff alpha (d + 1)| * (2 : ℝ) ^ (4 * d) *
        (2 : ℝ) ^ (alpha - ((d : ℝ) + 1)) := by ring

theorem one_lt_four_scale_polynomialApproximationFloor (d : ℕ) (hd : 1 ≤ d) :
    1 < 81 * (2 : ℝ) ^ (4 * d) *
      polynomialApproximationFloor logThreeDivLogTwo d := by
  rw [← normalizationTax_eq_four_scale_floor]
  exact one_lt_normalizationTax_logThreeDivLogTwo d hd

/-- Half-open integer blocks normalize to `[1,2)`.  The approximation estimate may use the
closed ambient interval `[1,2]`, but candidate enumeration never includes the right endpoint. -/
theorem normalized_mem_Ico_one_two_of_mem_dyadicBlock
    {T m : ℕ} (hm : m ∈ Set.Ico (2 ^ T) (2 ^ (T + 1))) :
    (m : ℝ) / (2 ^ T : ℕ) ∈ Set.Ico (1 : ℝ) 2 := by
  have hden : (0 : ℝ) < (2 ^ T : ℕ) := by positivity
  constructor
  · rw [le_div_iff₀ hden]
    norm_num
    exact_mod_cast hm.1
  · rw [div_lt_iff₀ hden]
    have hm' := hm.2
    rw [pow_succ] at hm'
    have hm'' : m < 2 * 2 ^ T := by simpa [Nat.mul_comm] using hm'
    exact_mod_cast hm''

/-- Any degree-`d` real polynomial has uniform error at least the explicit forward-difference
floor.  The hypothesis is deliberately pointwise on `[1,2]`; no compact-supremum API or
attainment theorem is required. -/
theorem polynomialApproximationFloor_le_of_pointwise
    (alpha : ℝ) (d : ℕ) (hd : 1 ≤ d) (halpha : alpha < 2)
    (P : ℝ[X]) (hP : P.natDegree ≤ d) (E : ℝ)
    (herr : ∀ t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 → |t ^ alpha - P.eval t| ≤ E) :
    polynomialApproximationFloor alpha d ≤ E := by
  let r : ℕ := d + 1
  let h : ℝ := 1 / (r : ℝ)
  let e : ℝ → ℝ := fun t ↦ t ^ alpha - P.eval t
  have hr : 1 ≤ r := by simp [r]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hh : 0 < h := by simp [h, hrpos]
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 2 ≤ r by simp [r, hd])
  have hexp : alpha - (r : ℝ) < 0 := by linarith
  have hend : (1 : ℝ) + (r : ℝ) * h = 2 := by
    dsimp [h]
    field_simp
    norm_num
  obtain ⟨xi, hxi1, hxi2raw, hmean⟩ :=
    exists_iterated_fwdDiff_rpow_point alpha 1 h r hr (by norm_num) hh
  have hxi2 : xi < 2 := by rw [hend] at hxi2raw; exact hxi2raw
  have hxipos : 0 < xi := (by norm_num : (0 : ℝ) < 1).trans hxi1
  have hpow : (2 : ℝ) ^ (alpha - (r : ℝ)) ≤ xi ^ (alpha - (r : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hxipos hxi2.le hexp.le
  have hpolyzero : Δ_[h]^[r] P.eval 1 = 0 :=
    Polynomial.fwdDiff_iter_eq_zero_of_natDegree_lt P r
      (lt_of_le_of_lt hP (by simp [r])) 1 h
  have hsplit :
      Δ_[h]^[r] e 1 =
        Δ_[h]^[r] (fun t : ℝ ↦ t ^ alpha) 1 - Δ_[h]^[r] P.eval 1 := by
    have hefun : e = (fun t : ℝ ↦ t ^ alpha) + (-1 : ℝ) • P.eval := by
      funext t
      simp only [e, Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg]
    rw [hefun]
    rw [fwdDiff_iter_add, fwdDiff_iter_const_smul]
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_one_mul, sub_eq_add_neg]
  have heq : Δ_[h]^[r] e 1 = Δ_[h]^[r] (fun t : ℝ ↦ t ^ alpha) 1 := by
    rw [hsplit, hpolyzero, sub_zero]
  have hsamples : ∀ k : ℕ, k ≤ r → |e (1 + (k : ℝ) * h)| ≤ E := by
    intro k hk
    apply herr
    constructor
    · have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      exact le_add_of_nonneg_right (mul_nonneg hk0 hh.le)
    · have hkR : (k : ℝ) ≤ (r : ℝ) := by exact_mod_cast hk
      have : (k : ℝ) * h ≤ (r : ℝ) * h :=
        mul_le_mul_of_nonneg_right hkR hh.le
      linarith [hend]
  have hupper : |Δ_[h]^[r] e 1| ≤ (2 : ℝ) ^ r * E :=
    abs_iterated_fwdDiff_le_two_pow_mul e r 1 h E hsamples
  have hcurvpos : 0 < xi ^ (alpha - (r : ℝ)) := Real.rpow_pos_of_pos hxipos _
  have hhpow : 0 ≤ h ^ r := pow_nonneg hh.le _
  have habsmean :
      |Δ_[h]^[r] (fun t : ℝ ↦ t ^ alpha) 1| =
        |fallingRpowCoeff alpha r| * h ^ r * xi ^ (alpha - (r : ℝ)) := by
    rw [hmean, abs_mul, abs_mul, abs_of_nonneg hhpow, abs_of_pos hcurvpos]
  have hlower :
      |fallingRpowCoeff alpha r| * h ^ r * (2 : ℝ) ^ (alpha - (r : ℝ)) ≤
        |Δ_[h]^[r] e 1| := by
    rw [heq, habsmean]
    exact mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) hhpow)
  have htwo : 0 < (2 : ℝ) ^ r := by positivity
  have hfin :
      |fallingRpowCoeff alpha r| * h ^ r *
          (2 : ℝ) ^ (alpha - (r : ℝ)) / (2 : ℝ) ^ r ≤ E := by
    rw [div_le_iff₀ htwo]
    exact hlower.trans (by simpa [mul_comm] using hupper)
  simpa only [polynomialApproximationFloor, r, h, Nat.cast_add, Nat.cast_one] using hfin

/-- Report 8's normalization-tax obstruction, including degree zero.  The error hypothesis is
pointwise on `[1,2]`; `H ≥1` and `T ≥4` make the arithmetic resolution scale no smaller
than its `H=1,T=4` value. -/
theorem normalizationTax_obstruction
    (T d H : ℕ) (hT : 4 ≤ T) (hH : 1 ≤ H)
    (P : ℝ[X]) (hP : P.natDegree ≤ d) (E : ℝ)
    (herr : ∀ t : ℝ, t ∈ Set.Icc (1 : ℝ) 2 →
      |t ^ logThreeDivLogTwo - P.eval t| ≤ E) :
    1 ≤ (H : ℝ) * (3 : ℝ) ^ T * (2 : ℝ) ^ (T * d) * E := by
  by_cases hd0 : d = 0
  · subst d
    have hconst := Polynomial.eq_C_of_natDegree_le_zero hP
    have h1 := herr 1 (by constructor <;> norm_num)
    have h2 := herr 2 (by constructor <;> norm_num)
    rw [hconst] at h1 h2
    simp only [Polynomial.eval_C] at h1 h2
    norm_num at h1
    rw [two_rpow_logThreeDivLogTwo] at h2
    have hE : 1 ≤ E := by
      have htri : (2 : ℝ) ≤ |3 - P.coeff 0| + |1 - P.coeff 0| := by
        calc
          (2 : ℝ) = |(3 - P.coeff 0) - (1 - P.coeff 0)| := by
            rw [show (3 - P.coeff 0) - (1 - P.coeff 0) = (2 : ℝ) by ring]
            norm_num
          _ ≤ |3 - P.coeff 0| + |1 - P.coeff 0| := abs_sub _ _
      linarith
    have hscale : (1 : ℝ) ≤ (H : ℝ) * (3 : ℝ) ^ T := by
      have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast hH
      have hthree : (1 : ℝ) ≤ (3 : ℝ) ^ T := one_le_pow₀ (by norm_num)
      nlinarith
    norm_num
    simpa using mul_le_mul hscale hE (by norm_num) (by positivity)
  have hd : 1 ≤ d := by omega
  have hfloor := polynomialApproximationFloor_le_of_pointwise
    logThreeDivLogTwo d hd (by linarith [logThreeDivLogTwo_lt_eight_fifths]) P hP E herr
  have hbase := one_lt_four_scale_polynomialApproximationFloor d hd
  have hscaleNat : 81 * 2 ^ (4 * d) ≤ H * 3 ^ T * 2 ^ (T * d) := by
    have h3 : 3 ^ 4 ≤ 3 ^ T := Nat.pow_le_pow_right (by omega) hT
    have hTd : 4 * d ≤ T * d := Nat.mul_le_mul_right d hT
    have h2 : 2 ^ (4 * d) ≤ 2 ^ (T * d) := Nat.pow_le_pow_right (by omega) hTd
    calc
      81 * 2 ^ (4 * d) = 3 ^ 4 * 2 ^ (4 * d) := by norm_num
      _ ≤ 3 ^ T * 2 ^ (T * d) := Nat.mul_le_mul h3 h2
      _ = 1 * (3 ^ T * 2 ^ (T * d)) := by omega
      _ ≤ H * (3 ^ T * 2 ^ (T * d)) := Nat.mul_le_mul_right _ hH
      _ = H * 3 ^ T * 2 ^ (T * d) := by ring
  have hscale :
      (81 : ℝ) * (2 : ℝ) ^ (4 * d) ≤
        (H : ℝ) * (3 : ℝ) ^ T * (2 : ℝ) ^ (T * d) := by
    exact_mod_cast hscaleNat
  have hfloorpos : 0 < polynomialApproximationFloor logThreeDivLogTwo d := by
    by_contra hnot
    have hnonpos : polynomialApproximationFloor logThreeDivLogTwo d ≤ 0 := le_of_not_gt hnot
    have : 81 * (2 : ℝ) ^ (4 * d) *
        polynomialApproximationFloor logThreeDivLogTwo d ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hnonpos
    linarith
  calc
    (1 : ℝ) ≤ 81 * (2 : ℝ) ^ (4 * d) *
        polynomialApproximationFloor logThreeDivLogTwo d := hbase.le
    _ ≤ ((H : ℝ) * (3 : ℝ) ^ T * (2 : ℝ) ^ (T * d)) *
        polynomialApproximationFloor logThreeDivLogTwo d :=
      mul_le_mul_of_nonneg_right hscale hfloorpos.le
    _ ≤ (H : ℝ) * (3 : ℝ) ^ T * (2 : ℝ) ^ (T * d) * E :=
      mul_le_mul_of_nonneg_left hfloor (by positivity)

end

end LeanProofs.TwoBaseIntegerExponent

import ExponentialIdentities.TwoBaseIntegerExponent.CrossResidualScaling

/-!
# Exact structural-prime scaling of structural-residual analysis's boundary node divisors

The report uses the two integer node products `Π_{n,n+1}` and
`Π_{n+1,n}`.  This module gives their exact normalizations at `3^n` and
`2^n`, respectively, including the unit constant-coefficient facts needed for
prime-power content cancellation.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Polynomial

noncomputable section

/-- The common content exponent of either cross-scaled boundary divisor. -/
def report14BoundaryDivisorExponent (n : ℕ) : ℕ :=
  n * (n * (n + 1) / 2)

theorem report14BoundaryDivisorExponent_eq (n : ℕ) :
    report14BoundaryDivisorExponent n = n * n * (n + 1) / 2 := by
  unfold report14BoundaryDivisorExponent
  rw [← Nat.mul_div_assoc n
    (even_iff_two_dvd.mp (Nat.even_mul_succ_self n))]
  simp only [mul_assoc]

/-- `Π_{n,n+1}`: the divisor of the dyadic boundary defect. -/
def report14DyadicDefectDivisor (n : ℕ) : ℤ[X] :=
  ∏ i ∈ range n, ∏ j ∈ range (n + 1),
    (X - C (((2 : ℤ) ^ i) * ((3 : ℤ) ^ j)))

/-- `Π_{n+1,n}`: the divisor of the triadic boundary defect. -/
def report14TriadicDefectDivisor (n : ℕ) : ℤ[X] :=
  ∏ i ∈ range (n + 1), ∏ j ∈ range n,
    (X - C (((2 : ℤ) ^ i) * ((3 : ℤ) ^ j)))

/-- The triadic defect divisor after extracting its full dyadic content at
the dilation `X ↦ 2^n X`. -/
def report14TriadicDivisorDyadicNormalization (n : ℕ) : ℤ[X] :=
  ∏ i ∈ range (n + 1), ∏ j ∈ range n,
    (C ((2 : ℤ) ^ (n - i)) * X - C ((3 : ℤ) ^ j))

/-- The dyadic defect divisor after extracting its full triadic content at
the dilation `X ↦ 3^n X`. -/
def report14DyadicDivisorTriadicNormalization (n : ℕ) : ℤ[X] :=
  ∏ i ∈ range n, ∏ j ∈ range (n + 1),
    (C ((3 : ℤ) ^ (n - j)) * X - C ((2 : ℤ) ^ i))

private theorem dyadic_node_factor (n i j : ℕ) (hi : i ≤ n) :
    ((X - C (((2 : ℤ) ^ i) * ((3 : ℤ) ^ j))).comp
      (C ((2 : ℤ) ^ n) * X)) =
      C ((2 : ℤ) ^ i) *
        (C ((2 : ℤ) ^ (n - i)) * X - C ((3 : ℤ) ^ j)) := by
  simp only [sub_comp, X_comp, C_comp]
  have hpow : (2 : ℤ) ^ n = 2 ^ i * 2 ^ (n - i) := by
    rw [← pow_add, Nat.add_sub_of_le hi]
  rw [hpow]
  simp only [map_mul]
  ring

private theorem triadic_node_factor (n i j : ℕ) (hj : j ≤ n) :
    ((X - C (((2 : ℤ) ^ i) * ((3 : ℤ) ^ j))).comp
      (C ((3 : ℤ) ^ n) * X)) =
      C ((3 : ℤ) ^ j) *
        (C ((3 : ℤ) ^ (n - j)) * X - C ((2 : ℤ) ^ i)) := by
  simp only [sub_comp, X_comp, C_comp]
  have hpow : (3 : ℤ) ^ n = 3 ^ j * 3 ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [hpow]
  simp only [map_mul]
  ring

private theorem dyadic_scalar_product (n : ℕ) :
    (∏ i ∈ range (n + 1), ∏ _j ∈ range n, C ((2 : ℤ) ^ i)) =
      C ((2 : ℤ) ^ report14BoundaryDivisorExponent n) := by
  simp only [Finset.prod_const, Finset.card_range]
  simp only [← map_pow]
  rw [← map_prod]
  congr 1
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.sum_mul, Finset.sum_range_id]
  simp only [report14BoundaryDivisorExponent, Nat.add_sub_cancel, mul_comm]

private theorem triadic_scalar_product (n : ℕ) :
    (∏ _i ∈ range n, ∏ j ∈ range (n + 1), C ((3 : ℤ) ^ j)) =
      C ((3 : ℤ) ^ report14BoundaryDivisorExponent n) := by
  simp only [Finset.prod_const, Finset.card_range]
  rw [← map_prod]
  rw [← map_pow]
  congr 1
  rw [← Finset.prod_pow]
  simp only [← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [← Finset.sum_mul, Finset.sum_range_id]
  simp only [report14BoundaryDivisorExponent, Nat.add_sub_cancel, mul_comm]

/-- Exact `2^b` extraction from `Π_{n+1,n}(2^nX)`. -/
theorem report14TriadicDefectDivisor_comp_two_pow
    (n : ℕ) :
    (report14TriadicDefectDivisor n).comp (C ((2 : ℤ) ^ n) * X) =
      C ((2 : ℤ) ^ report14BoundaryDivisorExponent n) *
        report14TriadicDivisorDyadicNormalization n := by
  unfold report14TriadicDefectDivisor
    report14TriadicDivisorDyadicNormalization
  simp only [Polynomial.prod_comp]
  calc
    (∏ i ∈ range (n + 1), ∏ j ∈ range n,
      (X - C (((2 : ℤ) ^ i) * ((3 : ℤ) ^ j))).comp
        (C ((2 : ℤ) ^ n) * X)) =
        ∏ i ∈ range (n + 1), ∏ j ∈ range n,
          (C ((2 : ℤ) ^ i) *
            (C ((2 : ℤ) ^ (n - i)) * X - C ((3 : ℤ) ^ j))) := by
      apply Finset.prod_congr rfl
      intro i hi
      apply Finset.prod_congr rfl
      intro j _
      exact dyadic_node_factor n i j (by simpa using (mem_range.mp hi))
    _ = (∏ i ∈ range (n + 1), ∏ _j ∈ range n, C ((2 : ℤ) ^ i)) *
          ∏ i ∈ range (n + 1), ∏ j ∈ range n,
            (C ((2 : ℤ) ^ (n - i)) * X - C ((3 : ℤ) ^ j)) := by
      simp only [prod_mul_distrib]
    _ = _ := by rw [dyadic_scalar_product]

/-- Exact `3^b` extraction from `Π_{n,n+1}(3^nX)`. -/
theorem report14DyadicDefectDivisor_comp_three_pow
    (n : ℕ) :
    (report14DyadicDefectDivisor n).comp (C ((3 : ℤ) ^ n) * X) =
      C ((3 : ℤ) ^ report14BoundaryDivisorExponent n) *
        report14DyadicDivisorTriadicNormalization n := by
  unfold report14DyadicDefectDivisor
    report14DyadicDivisorTriadicNormalization
  simp only [Polynomial.prod_comp]
  calc
    (∏ i ∈ range n, ∏ j ∈ range (n + 1),
      (X - C (((2 : ℤ) ^ i) * ((3 : ℤ) ^ j))).comp
        (C ((3 : ℤ) ^ n) * X)) =
        ∏ i ∈ range n, ∏ j ∈ range (n + 1),
          (C ((3 : ℤ) ^ j) *
            (C ((3 : ℤ) ^ (n - j)) * X - C ((2 : ℤ) ^ i))) := by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_congr rfl
      intro j hj
      exact triadic_node_factor n i j (by simpa using (mem_range.mp hj))
    _ = (∏ i ∈ range n, ∏ j ∈ range (n + 1), C ((3 : ℤ) ^ j)) *
          ∏ i ∈ range n, ∏ j ∈ range (n + 1),
            (C ((3 : ℤ) ^ (n - j)) * X - C ((2 : ℤ) ^ i)) := by
      simp only [prod_mul_distrib]
    _ = _ := by rw [triadic_scalar_product]

private theorem constantCoeff_C_int (a : ℤ) :
    Polynomial.constantCoeff (C a) = a := by
  change (C a).coeff 0 = a
  simp

private theorem constantCoeff_X_int :
    Polynomial.constantCoeff (X : ℤ[X]) = 0 := by
  change (X : ℤ[X]).coeff 0 = 0
  simp

/-- The dyadic normalizer has odd constant coefficient. -/
theorem report14TriadicDivisorDyadicNormalization_constantCoeff_odd
    (n : ℕ) :
    Odd (report14TriadicDivisorDyadicNormalization n).constantCoeff := by
  simp only [report14TriadicDivisorDyadicNormalization, map_prod, map_sub,
    map_mul, constantCoeff_C_int, constantCoeff_X_int, mul_zero, zero_sub]
  rw [Finset.prod_const, Finset.card_range]
  have hprod : Odd (∏ j ∈ range n, (-3 ^ j : ℤ)) := by
    exact Finset.prod_induction (fun j : ℕ ↦ (-3 ^ j : ℤ)) Odd
      (fun _ _ ha hb ↦ ha.mul hb) (by norm_num)
      (fun _ _ ↦ (show Odd (3 : ℤ) by norm_num).pow.neg)
  exact hprod.pow

/-- The triadic normalizer's constant coefficient is not divisible by `3`. -/
theorem report14DyadicDivisorTriadicNormalization_constantCoeff_not_three_dvd
    (n : ℕ) :
    ¬ (3 : ℤ) ∣
      (report14DyadicDivisorTriadicNormalization n).constantCoeff := by
  simp only [report14DyadicDivisorTriadicNormalization, map_prod, map_sub,
    map_mul, constantCoeff_C_int, constantCoeff_X_int, mul_zero, zero_sub]
  rw [Finset.prod_comm, Finset.prod_const, Finset.card_range]
  rw [(show Prime (3 : ℤ) by norm_num).dvd_pow_iff_dvd (by omega)]
  exact Finset.prod_induction (fun i : ℕ ↦ (-2 ^ i : ℤ))
    (fun z : ℤ ↦ ¬ (3 : ℤ) ∣ z)
    (fun _ _ ha hb ↦ (show Prime (3 : ℤ) by norm_num).not_dvd_mul ha hb)
    (by norm_num)
    (fun _ _ ↦ by
      rw [dvd_neg]
      exact (show Prime (3 : ℤ) by norm_num).coprime_iff_not_dvd.mp
        ((show IsCoprime (3 : ℤ) 2 by norm_num).pow_right))

end

end LeanProofs.TwoBaseIntegerExponent

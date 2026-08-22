import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Signed-progression determinants and their denominator tax

This file formalizes the finite algebraic core of the signed-progression construction in the
Alaoglu--Erdős continuation report.  The construction reduces, after rational row and column
scalings, to the geometric Vandermonde matrix `(t ^ (i * j))`.  We record:

* its exact Vandermonde factorization;
* the primitive integer product occurring in the report's invariant-quotient formula;
* coprimality of that product with both primitive bases; and
* an exact logarithmic expansion with a nonnegative, explicitly bounded remainder.

The final analytic statements are deliberately finite identities.  They do not assert the
continued-fraction asymptotics from the paper report.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators

noncomputable section

/-! ## The geometric Vandermonde factor -/

/-- The geometric Vandermonde matrix with entry `t ^ (i*j)`. -/
def geometricVandermondeMatrix {R : Type*} [CommRing R] (N : ℕ) (t : R) :
    Matrix (Fin N) (Fin N) R :=
  Matrix.of fun i j ↦ t ^ (i.1 * j.1)

@[simp] theorem geometricVandermondeMatrix_apply {R : Type*} [CommRing R]
    (N : ℕ) (t : R) (i j : Fin N) :
    geometricVandermondeMatrix N t i j = t ^ (i.1 * j.1) := rfl

/-- The geometric matrix is the ordinary Vandermonde matrix on the nodes `t^i`. -/
theorem geometricVandermondeMatrix_eq_vandermonde {R : Type*} [CommRing R]
    (N : ℕ) (t : R) :
    geometricVandermondeMatrix N t = Matrix.vandermonde (fun i : Fin N ↦ t ^ i.1) := by
  ext i j
  rw [geometricVandermondeMatrix_apply, Matrix.vandermonde_apply, pow_mul]

/-- Exact determinant factorization of the geometric Vandermonde matrix. -/
theorem det_geometricVandermondeMatrix {R : Type*} [CommRing R]
    (N : ℕ) (t : R) :
    (geometricVandermondeMatrix N t).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (t ^ j.1 - t ^ i.1) := by
  rw [geometricVandermondeMatrix_eq_vandermonde, Matrix.det_vandermonde]

/-- Each pairwise geometric difference splits into its pure monomial factor and a normalized
power difference. -/
theorem geometric_pow_sub_pow_factor {R : Type*} [CommRing R] (t : R)
    {i j : ℕ} (hij : i ≤ j) :
    t ^ j - t ^ i = t ^ i * (t ^ (j - i) - 1) := by
  nth_rewrite 1 [show j = i + (j - i) by omega]
  rw [pow_add]
  ring

/-- Pairwise factored form of the geometric Vandermonde determinant.  This is the exact finite
form from which the report's grouped product over the differences `d = j-i` follows. -/
theorem det_geometricVandermondeMatrix_factored {R : Type*} [CommRing R]
    (N : ℕ) (t : R) :
    (geometricVandermondeMatrix N t).det =
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        t ^ i.1 * (t ^ (j.1 - i.1) - 1) := by
  rw [det_geometricVandermondeMatrix]
  apply Finset.prod_congr rfl
  intro i _hi
  apply Finset.prod_congr rfl
  intro j hij
  apply geometric_pow_sub_pow_factor
  have hij' : i < j := Finset.mem_Ioi.mp hij
  exact_mod_cast hij'.le

/-! ## The primitive invariant quotient -/

/-- The unsigned difference `|P^d-Q^d|`, expressed purely in `ℕ`. -/
def progressionDifference (P Q d : ℕ) : ℕ :=
  max (P ^ d) (Q ^ d) - min (P ^ d) (Q ^ d)

theorem progressionDifference_comm (P Q d : ℕ) :
    progressionDifference P Q d = progressionDifference Q P d := by
  simp [progressionDifference, max_comm, min_comm]

/-- A primitive power difference is coprime to its left base. -/
theorem progressionDifference_coprime_left {P Q d : ℕ} (hPQ : P.Coprime Q)
    (hd : d ≠ 0) :
    (progressionDifference P Q d).Coprime P := by
  by_cases h : Q ^ d ≤ P ^ d
  · rw [progressionDifference, max_eq_left h, min_eq_right h]
    have hpows : (Q ^ d).Coprime (P ^ d) := (hPQ.pow d d).symm
    have hdiff : (P ^ d - Q ^ d).Coprime (P ^ d) :=
      (Nat.coprime_self_sub_left h).2 hpows
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self P hd) hdiff
  · have h' : P ^ d ≤ Q ^ d := le_of_not_ge h
    rw [progressionDifference, max_eq_right h', min_eq_left h']
    have hpows : (Q ^ d).Coprime (P ^ d) := (hPQ.pow d d).symm
    have hdiff : (Q ^ d - P ^ d).Coprime (P ^ d) :=
      (Nat.coprime_sub_self_left h').2 hpows
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self P hd) hdiff

/-- A primitive power difference is coprime to its right base. -/
theorem progressionDifference_coprime_right {P Q d : ℕ} (hPQ : P.Coprime Q)
    (hd : d ≠ 0) :
    (progressionDifference P Q d).Coprime Q := by
  rw [progressionDifference_comm]
  exact progressionDifference_coprime_left hPQ.symm hd

/-- The integer product on the right-hand side of the report's signed-progression
invariant-quotient formula.  The separate reduction from the original four-parameter matrix and
its tropical divisor is not asserted by this definition. -/
def progressionInvariantQuotient (N P Q : ℕ) : ℕ :=
  ∏ k ∈ Finset.range (N - 1),
    progressionDifference P Q (k + 1) ^ (N - (k + 1))

/-- The invariant quotient has no prime factor in common with the primitive numerator. -/
theorem progressionInvariantQuotient_coprime_left {N P Q : ℕ} (hPQ : P.Coprime Q) :
    (progressionInvariantQuotient N P Q).Coprime P := by
  rw [progressionInvariantQuotient, Nat.coprime_prod_left_iff]
  intro k hk
  exact (progressionDifference_coprime_left hPQ (by omega)).pow_left _

/-- The invariant quotient has no prime factor in common with the primitive denominator. -/
theorem progressionInvariantQuotient_coprime_right {N P Q : ℕ} (hPQ : P.Coprime Q) :
    (progressionInvariantQuotient N P Q).Coprime Q := by
  rw [progressionInvariantQuotient, Nat.coprime_prod_left_iff]
  intro k hk
  exact (progressionDifference_coprime_right hPQ (by omega)).pow_left _

/-- When `P > Q`, the unsigned primitive difference has the exponential form used in the
denominator-tax calculation. -/
theorem cast_progressionDifference_eq {P Q d : ℕ} (hQ : 0 < Q) (hQP : Q < P) :
    ((progressionDifference P Q d : ℕ) : ℝ) =
      (Q : ℝ) ^ d *
        (Real.exp ((d : ℝ) * Real.log ((P : ℝ) / (Q : ℝ))) - 1) := by
  have hpow : Q ^ d ≤ P ^ d := Nat.pow_le_pow_left hQP.le d
  rw [progressionDifference, max_eq_left hpow, min_eq_right hpow]
  rw [Nat.cast_sub hpow, Nat.cast_pow, Nat.cast_pow]
  have hP : (0 : ℝ) < P := by exact_mod_cast hQ.trans hQP
  have hQR : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  rw [Real.exp_nat_mul, Real.exp_log (div_pos hP (by exact_mod_cast hQ)), div_pow]
  field_simp [pow_ne_zero d hQR]

/-! ## Exact logarithmic denominator-tax expansion -/

/-- The normalized exponential remainder `log ((exp t - 1) / t)`, extended by zero at the
origin. -/
def progressionRho (t : ℝ) : ℝ :=
  if t = 0 then 0 else Real.log ((Real.exp t - 1) / t)

@[simp] theorem progressionRho_zero : progressionRho 0 = 0 := by
  simp [progressionRho]

/-- The elementary remainder lies between zero and `t` on the positive half-line. -/
theorem progressionRho_nonneg_le {t : ℝ} (ht : 0 < t) :
    0 ≤ progressionRho t ∧ progressionRho t ≤ t := by
  rw [progressionRho, if_neg ht.ne']
  have hexpLower : t + 1 ≤ Real.exp t := Real.add_one_le_exp t
  have hratioOne : 1 ≤ (Real.exp t - 1) / t := by
    rw [le_div_iff₀ ht]
    linarith
  have hneg := Real.add_one_le_exp (-t)
  have hexpInv : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have hdiffUpper : Real.exp t - 1 ≤ t * Real.exp t := by
    have hmul := mul_le_mul_of_nonneg_right hneg (Real.exp_pos t).le
    rw [add_mul, one_mul, hexpInv] at hmul
    linarith
  have hratioUpper : (Real.exp t - 1) / t ≤ Real.exp t := by
    exact (div_le_iff₀ ht).2 (by simpa [mul_comm] using hdiffUpper)
  constructor
  · exact Real.log_nonneg hratioOne
  · exact (Real.log_le_iff_le_exp (lt_of_lt_of_le zero_lt_one hratioOne)).2 hratioUpper

/-- Weight of the `d`th primitive power difference in an `N×N` progression determinant. -/
def progressionWeight (N d : ℕ) : ℕ := N - d

/-- The exact logarithmic remainder in the signed-progression product. -/
def progressionLogRemainder (N : ℕ) (eta : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N - 1),
    (progressionWeight N (k + 1) : ℝ) * progressionRho (((k + 1 : ℕ) : ℝ) * eta)

/-- Sum of the exponents of `eta` in the progression product. -/
def progressionEtaWeight (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (N - 1), progressionWeight N (k + 1)

/-- Sum of the exponents of the denominator scale `B` in the progression product. -/
def progressionBaseWeight (N : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (N - 1), (k + 1) * progressionWeight N (k + 1)

/-- The total exponent of `eta` is the number of unordered pairs of nodes. -/
theorem progressionEtaWeight_eq_choose (N : ℕ) :
    progressionEtaWeight N = N.choose 2 := by
  induction N with
  | zero => simp [progressionEtaWeight]
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      simp [progressionEtaWeight]
    rw [progressionEtaWeight]
    have hs : N + 1 - 1 = N := by omega
    rw [hs]
    have hNs : N = (N - 1) + 1 := by omega
    nth_rewrite 1 [hNs]
    rw [Finset.sum_range_succ]
    have hprefix :
        (∑ k ∈ Finset.range (N - 1), progressionWeight (N + 1) (k + 1)) =
          progressionEtaWeight N + (N - 1) := by
      calc
        _ = ∑ k ∈ Finset.range (N - 1),
              (progressionWeight N (k + 1) + 1) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_range] at hk
            simp only [progressionWeight]
            omega
        _ = (∑ k ∈ Finset.range (N - 1), progressionWeight N (k + 1)) +
              ∑ _k ∈ Finset.range (N - 1), 1 := Finset.sum_add_distrib
        _ = progressionEtaWeight N + (N - 1) := by simp [progressionEtaWeight]
    rw [hprefix]
    simp only [progressionWeight]
    rw [show N + 1 - (N - 1 + 1) = 1 by omega, ih]
    rw [Nat.choose_succ_succ]
    simp
    omega

private theorem sum_progression_steps_eq_choose (N : ℕ) :
    (∑ k ∈ Finset.range (N - 1), (k + 1)) = N.choose 2 := by
  by_cases h : 2 ≤ N
  · have hs := Nat.sum_range_add_choose (N - 2) 1
    simp only [Nat.choose_one_right] at hs
    have h1 : N - 2 + 1 = N - 1 := by omega
    rw [h1] at hs
    have h2 : N - 1 + 1 = N := by omega
    simpa [h2] using hs
  · have hsmall : N = 0 ∨ N = 1 := by omega
    rcases hsmall with rfl | rfl <;> decide

/-- The total exponent of the primitive denominator scale is `choose (N+1) 3`. -/
theorem progressionBaseWeight_eq_choose (N : ℕ) :
    progressionBaseWeight N = (N + 1).choose 3 := by
  induction N with
  | zero => norm_num [progressionBaseWeight, Nat.choose]
  | succ N ih =>
    by_cases hN : N = 0
    · subst N
      norm_num [progressionBaseWeight, Nat.choose]
    rw [progressionBaseWeight]
    have hs : N + 1 - 1 = N := by omega
    rw [hs]
    have hNs : N = (N - 1) + 1 := by omega
    nth_rewrite 1 [hNs]
    rw [Finset.sum_range_succ]
    have hprefix :
        (∑ k ∈ Finset.range (N - 1),
          (k + 1) * progressionWeight (N + 1) (k + 1)) =
          progressionBaseWeight N + N.choose 2 := by
      calc
        _ = ∑ k ∈ Finset.range (N - 1),
              ((k + 1) * progressionWeight N (k + 1) + (k + 1)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mem_range] at hk
            have hw : progressionWeight (N + 1) (k + 1) =
                progressionWeight N (k + 1) + 1 := by
              simp only [progressionWeight]
              omega
            rw [hw]
            ring
        _ = (∑ k ∈ Finset.range (N - 1),
              (k + 1) * progressionWeight N (k + 1)) +
              ∑ k ∈ Finset.range (N - 1), (k + 1) := Finset.sum_add_distrib
        _ = progressionBaseWeight N + N.choose 2 := by
          rw [progressionBaseWeight, sum_progression_steps_eq_choose]
    rw [hprefix]
    have hlastD : N - 1 + 1 = N := by omega
    have hlastW : progressionWeight (N + 1) N = 1 := by
      simp only [progressionWeight]
      omega
    rw [hlastD, hlastW, mul_one, ih]
    have hc2 : (N + 1).choose 2 = N.choose 2 + N := by
      simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ N 1
    have hc3 : (N + 2).choose 3 = (N + 1).choose 2 + (N + 1).choose 3 := by
      simpa using Nat.choose_succ_succ (N + 1) 2
    have hadd : N + 1 + 1 = N + 2 := by omega
    rw [hadd]
    omega

/-- Logarithm of the weighted integer factor `∏ d^(N-d)`. -/
def progressionIntegerLog (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N - 1),
    (progressionWeight N (k + 1) : ℝ) * Real.log (k + 1 : ℕ)

/-- Logarithm of the model primitive quotient
`∏_{1 ≤ d < N} (B^d (exp(d eta)-1))^(N-d)`. -/
def progressionTaxLog (N : ℕ) (B eta : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (N - 1),
    (progressionWeight N (k + 1) : ℝ) *
      Real.log (B ^ (k + 1) * (Real.exp (((k + 1 : ℕ) : ℝ) * eta) - 1))

/-- The positive real product whose logarithm is `progressionTaxLog`. -/
def progressionTaxProduct (N : ℕ) (B eta : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (N - 1),
    (B ^ (k + 1) * (Real.exp (((k + 1 : ℕ) : ℝ) * eta) - 1)) ^
      progressionWeight N (k + 1)

/-- The natural invariant quotient becomes the exact positive tax product after casting to
`ℝ`, with `B = Q` and `eta = log(P/Q)`. -/
theorem cast_progressionInvariantQuotient_eq_taxProduct (N P Q : ℕ) (hQ : 0 < Q)
    (hQP : Q < P) :
    ((progressionInvariantQuotient N P Q : ℕ) : ℝ) =
      progressionTaxProduct N (Q : ℝ) (Real.log ((P : ℝ) / (Q : ℝ))) := by
  rw [progressionInvariantQuotient, progressionTaxProduct]
  push_cast
  apply Finset.prod_congr rfl
  intro k hk
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using
    (cast_progressionDifference_eq (d := k + 1) hQ hQP)

private theorem log_finset_prod_of_ne_zero {s : Finset ℕ} {f : ℕ → ℝ}
    (hf : ∀ k ∈ s, f k ≠ 0) :
    Real.log (∏ k ∈ s, f k) = ∑ k ∈ s, Real.log (f k) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hfa : f a ≠ 0 := hf a (by simp)
      have hfs : ∀ k ∈ s, f k ≠ 0 := fun k hk ↦ hf k (by simp [hk])
      have hprod : ∏ k ∈ s, f k ≠ 0 := (Finset.prod_ne_zero_iff).2 hfs
      rw [Finset.prod_insert ha, Finset.sum_insert ha, Real.log_mul hfa hprod, ih hfs]

/-- `progressionTaxLog` is literally the logarithm of the finite positive model product. -/
theorem log_progressionTaxProduct (N : ℕ) {B eta : ℝ} (hB : 0 < B) (heta : 0 < eta) :
    Real.log (progressionTaxProduct N B eta) = progressionTaxLog N B eta := by
  rw [progressionTaxProduct, progressionTaxLog]
  rw [log_finset_prod_of_ne_zero]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Real.log_pow]
  · intro k hk
    apply pow_ne_zero
    apply mul_ne_zero (pow_ne_zero _ hB.ne')
    apply sub_ne_zero.mpr
    exact ne_of_gt (Real.one_lt_exp_iff.mpr (mul_pos (by positivity) heta))

/-- One power-difference logarithm splits into its base height, small-spacing term, integer
factor, and normalized remainder. -/
theorem log_progression_powerDifference {B eta : ℝ} (hB : 0 < B) (heta : 0 < eta)
    (d : ℕ) (hd : d ≠ 0) :
    Real.log (B ^ d * (Real.exp ((d : ℝ) * eta) - 1)) =
      (d : ℝ) * Real.log B + Real.log eta + Real.log d +
        progressionRho ((d : ℝ) * eta) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have ht : 0 < (d : ℝ) * eta := mul_pos hdR heta
  have hexp : 0 < Real.exp ((d : ℝ) * eta) - 1 :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr ht)
  have hratio : 0 < (Real.exp ((d : ℝ) * eta) - 1) / ((d : ℝ) * eta) :=
    div_pos hexp ht
  have hfactor : Real.exp ((d : ℝ) * eta) - 1 =
      ((d : ℝ) * eta) *
        ((Real.exp ((d : ℝ) * eta) - 1) / ((d : ℝ) * eta)) := by
    field_simp
  have hlogDiff : Real.log (Real.exp ((d : ℝ) * eta) - 1) =
      Real.log d + Real.log eta + progressionRho ((d : ℝ) * eta) := by
    rw [hfactor, Real.log_mul (mul_ne_zero hdR.ne' heta.ne') hratio.ne',
      Real.log_mul hdR.ne' heta.ne', progressionRho, if_neg ht.ne']
  rw [Real.log_mul (pow_ne_zero _ hB.ne') hexp.ne', Real.log_pow, hlogDiff]
  ring

/-- Exact finite denominator-tax identity.  The coefficients are kept as explicit finite sums;
separate combinatorial simplification identifies them with `choose (N+1) 3` and `choose N 2`.
-/
theorem progressionTaxLog_eq (N : ℕ) {B eta : ℝ} (hB : 0 < B) (heta : 0 < eta) :
    progressionTaxLog N B eta =
      (progressionBaseWeight N : ℝ) * Real.log B +
      (progressionEtaWeight N : ℝ) * Real.log eta +
      progressionIntegerLog N + progressionLogRemainder N eta := by
  rw [progressionTaxLog, progressionBaseWeight, progressionEtaWeight,
    progressionIntegerLog, progressionLogRemainder]
  calc
    ∑ k ∈ Finset.range (N - 1),
        (progressionWeight N (k + 1) : ℝ) *
          Real.log (B ^ (k + 1) * (Real.exp (((k + 1 : ℕ) : ℝ) * eta) - 1)) =
      ∑ k ∈ Finset.range (N - 1),
        (progressionWeight N (k + 1) : ℝ) *
          (((k + 1 : ℕ) : ℝ) * Real.log B + Real.log eta +
            Real.log (k + 1 : ℕ) +
              progressionRho (((k + 1 : ℕ) : ℝ) * eta)) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        exact log_progression_powerDifference hB heta (k + 1) (by omega)
    _ =
        ((↑(∑ k ∈ Finset.range (N - 1),
            (k + 1) * progressionWeight N (k + 1)) : ℕ) : ℝ) * Real.log B +
        ((↑(∑ k ∈ Finset.range (N - 1),
            progressionWeight N (k + 1)) : ℕ) : ℝ) * Real.log eta +
        ∑ k ∈ Finset.range (N - 1),
          (progressionWeight N (k + 1) : ℝ) * Real.log (k + 1 : ℕ) +
        ∑ k ∈ Finset.range (N - 1),
          (progressionWeight N (k + 1) : ℝ) *
            progressionRho (((k + 1 : ℕ) : ℝ) * eta) := by
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
      simp only [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Closed-binomial form of the exact denominator-tax identity. -/
theorem progressionTaxLog_eq_choose (N : ℕ) {B eta : ℝ} (hB : 0 < B)
    (heta : 0 < eta) :
    progressionTaxLog N B eta =
      (((N + 1).choose 3 : ℕ) : ℝ) * Real.log B +
      ((N.choose 2 : ℕ) : ℝ) * Real.log eta +
      progressionIntegerLog N + progressionLogRemainder N eta := by
  rw [progressionTaxLog_eq N hB heta, progressionBaseWeight_eq_choose,
    progressionEtaWeight_eq_choose]

/-- The logarithmic remainder is nonnegative and at most `eta` times the base-weight sum. -/
theorem progressionLogRemainder_nonneg_le (N : ℕ) {eta : ℝ} (heta : 0 < eta) :
    0 ≤ progressionLogRemainder N eta ∧
      progressionLogRemainder N eta ≤ (progressionBaseWeight N : ℝ) * eta := by
  constructor
  · rw [progressionLogRemainder]
    apply Finset.sum_nonneg
    intro k hk
    apply mul_nonneg (by positivity)
    exact (progressionRho_nonneg_le (mul_pos (by positivity) heta)).1
  · rw [progressionLogRemainder]
    calc
      ∑ k ∈ Finset.range (N - 1),
          (progressionWeight N (k + 1) : ℝ) *
            progressionRho (((k + 1 : ℕ) : ℝ) * eta) ≤
        ∑ k ∈ Finset.range (N - 1),
          (progressionWeight N (k + 1) : ℝ) *
            (((k + 1 : ℕ) : ℝ) * eta) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left
            (progressionRho_nonneg_le (mul_pos (by positivity) heta)).2 (by positivity)
      _ = (progressionBaseWeight N : ℝ) * eta := by
        rw [progressionBaseWeight]
        push_cast
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        ring

/-- Closed-binomial remainder bound from the report. -/
theorem progressionLogRemainder_nonneg_le_choose (N : ℕ) {eta : ℝ} (heta : 0 < eta) :
    0 ≤ progressionLogRemainder N eta ∧
      progressionLogRemainder N eta ≤ (((N + 1).choose 3 : ℕ) : ℝ) * eta := by
  simpa [progressionBaseWeight_eq_choose] using progressionLogRemainder_nonneg_le N heta

/-- The elementary integer-gap inequality used to expose the denominator tax. -/
theorem log_base_add_log_eta_ge_neg_eta {B eta : ℝ} (hB : 0 < B) (heta : 0 < eta)
    (hgap : 1 ≤ B * (Real.exp eta - 1)) :
    -eta ≤ Real.log B + Real.log eta := by
  have hexp : 0 < Real.exp eta - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr heta)
  have hratio : Real.exp eta - 1 ≤ eta * Real.exp eta := by
    have hneg := Real.add_one_le_exp (-eta)
    have hexpInv : Real.exp (-eta) * Real.exp eta = 1 := by
      rw [← Real.exp_add]
      simp
    have hmul := mul_le_mul_of_nonneg_right hneg (Real.exp_pos eta).le
    rw [add_mul, one_mul, hexpInv] at hmul
    linarith
  have hBbound : 1 ≤ B * eta * Real.exp eta := by
    calc
      1 ≤ B * (Real.exp eta - 1) := hgap
      _ ≤ B * (eta * Real.exp eta) := mul_le_mul_of_nonneg_left hratio hB.le
      _ = B * eta * Real.exp eta := by ring
  have hpos : 0 < B * eta := mul_pos hB heta
  have hlog : 0 ≤ Real.log (B * eta * Real.exp eta) := Real.log_nonneg hBbound
  rw [Real.log_mul (mul_ne_zero hB.ne' heta.ne') (Real.exp_ne_zero eta),
    Real.log_mul hB.ne' heta.ne', Real.log_exp] at hlog
  linarith

/-- The report's denominator-tax lower bound, with the weighted integer factor left in exact
finite-sum form.  `progressionIntegerLog N` is `log (∏_{d=1}^{N-1} d^(N-d))`. -/
theorem progressionTaxLog_lower_bound (N : ℕ) {B eta : ℝ} (hB : 0 < B)
    (heta : 0 < eta) (hgap : 1 ≤ B * (Real.exp eta - 1)) :
    (((N.choose 3 : ℕ) : ℝ) * Real.log eta⁻¹ -
        (((N + 1).choose 3 : ℕ) : ℝ) * eta + progressionIntegerLog N) ≤
      progressionTaxLog N B eta := by
  rw [progressionTaxLog_eq_choose N hB heta]
  have hrem := (progressionLogRemainder_nonneg_le_choose N heta).1
  have hlog := log_base_add_log_eta_ge_neg_eta hB heta hgap
  have hA : (0 : ℝ) ≤ (((N + 1).choose 3 : ℕ) : ℝ) := by positivity
  have hsum : 0 ≤ Real.log B + Real.log eta + eta := by linarith
  have hcore : 0 ≤ (((N + 1).choose 3 : ℕ) : ℝ) *
      (Real.log B + Real.log eta + eta) := mul_nonneg hA hsum
  have hcNat : (N + 1).choose 3 = N.choose 2 + N.choose 3 := by
    simpa using Nat.choose_succ_succ N 2
  have hc : ((((N + 1).choose 3 : ℕ) : ℝ)) =
      ((N.choose 2 : ℕ) : ℝ) + ((N.choose 3 : ℕ) : ℝ) := by
    exact_mod_cast hcNat
  rw [Real.log_inv]
  calc
    ((N.choose 3 : ℕ) : ℝ) * -Real.log eta -
          ((N + 1).choose 3 : ℕ) * eta + progressionIntegerLog N ≤
      ((N.choose 3 : ℕ) : ℝ) * -Real.log eta -
          ((N + 1).choose 3 : ℕ) * eta + progressionIntegerLog N +
          ((N + 1).choose 3 : ℕ) * (Real.log B + Real.log eta + eta) +
          progressionLogRemainder N eta := by linarith
    _ = ((N + 1).choose 3 : ℕ) * Real.log B +
          (N.choose 2 : ℕ) * Real.log eta + progressionIntegerLog N +
          progressionLogRemainder N eta := by rw [hc]; ring

/-- Exact report-style logarithmic expansion for a primitive natural numerator and denominator,
oriented by `Q < P`. -/
theorem log_cast_progressionInvariantQuotient_eq (N P Q : ℕ) (hQ : 0 < Q) (hQP : Q < P) :
    Real.log ((progressionInvariantQuotient N P Q : ℕ) : ℝ) =
      (((N + 1).choose 3 : ℕ) : ℝ) * Real.log Q +
      ((N.choose 2 : ℕ) : ℝ) * Real.log (Real.log ((P : ℝ) / (Q : ℝ))) +
      progressionIntegerLog N +
      progressionLogRemainder N (Real.log ((P : ℝ) / (Q : ℝ))) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hPR : (0 : ℝ) < P := by exact_mod_cast hQ.trans hQP
  have hratio : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQR]
    simpa using (show (Q : ℝ) < P by exact_mod_cast hQP)
  have heta : 0 < Real.log ((P : ℝ) / (Q : ℝ)) := Real.log_pos hratio
  rw [cast_progressionInvariantQuotient_eq_taxProduct N P Q hQ hQP,
    log_progressionTaxProduct N hQR heta, progressionTaxLog_eq_choose N hQR heta]

/-- Fully instantiated denominator-tax lower bound for the primitive natural quotient. -/
theorem log_cast_progressionInvariantQuotient_lower_bound (N P Q : ℕ) (hQ : 0 < Q)
    (hQP : Q < P) :
    (((N.choose 3 : ℕ) : ℝ) *
        Real.log (Real.log ((P : ℝ) / (Q : ℝ)))⁻¹ -
      (((N + 1).choose 3 : ℕ) : ℝ) * Real.log ((P : ℝ) / (Q : ℝ)) +
      progressionIntegerLog N) ≤
        Real.log ((progressionInvariantQuotient N P Q : ℕ) : ℝ) := by
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hPR : (0 : ℝ) < P := by exact_mod_cast hQ.trans hQP
  let eta : ℝ := Real.log ((P : ℝ) / (Q : ℝ))
  have hratio : (1 : ℝ) < (P : ℝ) / (Q : ℝ) := by
    rw [lt_div_iff₀ hQR]
    simpa using (show (Q : ℝ) < P by exact_mod_cast hQP)
  have heta : 0 < eta := Real.log_pos hratio
  have hQRne : (Q : ℝ) ≠ 0 := hQR.ne'
  have hexpEta : Real.exp eta = (P : ℝ) / (Q : ℝ) := by
    exact Real.exp_log (div_pos hPR hQR)
  have hfactor : (Q : ℝ) * (Real.exp eta - 1) = (P - Q : ℕ) := by
    rw [hexpEta]
    rw [Nat.cast_sub hQP.le]
    field_simp
  have hsub : 1 ≤ P - Q := by omega
  have hgap : (1 : ℝ) ≤ (Q : ℝ) * (Real.exp eta - 1) := by
    rw [hfactor]
    exact_mod_cast hsub
  rw [cast_progressionInvariantQuotient_eq_taxProduct N P Q hQ hQP,
    log_progressionTaxProduct N hQR heta]
  exact progressionTaxLog_lower_bound N hQR heta hgap

end

end LeanProofs.TwoBaseIntegerExponent

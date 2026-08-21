import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-!
# Determinant lower bounds over rings of integers

This module gives the field-norm analogue of the elementary fact that a nonzero integer
has absolute value at least one.  A nonzero algebraic-integer determinant cannot be small
at one complex embedding unless it is large at another embedding.  Uniform conjugate
bounds for its entries control this loss through the house of the determinant.

The final two numerical lemmas place the complete loss for the six-exponentials grid on
the same `n ^ 11` scale as the rational-denominator loss used elsewhere in this project.
-/

open scoped Nat

namespace LeanProofs.IntegerExponent

open Matrix

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- The factorial contribution for a size-`n ^ 6` determinant fits below `2 ^ (n ^ 11)`. -/
theorem factorial_sixth_pow_le_two_pow_eleventh_pow
    (n : ℕ) (hn : 2 ≤ n) :
    (n ^ 6).factorial ≤ 2 ^ (n ^ 11) := by
  have hnTwo : n ≤ 2 ^ n := Nat.le_of_lt n.lt_two_pow_self
  have hSix : 6 ≤ n ^ 3 := by
    calc
      6 ≤ 2 ^ 3 := by norm_num
      _ ≤ n ^ 3 := Nat.pow_le_pow_left hn 3
  have hExp : n * (6 * n ^ 6) ≤ n ^ 11 := by
    calc
      n * (6 * n ^ 6) = 6 * n ^ 7 := by ring
      _ ≤ n ^ 3 * n ^ 7 := Nat.mul_le_mul_right _ hSix
      _ = n ^ 10 := by rw [← pow_add]
      _ ≤ n ^ 11 := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    (n ^ 6).factorial ≤ (n ^ 6) ^ (n ^ 6) := Nat.factorial_le_pow _
    _ = n ^ (6 * n ^ 6) := by rw [← pow_mul]
    _ ≤ (2 ^ n) ^ (6 * n ^ 6) :=
      pow_le_pow_left₀ (Nat.zero_le _) hnTwo _
    _ = 2 ^ (n * (6 * n ^ 6)) := by rw [← pow_mul]
    _ ≤ 2 ^ (n ^ 11) := Nat.pow_le_pow_right (by omega) hExp

/-- The degree and conjugate-height loss for the six-exponentials determinant is a single
`n ^ 11`-st power, so the existing denominator-aware analytic margin can absorb it. -/
theorem algebraic_det_loss_le_uniform_power
    (n T degree : ℕ) (hn : 2 ≤ n) :
    ((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) ≤
      ((2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) := by
  have hbase :
      (n ^ 6).factorial * T ^ (6 * n ^ 11) ≤ (2 * T ^ 6) ^ (n ^ 11) := by
    calc
      (n ^ 6).factorial * T ^ (6 * n ^ 11) ≤
          2 ^ (n ^ 11) * T ^ (6 * n ^ 11) :=
        Nat.mul_le_mul_right _ (factorial_sixth_pow_le_two_pow_eleventh_pow n hn)
      _ = 2 ^ (n ^ 11) * (T ^ 6) ^ (n ^ 11) := by rw [← pow_mul]
      _ = (2 * T ^ 6) ^ (n ^ 11) := by rw [mul_pow]
  calc
    ((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1) ≤
        ((2 * T ^ 6) ^ (n ^ 11)) ^ (degree - 1) :=
      Nat.pow_le_pow_left hbase _
    _ = ((2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring

/-- A common entry-clearing scale and the conjugate/degree loss combine into one base
raised to `n ^ 11`. -/
theorem combined_algebraic_loss_le_uniform_power
    (n T degree B : ℕ) (hn : 2 ≤ n) :
    B ^ (n ^ 11) *
        (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1)) ≤
      (B * (2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) := by
  have hloss := algebraic_det_loss_le_uniform_power n T degree hn
  calc
    B ^ (n ^ 11) *
          (((n ^ 6).factorial * T ^ (6 * n ^ 11)) ^ (degree - 1)) ≤
        B ^ (n ^ 11) * ((2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) :=
      Nat.mul_le_mul_left _ hloss
    _ = (B * (2 * T ^ 6) ^ (degree - 1)) ^ (n ^ 11) := by
      exact (mul_pow B ((2 * T ^ 6) ^ (degree - 1)) (n ^ 11)).symm

/-- A nonzero algebraic integer cannot be too small at one embedding once its house is
bounded.  This is the field-norm replacement for `1 ≤ |z|` for nonzero `z : ℤ`. -/
theorem one_div_house_bound_pow_le_norm_embedding
    (alpha : NumberField.RingOfIntegers K) (halpha : alpha ≠ 0) (sigma : K →+* ℂ)
    {H : ℝ} (hH : NumberField.house (alpha : K) ≤ H) :
    1 / H ^ (Module.finrank ℚ K - 1) ≤ ‖sigma (alpha : K)‖ := by
  have hhouseOne : 1 ≤ NumberField.house (alpha : K) :=
    NumberField.one_le_house_of_isIntegral alpha.property
      (by
        intro h
        apply halpha
        rw [NumberField.RingOfIntegers.ext_iff]
        exact h)
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one (hhouseOne.trans hH)
  have hnormNe : Algebra.norm ℤ alpha ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr halpha
  have hnormOne : (1 : ℝ) ≤ ‖Algebra.norm ℚ (alpha : K)‖ := by
    rw [← Algebra.coe_norm_int]
    rw [Int.norm_cast_rat, Int.norm_eq_abs, ← Int.cast_one, ← Int.cast_abs, Int.cast_le]
    exact Int.one_le_abs hnormNe
  have hnormUpper := NumberField.norm_norm_le_norm_mul_house_pow (alpha : K) sigma
  have hprod : (1 : ℝ) ≤ ‖sigma (alpha : K)‖ * H ^ (Module.finrank ℚ K - 1) := by
    calc
      (1 : ℝ) ≤ ‖Algebra.norm ℚ (alpha : K)‖ := hnormOne
      _ ≤ ‖sigma (alpha : K)‖ * NumberField.house (alpha : K) ^
          (Module.finrank ℚ K - 1) := hnormUpper
      _ ≤ ‖sigma (alpha : K)‖ * H ^ (Module.finrank ℚ K - 1) := by
        gcongr
  exact (div_le_iff₀ (pow_pos hHpos _)).2 (by simpa [mul_comm] using hprod)

/-- Determinant form of `one_div_house_bound_pow_le_norm_embedding`, with the chosen
complex embedding applied entrywise to a matrix over the ring of integers. -/
theorem one_div_house_bound_pow_le_norm_det
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : Matrix iota iota (NumberField.RingOfIntegers K)) (hdet : A.det ≠ 0)
    (sigma : K →+* ℂ) {H : ℝ}
    (hH : NumberField.house ((A.det : NumberField.RingOfIntegers K) : K) ≤ H) :
    1 / H ^ (Module.finrank ℚ K - 1) ≤
      ‖Matrix.det (fun i j ↦ sigma (A i j : K))‖ := by
  have h := one_div_house_bound_pow_le_norm_embedding A.det hdet sigma hH
  let f : NumberField.RingOfIntegers K →+* ℂ :=
    sigma.comp (algebraMap (NumberField.RingOfIntegers K) K)
  have hmap : f A.det = Matrix.det (f.mapMatrix A) := f.map_det A
  have hmatrix : f.mapMatrix A = A.map (fun z ↦ sigma (z : K)) := by
    ext i j
    simp only [f, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_comp,
      Function.comp_apply, NumberField.RingOfIntegers.coe_eq_algebraMap]
  change 1 / H ^ (Module.finrank ℚ K - 1) ≤ ‖f A.det‖ at h
  rw [hmap, hmatrix] at h
  change 1 / H ^ (Module.finrank ℚ K - 1) ≤
    ‖Matrix.det (A.map (fun z ↦ sigma (z : K)))‖
  exact h

/-- A uniform bound for all conjugates of all entries gives a factorial-times-power
bound for the house of an algebraic-integer determinant. -/
theorem house_det_le_factorial_mul_pow
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : Matrix iota iota (NumberField.RingOfIntegers K)) {E : ℝ}
    (hentry : ∀ (tau : K →+* ℂ) i j, ‖tau (A i j : K)‖ ≤ E) :
    NumberField.house ((A.det : NumberField.RingOfIntegers K) : K) ≤
      (Fintype.card iota).factorial • E ^ Fintype.card iota := by
  rw [NumberField.house, NumberField.canonicalEmbedding.norm_le_iff]
  intro tau
  let f : NumberField.RingOfIntegers K →+* ℂ :=
    tau.comp (algebraMap (NumberField.RingOfIntegers K) K)
  have hmap : f A.det = Matrix.det (f.mapMatrix A) := f.map_det A
  have hmatrix : f.mapMatrix A = A.map (fun z ↦ tau (z : K)) := by
    ext i j
    simp only [f, RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_comp,
      Function.comp_apply, NumberField.RingOfIntegers.coe_eq_algebraMap]
  change ‖tau ((A.det : NumberField.RingOfIntegers K) : K)‖ ≤ _
  change ‖f A.det‖ ≤ _
  rw [hmap, hmatrix]
  exact Matrix.det_le (abv := IsAbsoluteValue.toAbsoluteValue (norm : ℂ → ℝ))
    (hentry tau)

/-- Entrywise form of the algebraic-integer determinant lower bound. -/
theorem one_div_conjugate_entry_bound_le_norm_det
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (A : Matrix iota iota (NumberField.RingOfIntegers K)) (hdet : A.det ≠ 0)
    (sigma : K →+* ℂ) {E : ℝ}
    (hentry : ∀ (tau : K →+* ℂ) i j, ‖tau (A i j : K)‖ ≤ E) :
    1 / ((Fintype.card iota).factorial • E ^ Fintype.card iota) ^
        (Module.finrank ℚ K - 1) ≤
      ‖Matrix.det (fun i j ↦ sigma (A i j : K))‖ :=
  one_div_house_bound_pow_le_norm_det A hdet sigma
    (house_det_le_factorial_mul_pow A hentry)

/-- Glue from a scaled matrix over the ring of integers to a chosen complex analytic
matrix.  If every embedded entry is `Q` times the corresponding analytic entry, the
determinant acquires the factor `Q ^ card`. -/
theorem one_div_entry_bound_le_scaled_norm_det
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (Z : Matrix iota iota (NumberField.RingOfIntegers K)) (hdet : Z.det ≠ 0)
    (A : Matrix iota iota ℂ) (sigma : K →+* ℂ) (Q : ℕ) {E : ℝ}
    (hmap : ∀ i j, sigma (Z i j : K) = (Q : ℂ) * A i j)
    (hentry : ∀ (tau : K →+* ℂ) i j, ‖tau (Z i j : K)‖ ≤ E) :
    1 / ((Fintype.card iota).factorial • E ^ Fintype.card iota) ^
          (Module.finrank ℚ K - 1) ≤
      (Q : ℝ) ^ Fintype.card iota * ‖A.det‖ := by
  have hlower := one_div_conjugate_entry_bound_le_norm_det Z hdet sigma hentry
  have hmatrix : (fun i j ↦ sigma (Z i j : K)) = (Q : ℂ) • A := by
    ext i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using hmap i j
  rw [hmatrix, Matrix.det_smul, norm_mul, norm_pow] at hlower
  simpa using hlower

end


end LeanProofs.IntegerExponent

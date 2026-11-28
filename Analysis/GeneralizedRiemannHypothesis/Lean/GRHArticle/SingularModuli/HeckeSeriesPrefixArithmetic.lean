import GRHArticle.SingularModuli.HeckePackedPolynomialArithmetic
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Exact finite prefixes of integer series

The executable operations retain only a fixed requested prefix. Their
correctness relates the coefficients to the corresponding formal series.
-/

namespace GRHArticle.SingularModuli

open PowerSeries
open scoped PowerSeries

/-- The first `N` coefficients of the formal series are given by `xs`. -/
def SeriesPrefix (N : ℕ) (xs : List ℤ) (F : ℤ⟦X⟧) : Prop :=
  ∀ i : Fin N, xs.getD i 0 = F.coeff i

namespace SeriesPrefix

variable {N : ℕ} {A B : ℤ⟦X⟧} {xs ys : List ℤ}

/-- Store the first `N` values of a coefficient function. -/
def read (N : ℕ) (f : ℕ → ℤ) : List ℤ := List.ofFn fun i : Fin N ↦ f i

@[simp] theorem getD_read (N : ℕ) (f : ℕ → ℤ) (i : Fin N) :
    (read N f).getD i 0 = f i := by
  simp only [read, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dif_pos,
    Option.getD_some]

theorem of_mk (N : ℕ) (f : ℕ → ℤ) : SeriesPrefix N (read N f) (PowerSeries.mk f) := by
  intro i
  rw [getD_read, coeff_mk]

theorem const (N : ℕ) (c : ℤ) :
    SeriesPrefix N (read N fun i ↦ if i = 0 then c else 0) (C c) := by
  intro i
  rw [getD_read, coeff_C]

/-- Add finite coefficient prefixes. -/
def add (N : ℕ) (xs ys : List ℤ) : List ℤ :=
  read N fun i ↦ xs.getD i 0 + ys.getD i 0

theorem add_spec (ha : SeriesPrefix N xs A) (hb : SeriesPrefix N ys B) :
    SeriesPrefix N (add N xs ys) (A + B) := by
  intro i
  rw [add, getD_read, ha i, hb i, map_add]

/-- Subtract finite coefficient prefixes. -/
def sub (N : ℕ) (xs ys : List ℤ) : List ℤ :=
  read N fun i ↦ xs.getD i 0 - ys.getD i 0

theorem sub_spec (ha : SeriesPrefix N xs A) (hb : SeriesPrefix N ys B) :
    SeriesPrefix N (sub N xs ys) (A - B) := by
  intro i
  rw [sub, getD_read, ha i, hb i, map_sub]

/-- Scale all coefficients by the same integer. -/
def scale (N : ℕ) (c : ℤ) (xs : List ℤ) : List ℤ :=
  read N fun i ↦ c * xs.getD i 0

theorem scale_spec (ha : SeriesPrefix N xs A) (c : ℤ) :
    SeriesPrefix N (scale N c xs) (C c * A) := by
  intro i
  rw [scale, getD_read, ha i, coeff_C_mul]

theorem mul_spec (ha : SeriesPrefix N xs A) (hb : SeriesPrefix N ys B) :
    SeriesPrefix N (multiplyPackedIntegerPolynomial N xs ys) (A * B) := by
  intro i
  rw [getD_multiplyPackedIntegerPolynomial N xs ys i, Polynomial.coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have h := Finset.mem_antidiagonal.mp hj
  rw [coeff_coefficientListPolynomial, coeff_coefficientListPolynomial,
    ha ⟨j.1, by have := i.isLt; omega⟩, hb ⟨j.2, by have := i.isLt; omega⟩]

/-- Shift a prefix by `d` powers of the series variable. -/
def shift (N d : ℕ) (xs : List ℤ) : List ℤ :=
  read N fun i ↦ if d ≤ i then xs.getD (i-d) 0 else 0

theorem shift_spec (ha : SeriesPrefix N xs A) (d : ℕ) :
    SeriesPrefix N (shift N d xs) (X ^ d * A) := by
  intro i
  rw [shift, getD_read, coeff_X_pow_mul']
  split_ifs
  · exact ha ⟨i-d, (Nat.sub_le ..).trans_lt i.isLt⟩
  · rfl

/-- Substitute the `d`th power of the variable in a prefix. -/
def substitutePower (N d : ℕ) (xs : List ℤ) : List ℤ :=
  read N fun i ↦ if d ∣ i then xs.getD (i/d) 0 else 0

theorem substitutePower_spec (ha : SeriesPrefix N xs A) (d : ℕ) (hd : d ≠ 0) :
    SeriesPrefix N (substitutePower N d xs) (expand d hd A) := by
  intro i
  rw [substitutePower, getD_read, coeff_expand]
  split_ifs
  · exact ha ⟨i/d, (Nat.div_le_self ..).trans_lt i.isLt⟩
  · rfl

/-- Compute a power, retaining only the requested prefix at each step. -/
def pow (N : ℕ) (xs : List ℤ) : ℕ → List ℤ
  | 0 => read N fun i ↦ if i = 0 then 1 else 0
  | n+1 => multiplyPackedIntegerPolynomial N (pow N xs n) xs

theorem pow_spec (ha : SeriesPrefix N xs A) (n : ℕ) : SeriesPrefix N (pow N xs n) (A^n) := by
  induction n with
  | zero => simpa only [pow, pow_zero, map_one] using const N 1
  | succ n ih => simpa only [pow, pow_succ] using mul_spec ih ha

private noncomputable def unitInverseApproximation (A : ℤ⟦X⟧) : ℕ → ℤ⟦X⟧
  | 0 => 1
  | k+1 =>
    let V := unitInverseApproximation A k
    V * (C 2 - A * V)

private theorem dvd_residual_unitInverseApproximation {A : ℤ⟦X⟧} (ha : A.constantCoeff = 1)
    (k : ℕ) : X ^ (2^k) ∣ 1 - A * unitInverseApproximation A k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_one, unitInverseApproximation, mul_one, X_dvd_iff]
    simp [ha]
  | succ k ih =>
    have h : 1 - A * unitInverseApproximation A (k+1) =
        (1 - A * unitInverseApproximation A k)^2 := by
      simp only [unitInverseApproximation, map_ofNat]
      ring
    rw [h, pow_succ, pow_mul]
    exact pow_dvd_pow_of_dvd ih 2

/-- Repeated Newton inversion of a unit series, truncated after each
operation. Each step doubles the guaranteed number of correct coefficients. -/
def inverseUnit (N : ℕ) (xs : List ℤ) : ℕ → List ℤ
  | 0 => read N fun i ↦ if i = 0 then 1 else 0
  | k+1 =>
    let V := inverseUnit N xs k
    multiplyPackedIntegerPolynomial N V
      (sub N (read N fun i ↦ if i = 0 then 2 else 0) (multiplyPackedIntegerPolynomial N xs V))

theorem inverseUnit_spec (ha : SeriesPrefix N xs A) (hA : A.constantCoeff = 1) (k : ℕ)
    (hN : N ≤ 2 ^ k) : SeriesPrefix N (inverseUnit N xs k) (invOfUnit A 1) := by
  have happrox (j : ℕ) :
      SeriesPrefix N (inverseUnit N xs j) (unitInverseApproximation A j) := by
    induction j with
    | zero => simpa only [inverseUnit, unitInverseApproximation, map_one] using const N 1
    | succ j ih =>
      simpa only [inverseUnit, unitInverseApproximation] using
        mul_spec ih (sub_spec (const N 2) (mul_spec ha ih))
  have hd : X ^ (2^k) ∣ invOfUnit A 1 - unitInverseApproximation A k := by
    have h : invOfUnit A 1 - unitInverseApproximation A k =
        invOfUnit A 1 * (1 - A * unitInverseApproximation A k) := by
      rw [mul_sub, mul_one, ← mul_assoc, invOfUnit_mul A 1 hA, one_mul]
    rw [h]
    exact dvd_mul_of_dvd_right (dvd_residual_unitInverseApproximation hA k) _
  intro i
  have he := (X_pow_dvd_iff.mp hd) i ((i.isLt).trans_le hN)
  rw [map_sub, sub_eq_zero] at he
  exact (happrox k i).trans he.symm

end SeriesPrefix

end GRHArticle.SingularModuli

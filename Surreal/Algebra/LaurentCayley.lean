import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Clearing a Laurent polynomial in Cayley coordinates

Algebraic prerequisites for `trigonometry:thm:stability`: the substitution
`Z = z * (1 + c X) / (1 - c X)` has a polynomial numerator with common
denominator `(1 - c² X²)^N`. Its constant and linear coefficients are exact.
The Laurent polynomial and its evaluation are Mathlib's existing constructions.
-/

namespace Surreal.LaurentCayley

open Polynomial
open scoped BigOperators

noncomputable section

variable {K : Type*}

section Ring

variable [CommRing K]

/-- The cleared numerator of one integer frequency, for a degree bound `N`. -/
def frequency (c : K) (N : ℕ) (k : ℤ) : K[X] :=
  (1 + C c * X) ^ (N + k).toNat * (1 - C c * X) ^ (N - k).toNat

/-- A denominator shared by all frequencies between `-N` and `N`. -/
def denominator (c : K) (N : ℕ) : K[X] :=
  ((1 + C c * X) * (1 - C c * X)) ^ N

/-- The polynomial numerator at the base phase `z`. -/
def numerator (p : LaurentPolynomial K) (z : Kˣ) (c : K) (N : ℕ) : K[X] :=
  p.coeff.sum fun k a => C (a * (z ^ k).val) * frequency c N k

/-- Numerator formation is additive when the same denominator bound is used. -/
theorem numerator_add (p q : LaurentPolynomial K) (z : Kˣ) (c : K) (N : ℕ) :
    numerator (p + q) z c N = numerator p z c N + numerator q z c N := by
  simp only [numerator, AddMonoidAlgebra.coeff_add]
  exact Finsupp.sum_add_index (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul])

/-- Every Laurent polynomial admits an absolute frequency bound. -/
theorem exists_frequency_bound (p : LaurentPolynomial K) :
    ∃ N : ℕ, ∀ k ∈ p.coeff.support, k.natAbs ≤ N :=
  ⟨p.coeff.support.sup Int.natAbs, fun _ hk => Finset.le_sup hk⟩

@[simp] theorem frequency_coeff_zero (c : K) (N : ℕ) (k : ℤ) :
    (frequency c N k).coeff 0 = 1 := by
  simp [frequency, coeff_zero_eq_eval_zero]

private theorem coeff_one_pow (P : K[X]) (hP : P.coeff 0 = 1) (n : ℕ) :
    (P ^ n).coeff 1 = n * P.coeff 1 := by
  induction n with
  | zero => simp [coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_coeff_one, ih]
    have h0 : (P ^ n).coeff 0 = 1 := by
      simpa only [coeff_zero_eq_eval_zero, eval_pow, one_pow] using
        congrArg (fun x : K => x ^ n) hP
    rw [h0, hP]
    push_cast
    ring

/-- The frequency numerator has linear coefficient `2 k c`, independent of `N`. -/
theorem frequency_coeff_one (c : K) (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N) :
    (frequency c N k).coeff 1 = 2 * (k : K) * c := by
  have hp : 0 ≤ (N : ℤ) + k := by omega
  have hm : 0 ≤ (N : ℤ) - k := by omega
  have he : (((N : ℤ) + k).toNat : K) - (((N : ℤ) - k).toNat : K) =
      2 * (k : K) := by
    have hi : (((N : ℤ) + k).toNat : ℤ) - (((N : ℤ) - k).toNat : ℤ) = 2 * k := by
      omega
    have hc := congrArg (fun j : ℤ => (j : K)) hi
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat] using hc
  unfold frequency
  rw [mul_coeff_one, coeff_one_pow _ (by simp), coeff_one_pow _ (by simp)]
  simp [coeff_zero_eq_eval_zero, coeff_one]
  linear_combination he * c

@[simp] theorem denominator_coeff_zero (c : K) (N : ℕ) :
    (denominator c N).coeff 0 = 1 := by
  simp [denominator, coeff_zero_eq_eval_zero]

@[simp] theorem denominator_coeff_one (c : K) (N : ℕ) :
    (denominator c N).coeff 1 = 0 := by
  rw [denominator, coeff_one_pow _ (by simp [coeff_zero_eq_eval_zero]), mul_coeff_one]
  simp [coeff_one]

/-- Clearing denominators preserves the value at the center exactly. -/
theorem numerator_coeff_zero (p : LaurentPolynomial K) (z : Kˣ) (c : K) (N : ℕ) :
    (numerator p z c N).coeff 0 = p.smeval z := by
  simp [numerator, LaurentPolynomial.smeval, Finsupp.sum, smul_eq_mul]

/-- The first coefficient is the frequency-weighted sum, with factor `2c`. -/
theorem numerator_coeff_one (p : LaurentPolynomial K) (z : Kˣ) (c : K) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    (numerator p z c N).coeff 1 =
      ∑ k ∈ p.coeff.support, p.coeff k * (z ^ k).val * (2 * (k : K) * c) := by
  simp only [numerator, Finsupp.sum, finsetSum_coeff, coeff_C_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [frequency_coeff_one c N k (hN k hk)]

/-- The common denominator is even and has no linear term. -/
theorem denominator_eq (c : K) (N : ℕ) :
    denominator c N = (1 - C (c ^ 2) * X ^ 2) ^ N := by
  unfold denominator
  congr 1
  rw [map_pow]
  ring

/-- The frequency construction commutes with coefficient homomorphisms. -/
theorem map_frequency {L : Type*} [CommRing L] (f : K →+* L)
    (c : K) (N : ℕ) (k : ℤ) :
    (frequency c N k).map f = frequency (f c) N k := by
  simp [frequency]

/-- Frequency numerators introduce no coefficients outside the given subring. -/
theorem frequency_coeff_mem (S : Subring K) (c : K) (hc : c ∈ S)
    (N : ℕ) (k : ℤ) (j : ℕ) : (frequency c N k).coeff j ∈ S := by
  have he := congrArg (fun P : K[X] => P.coeff j)
    (map_frequency S.subtype (⟨c, hc⟩ : S) N k)
  rw [coeff_map] at he
  change (((frequency (⟨c, hc⟩ : S) N k).coeff j : S) : K) =
    (frequency c N k).coeff j at he
  rw [← he]
  exact ((frequency (⟨c, hc⟩ : S) N k).coeff j).property

/-- A finite coefficient sum of finite frequencies stays in the coefficient subring. -/
theorem numerator_coeff_mem (S : Subring K) (p : LaurentPolynomial K) (z : Kˣ)
    (c : K) (N : ℕ) (hc : c ∈ S)
    (hp : ∀ k ∈ p.coeff.support, p.coeff k ∈ S)
    (hz : ∀ k : ℤ, (z ^ k).val ∈ S) (j : ℕ) :
    (numerator p z c N).coeff j ∈ S := by
  simp only [numerator, Finsupp.sum, finsetSum_coeff, coeff_C_mul]
  apply S.sum_mem
  intro k hk
  exact S.mul_mem (S.mul_mem (hp k hk) (hz k)) (frequency_coeff_mem S c hc N k j)

end Ring

section Field

variable [Field K]

/-- One cleared frequency is exactly the rational Cayley substitution. -/
theorem eval_frequency (c x : K) (N : ℕ) (k : ℤ) (hk : k.natAbs ≤ N)
    (hp : 1 + c * x ≠ 0) (hm : 1 - c * x ≠ 0) :
    (frequency c N k).eval x =
      (denominator c N).eval x * ((1 + c * x) / (1 - c * x)) ^ k := by
  simp only [frequency, denominator, eval_mul, eval_pow, eval_add, eval_one, eval_C,
    eval_X, eval_sub]
  rcases k with n | n
  · have h : n ≤ N := by simpa using hk
    simp only [Int.ofNat_eq_natCast, ← Int.natCast_add, Int.toNat_natCast,
      Int.toNat_sub, zpow_natCast, div_pow, pow_add, mul_pow]
    rw [pow_sub₀ _ hm h]
    ring
  · have h : n + 1 ≤ N := by simpa using hk
    have ha : ((N : ℤ) + Int.negSucc n).toNat = N - (n + 1) := by omega
    have hb : ((N : ℤ) - Int.negSucc n).toNat = N + (n + 1) := by omega
    rw [ha, hb, zpow_negSucc, div_pow, inv_div, pow_add, mul_pow, pow_sub₀ _ hp h]
    ring

/-- Exact evaluation of the numerator; the chart is evaluated at an actual unit. -/
theorem eval_numerator (p : LaurentPolynomial K) (z : Kˣ) (c x : K) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N)
    (hp : 1 + c * x ≠ 0) (hm : 1 - c * x ≠ 0) :
    (numerator p z c N).eval x = (denominator c N).eval x *
      p.smeval (z * Units.mk0 ((1 + c * x) / (1 - c * x)) (div_ne_zero hp hm)) := by
  simp only [numerator, Finsupp.sum, eval_finsetSum, eval_mul, eval_C,
    LaurentPolynomial.smeval, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [eval_frequency c x N k (hN k hk) hp hm]
  simp only [mul_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  ring

end Field

end
end Surreal.LaurentCayley

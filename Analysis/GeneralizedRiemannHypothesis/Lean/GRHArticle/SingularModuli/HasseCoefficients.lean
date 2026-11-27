import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Ring

/-!
# Hasse coefficients in characteristics seven, thirteen, and nineteen

For a nonsingular short Weierstrass model we compute the coefficient of
`X ^ (p-1)` in the power of its cubic appearing in the Hasse criterion.
The resulting conditions give the j-invariants used in `smd:lem:reduction(iv)`.
-/

open Polynomial
namespace GRHArticle.SingularModuli
variable {K : Type*} [Field K]

/-- The coefficient of the short Weierstrass cubic used in the Hasse criterion. -/
noncomputable def hasseCoefficient (p : ℕ) (A B : K) : K :=
  (((X ^ 3 + C A * X + C B : K[X]) ^ ((p - 1) / 2)).coeff (p - 1))

private theorem cubicCoeff_succ (A B : K) (k i : ℕ) :
    let f := (X ^ 3 + C A * X + C B : K[X])
    (f ^ (k + 1)).coeff i =
      (if 3 ≤ i then (f ^ k).coeff (i - 3) else 0) +
      (if 1 ≤ i then (f ^ k).coeff (i - 1) * A else 0) +
      (f ^ k).coeff i * B := by
  intro f
  rw [pow_succ]
  conv_lhs => arg 1; rhs; change X ^ 3 + C A * X + C B
  rw [mul_add, mul_add, ← mul_assoc, coeff_add, coeff_add,
    coeff_mul_X_pow', coeff_mul_C]
  conv_lhs => arg 1; rhs; arg 1; rhs; rw [← pow_one X]
  rw [coeff_mul_X_pow']
  split <;> simp [coeff_mul_C]

private def coefficientRec {R : Type*} [CommRing R] (A B : R) : ℕ → ℕ → R
  | 0, i => if i = 0 then 1 else 0
  | k + 1, i =>
    (if 3 ≤ i then coefficientRec A B k (i - 3) else 0) +
    (if 1 ≤ i then coefficientRec A B k (i - 1) * A else 0) +
    coefficientRec A B k i * B

private theorem coeff_eq_rec (A B : K) (k i : ℕ) :
    (((X ^ 3 + C A * X + C B : K[X]) ^ k).coeff i) = coefficientRec A B k i := by
  induction k generalizing i with
  | zero => simp [coefficientRec, coeff_one]
  | succ k ih => simp only [cubicCoeff_succ, coefficientRec, ih]

/-- The sixth coefficient of the cube of the Weierstrass cubic. -/
theorem hasseCoefficient_seven (A B : K) :
    hasseCoefficient 7 A B = 3 * B := by
  norm_num [hasseCoefficient, coeff_eq_rec, coefficientRec]
  ring

/-- The twelfth coefficient of the sixth power of the Weierstrass cubic. -/
theorem hasseCoefficient_thirteen (A B : K) :
    hasseCoefficient 13 A B = 20 * A ^ 3 + 15 * B ^ 2 := by
  norm_num [hasseCoefficient, coeff_eq_rec, coefficientRec]
  ring

/-- Reduction of the eighteenth coefficient of the ninth power in characteristic nineteen. -/
theorem hasseCoefficient_nineteen [CharP K 19] (A B : K) :
    hasseCoefficient 19 A B = B * (10 * A ^ 3 + 8 * B ^ 2) := by
  norm_num [hasseCoefficient, coeff_eq_rec, coefficientRec]
  ring_nf
  reduce_mod_char!

variable (W : WeierstrassCurve K) [W.IsShortNF] [W.IsElliptic]

/-- With zero linear coefficient, substitution of `X³` in a binomial
gives the Hasse coefficient for every prime congruent to one modulo three. -/
theorem hasseCoefficient_zero_linear (p : ℕ) (B : K) (h : 3 ∣ p - 1) :
    hasseCoefficient p 0 B =
      B ^ ((p - 1) / 2 - (p - 1) / 3) * (((p - 1) / 2).choose ((p - 1) / 3) : K) := by
  have hsub : (X ^ 3 + C (0 : K) * X + C B : K[X]) = expand K 3 (X + C B) := by simp
  rw [hasseCoefficient, hsub, ← map_pow, coeff_expand (by decide : 0 < 3), if_pos h,
    coeff_X_add_C_pow]

/-- At `j = 0` the Hasse coefficient is nonzero in characteristic
`p ≡ 1 (mod 3)`, as used in `smd:lem:reduction(iii)`. -/
theorem hasseCoefficient_ne_zero_of_j_zero {p : ℕ} [hp : Fact p.Prime] [CharP K p]
    (hmod : p % 3 = 1) (hj : W.j = 0) : hasseCoefficient p W.a₄ W.a₆ ≠ 0 := by
  have hp2 := hp.out.two_le
  have hp3 : 3 < p := by omega
  have h48 : ¬p ∣ 48 := by
    rw [show 48 = 2 ^ 4 * 3 by decide, hp.out.dvd_mul]
    rintro (h | h)
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.out.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h
      omega
  have hn : (48 : K) ≠ 0 := (CharP.cast_eq_zero_iff K p 48).not.mpr h48
  have hc := W.j_eq_zero_iff.mp hj
  rw [W.c₄_of_isShortNF, mul_eq_zero] at hc
  have ha : W.a₄ = 0 := hc.resolve_left (neg_ne_zero.mpr hn)
  have hb : W.a₆ ≠ 0 := by
    intro he
    apply W.isUnit_Δ.ne_zero
    rw [W.Δ_of_isShortNF, ha, he]
    ring
  have hdiv : 3 ∣ p - 1 := by omega
  rw [ha, hasseCoefficient_zero_linear p _ hdiv]
  apply mul_ne_zero (pow_ne_zero _ hb)
  apply (CharP.cast_eq_zero_iff K p _).not.mpr
  exact hp.out.coprime_iff_not_dvd.mp (hp.out.coprime_choose_of_lt (by omega) (by omega))

private theorem short_j_eq_iff (v : K) :
    W.j = v ↔ (-48 * W.a₄) ^ 3 - v * (-16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)) = 0 := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    inv_mul_eq_div, div_eq_iff W.isUnit_Δ.ne_zero, W.c₄_of_isShortNF, W.Δ_of_isShortNF, sub_eq_zero]

/-- Over any field of characteristic seven, the Hasse coefficient of a
nonsingular short model vanishes precisely at `j = 6`. -/
theorem hasseCoefficient_seven_eq_zero_iff_j [CharP K 7] :
    hasseCoefficient 7 W.a₄ W.a₆ = 0 ↔ W.j = 6 := by
  rw [hasseCoefficient_seven, short_j_eq_iff]
  have h (A B : K) : (-48 * A) ^ 3 - 6 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = 2 * B ^ 2 := by
    ring_nf
    reduce_mod_char!
  rw [h, mul_eq_zero, mul_eq_zero]
  simp [show (3 : K) ≠ 0 from (CharP.cast_eq_zero_iff K 7 3).not.mpr (by decide),
    show (2 : K) ≠ 0 from (CharP.cast_eq_zero_iff K 7 2).not.mpr (by decide)]

/-- The characteristic-thirteen Hasse coefficient vanishes precisely at `j = 5`. -/
theorem hasseCoefficient_thirteen_eq_zero_iff_j [CharP K 13] :
    hasseCoefficient 13 W.a₄ W.a₆ = 0 ↔ W.j = 5 := by
  rw [hasseCoefficient_thirteen, short_j_eq_iff]
  have h (A B : K) : (-48 * A) ^ 3 - 5 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = 20 * A ^ 3 + 15 * B ^ 2 := by
    ring_nf
    reduce_mod_char!
    ring_nf
    reduce_mod_char!
  rw [h]

/-- The characteristic-nineteen Hasse coefficient vanishes precisely at
`j = 18` and `j = 7`. -/
theorem hasseCoefficient_nineteen_eq_zero_iff_j [CharP K 19] :
    hasseCoefficient 19 W.a₄ W.a₆ = 0 ↔ W.j = 18 ∨ W.j = 7 := by
  rw [hasseCoefficient_nineteen, short_j_eq_iff, short_j_eq_iff]
  have h18 (A B : K) : (-48 * A) ^ 3 - 18 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = 5 * B ^ 2 := by
    ring_nf
    reduce_mod_char!
  have h7 (A B : K) : (-48 * A) ^ 3 - 7 * (-16 * (4 * A ^ 3 + 27 * B ^ 2)) = 17 * (10 * A ^ 3 + 8 * B ^ 2) := by
    ring_nf
    reduce_mod_char!
    ring
  rw [h18, h7, mul_eq_zero]
  simp [mul_eq_zero, show (5 : K) ≠ 0 from (CharP.cast_eq_zero_iff K 19 5).not.mpr (by decide),
    show (17 : K) ≠ 0 from (CharP.cast_eq_zero_iff K 19 17).not.mpr (by decide)]

end GRHArticle.SingularModuli

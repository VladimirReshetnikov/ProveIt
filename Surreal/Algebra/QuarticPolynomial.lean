import Surreal.Algebra.QuarticConstants
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The native six-witness quartic polynomial

The exact total-degree assertion in `odg:thm:standarddef` and
`odg:eq:standardquartic`. Variable 0 is t, variables 1 and 2 are x and y,
and variables 3 through 6 are the four square witnesses.
-/

namespace Surreal.QuarticConstants

open MvPolynomial

noncomputable section

private def squareIndex (j : Fin 4) : Fin 7 := ⟨j.val + 3, by omega⟩

/-- The quartic as an integer polynomial in one input and six existential variables. -/
def polynomial : MvPolynomial (Fin 7) ℤ :=
  value (X 0) (X 1) (X 2) (fun j => X (squareIndex j))

/-- Evaluation agrees with the formula over every commutative ring. -/
theorem eval₂_polynomial {R : Type*} [CommRing R] (a : Fin 7 → R) :
    polynomial.eval₂ (Int.castRingHom R) a =
      value (a 0) (a 1) (a 2) (fun j => a ⟨j.val + 3, by omega⟩) := by
  simp [polynomial, value, squareIndex, eval₂_sum]

private theorem degreeOf_sub_left {p q : MvPolynomial (Fin 7) ℤ}
    (h : q.degreeOf 1 < p.degreeOf 1) : (p - q).degreeOf 1 = p.degreeOf 1 := by
  rw [sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt (by simpa only [degreeOf_neg] using h)]

/-- The degree is exactly four, with ordinary integer coefficients and no parameters. -/
theorem polynomial_totalDegree : polynomial.totalDegree = 4 := by
  let a : MvPolynomial (Fin 7) ℤ := X 1 ^ 2 - C 2 * X 2 ^ 2 - 1
  let s : MvPolynomial (Fin 7) ℤ := ∑ j : Fin 4, X (squareIndex j) ^ 2
  let b : MvPolynomial (Fin 7) ℤ := X 1 - X 0 ^ 2 - s
  have ha : a.totalDegree ≤ 2 := by
    have h₁ := totalDegree_mul (C 2 : MvPolynomial (Fin 7) ℤ) (X 2 ^ 2)
    have h₂ := totalDegree_sub (X 1 ^ 2 : MvPolynomial (Fin 7) ℤ) (C 2 * X 2 ^ 2)
    have h₃ := totalDegree_sub (X 1 ^ 2 - C 2 * X 2 ^ 2 : MvPolynomial (Fin 7) ℤ) 1
    simp only [totalDegree_C, totalDegree_X_pow, totalDegree_one, zero_add] at h₁ h₂ h₃
    dsimp [a]
    omega
  have hs : s.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro j _
    simp only [totalDegree_X_pow, le_refl]
  have hb : b.totalDegree ≤ 2 := by
    have h₁ := totalDegree_sub (X 1 : MvPolynomial (Fin 7) ℤ) (X 0 ^ 2)
    have h₂ := totalDegree_sub (X 1 - X 0 ^ 2 : MvPolynomial (Fin 7) ℤ) s
    simp only [totalDegree_X, totalDegree_X_pow] at h₁
    dsimp [b]
    omega
  have ha' : a.degreeOf 1 = 2 := by
    have h₁ := degreeOf_mul_le 1 (C 2 : MvPolynomial (Fin 7) ℤ) (X 2 ^ 2)
    simp only [degreeOf_C, degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 7) ≠ 2), zero_add] at h₁
    have h₂ : (X 1 ^ 2 - C 2 * X 2 ^ 2 : MvPolynomial (Fin 7) ℤ).degreeOf 1 = 2 := by
      rw [degreeOf_sub_left (by simpa only [degreeOf_X_self_pow] using (by omega :
        (C 2 * X 2 ^ 2 : MvPolynomial (Fin 7) ℤ).degreeOf 1 < 2)), degreeOf_X_self_pow]
    dsimp [a]
    rw [degreeOf_sub_left (by simp only [degreeOf_one, h₂]; decide), h₂]
  have hs' : s.degreeOf 1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_sum_le 1 _ _).trans
    apply Finset.sup_le
    intro j _
    have hj : (1 : Fin 7) ≠ squareIndex j := by
      intro h
      have he := congrArg Fin.val h
      dsimp [squareIndex] at he
      omega
    simp only [degreeOf_X_pow_of_ne 2 hj, le_refl]
  have hb' : b.degreeOf 1 = 1 := by
    have h₁ : (X 1 - X 0 ^ 2 : MvPolynomial (Fin 7) ℤ).degreeOf 1 = 1 := by
      rw [degreeOf_sub_left (by
        simp only [degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 7) ≠ 0), degreeOf_X_self]
        decide), degreeOf_X_self]
    dsimp [b]
    rw [degreeOf_sub_left (by rw [hs', h₁]; decide), h₁]
  have ha0 : a ≠ 0 := by
    intro h
    simp only [h, degreeOf_zero] at ha'
    omega
  have ha2 : (a ^ 2).degreeOf 1 = 4 := by
    rw [degreeOf_pow_eq _ _ _ ha0, ha']
  have hb2 : (b ^ 2).degreeOf 1 ≤ 2 := by
    simpa only [hb', mul_one] using degreeOf_pow_le 1 b 2
  have hd : (a ^ 2 + b ^ 2).degreeOf 1 = 4 := by
    rw [degreeOf_add_eq_of_degreeOf_lt (by omega), ha2]
  have hl := degreeOf_le_totalDegree (a ^ 2 + b ^ 2) 1
  have h₁ := totalDegree_pow a 2
  have h₂ := totalDegree_pow b 2
  have h₃ := totalDegree_add (a ^ 2) (b ^ 2)
  change (a ^ 2 + b ^ 2).totalDegree = 4
  omega

end
end Surreal.QuarticConstants

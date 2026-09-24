import Surreal.Algebra.QuarticVariant
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The native squared-bound quartic and its degree

The exact total-degree assertion for `odg:def:eq:F4` in
`odg:def:rem:quarticvariant`. Variable 0 is x, variables 1 and 2 are u
and v, and variables 3 through 6 are the four square witnesses.
-/

namespace Surreal.QuarticVariant

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
    (h : q.degreeOf 0 < p.degreeOf 0) : (p - q).degreeOf 0 = p.degreeOf 0 := by
  rw [sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt (by simpa only [degreeOf_neg] using h)]

/-- The degree is exactly four, with ordinary integer coefficients and no parameters. -/
theorem polynomial_totalDegree : polynomial.totalDegree = 4 := by
  let a : MvPolynomial (Fin 7) ℤ := X 1 ^ 2 - C 2 * X 2 ^ 2 - 1
  let s : MvPolynomial (Fin 7) ℤ := ∑ j : Fin 4, X (squareIndex j) ^ 2
  let b : MvPolynomial (Fin 7) ℤ := X 1 ^ 2 - X 0 ^ 2 - s
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
    have h₁ := totalDegree_sub (X 1 ^ 2 : MvPolynomial (Fin 7) ℤ) (X 0 ^ 2)
    have h₂ := totalDegree_sub (X 1 ^ 2 - X 0 ^ 2 : MvPolynomial (Fin 7) ℤ) s
    simp only [totalDegree_X_pow] at h₁
    dsimp [b]
    omega
  have ha' : a.degreeOf 0 = 0 := by
    have h₁ := degreeOf_mul_le 0 (C 2 : MvPolynomial (Fin 7) ℤ) (X 2 ^ 2)
    have h₂ := degreeOf_sub_le 0 (X 1 ^ 2 : MvPolynomial (Fin 7) ℤ) (C 2 * X 2 ^ 2)
    have h₃ := degreeOf_sub_le 0 (X 1 ^ 2 - C 2 * X 2 ^ 2 : MvPolynomial (Fin 7) ℤ) 1
    simp only [degreeOf_C, degreeOf_one,
      degreeOf_X_pow_of_ne 2 (by decide : (0 : Fin 7) ≠ 1),
      degreeOf_X_pow_of_ne 2 (by decide : (0 : Fin 7) ≠ 2)] at h₁ h₂ h₃
    dsimp [a]
    omega
  have hs' : s.degreeOf 0 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_sum_le 0 _ _).trans
    apply Finset.sup_le
    intro j _
    have hj : (0 : Fin 7) ≠ squareIndex j := by
      intro h
      have he := congrArg Fin.val h
      dsimp [squareIndex] at he
      omega
    simp only [degreeOf_X_pow_of_ne 2 hj, le_refl]
  have hb' : b.degreeOf 0 = 2 := by
    have h₁ : (X 1 ^ 2 - X 0 ^ 2 : MvPolynomial (Fin 7) ℤ).degreeOf 0 = 2 := by
      rw [show (X 1 ^ 2 - X 0 ^ 2 : MvPolynomial (Fin 7) ℤ) =
        -(X 0 ^ 2 - X 1 ^ 2) by ring, degreeOf_neg]
      rw [degreeOf_sub_left (by
        simp only [degreeOf_X_pow_of_ne 2 (by decide : (0 : Fin 7) ≠ 1), degreeOf_X_self_pow]
        decide), degreeOf_X_self_pow]
    dsimp [b]
    rw [degreeOf_sub_left (by rw [hs', h₁]; decide), h₁]
  have hb0 : b ≠ 0 := by
    intro h
    simp only [h, degreeOf_zero] at hb'
    omega
  have hb2 : (b ^ 2).degreeOf 0 = 4 := by
    rw [degreeOf_pow_eq _ _ _ hb0, hb']
  have ha2 : (a ^ 2).degreeOf 0 ≤ 0 := by
    simpa only [ha', mul_zero] using degreeOf_pow_le 0 a 2
  have hd : (a ^ 2 + b ^ 2).degreeOf 0 = 4 := by
    rw [add_comm, degreeOf_add_eq_of_degreeOf_lt (by omega), hb2]
  have hl := degreeOf_le_totalDegree (a ^ 2 + b ^ 2) 0
  have h₁ := totalDegree_pow a 2
  have h₂ := totalDegree_pow b 2
  have h₃ := totalDegree_add (a ^ 2) (b ^ 2)
  change (a ^ 2 + b ^ 2).totalDegree = 4
  omega

end
end Surreal.QuarticVariant

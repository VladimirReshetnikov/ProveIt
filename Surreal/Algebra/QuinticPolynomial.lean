import Surreal.Algebra.QuinticConstants
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# The native quintic polynomial and its exact degree

The total-degree-five assertion in `odg:def:rem:quintic`. Variable 0 is x;
variables 1, 2, 3 are u, v, w; variables 4 through 7 are the four squares.
-/

namespace Surreal.QuinticConstants

open MvPolynomial

noncomputable section

private def squareIndex (j : Fin 4) : Fin 8 := ⟨j.val + 4, by omega⟩

/-- The eight-variable integer polynomial in the source formula. -/
def polynomial : MvPolynomial (Fin 8) ℤ :=
  value (X 0) (X 1) (X 2) (X 3) (fun j => X (squareIndex j))

/-- Its evaluation is exactly the literal quintic value, with no coefficient parameters. -/
theorem eval₂_polynomial {R : Type*} [CommRing R] (a : Fin 8 → R) :
    polynomial.eval₂ (Int.castRingHom R) a =
      value (a 0) (a 1) (a 2) (a 3) (fun j => a ⟨j.val + 4, by omega⟩) := by
  simp [polynomial, value, squareIndex, eval₂_sum]

private theorem degreeOf_sub_left {p q : MvPolynomial (Fin 8) ℤ}
    (h : q.degreeOf 1 < p.degreeOf 1) : (p - q).degreeOf 1 = p.degreeOf 1 := by
  rw [sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt (by simpa only [degreeOf_neg] using h)]

private theorem ne_zero_of_degreeOf {p : MvPolynomial (Fin 8) ℤ} {n : ℕ}
    (hn : 0 < n) (h : p.degreeOf 1 = n) : p ≠ 0 := by
  intro hp
  simp only [hp, degreeOf_zero] at h
  omega

/-- The polynomial has total degree exactly five, not merely at most five. -/
theorem polynomial_totalDegree : polynomial.totalDegree = 5 := by
  let a : MvPolynomial (Fin 8) ℤ := X 1 ^ 2 - C 2 * X 2 ^ 2 - 1
  let b : MvPolynomial (Fin 8) ℤ := X 2 - X 0 * X 3
  let s : MvPolynomial (Fin 8) ℤ := ∑ j : Fin 4, X (squareIndex j) ^ 2
  let c : MvPolynomial (Fin 8) ℤ := X 1 - C 2 - s
  have ha : a.totalDegree ≤ 2 := by
    have h₁ := totalDegree_mul (C 2 : MvPolynomial (Fin 8) ℤ) (X 2 ^ 2)
    have h₂ := totalDegree_sub (X 1 ^ 2 : MvPolynomial (Fin 8) ℤ) (C 2 * X 2 ^ 2)
    have h₃ := totalDegree_sub (X 1 ^ 2 - C 2 * X 2 ^ 2 : MvPolynomial (Fin 8) ℤ) 1
    simp only [totalDegree_C, totalDegree_X_pow, totalDegree_one, zero_add] at h₁ h₂ h₃
    dsimp [a]
    omega
  have hb : b.totalDegree ≤ 2 := by
    have h₁ := totalDegree_mul (X 0 : MvPolynomial (Fin 8) ℤ) (X 3)
    have h₂ := totalDegree_sub (X 2 : MvPolynomial (Fin 8) ℤ) (X 0 * X 3)
    simp only [totalDegree_X] at h₁ h₂
    dsimp [b]
    omega
  have hs : s.totalDegree ≤ 2 := by
    apply totalDegree_finsetSum_le
    intro j _
    simp only [totalDegree_X_pow, le_refl]
  have hc : c.totalDegree ≤ 2 := by
    have h₁ := totalDegree_sub (X 1 : MvPolynomial (Fin 8) ℤ) (C 2)
    have h₂ := totalDegree_sub (X 1 - C 2 : MvPolynomial (Fin 8) ℤ) s
    simp only [totalDegree_X, totalDegree_C] at h₁
    dsimp [c]
    omega
  have ha' : a.degreeOf 1 = 2 := by
    have h₁ := degreeOf_mul_le 1 (C 2 : MvPolynomial (Fin 8) ℤ) (X 2 ^ 2)
    simp only [degreeOf_C, degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 8) ≠ 2), zero_add] at h₁
    have h₂ : (X 1 ^ 2 - C 2 * X 2 ^ 2 : MvPolynomial (Fin 8) ℤ).degreeOf 1 = 2 := by
      rw [degreeOf_sub_left (by simpa only [degreeOf_X_self_pow] using (by omega :
        (C 2 * X 2 ^ 2 : MvPolynomial (Fin 8) ℤ).degreeOf 1 < 2)), degreeOf_X_self_pow]
    dsimp [a]
    rw [degreeOf_sub_left (by simp only [degreeOf_one, h₂]; decide), h₂]
  have hb' : b.degreeOf 1 = 0 := by
    have h₁ := degreeOf_mul_le 1 (X 0 : MvPolynomial (Fin 8) ℤ) (X 3)
    have h₂ := degreeOf_sub_le 1 (X 2 : MvPolynomial (Fin 8) ℤ) (X 0 * X 3)
    simp only [degreeOf_X_of_ne (by decide : (1 : Fin 8) ≠ 0),
      degreeOf_X_of_ne (by decide : (1 : Fin 8) ≠ 3),
      degreeOf_X_of_ne (by decide : (1 : Fin 8) ≠ 2)] at h₁ h₂
    dsimp [b]
    omega
  have hs' : s.degreeOf 1 = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (degreeOf_sum_le 1 _ _).trans
    apply Finset.sup_le
    intro j _
    have hj : (1 : Fin 8) ≠ squareIndex j := by
      intro h
      have he := congrArg Fin.val h
      dsimp [squareIndex] at he
      omega
    simp only [degreeOf_X_pow_of_ne 2 hj, le_refl]
  have hc' : c.degreeOf 1 = 1 := by
    have h₁ : (X 1 - C 2 : MvPolynomial (Fin 8) ℤ).degreeOf 1 = 1 := by
      rw [degreeOf_sub_left (by simp only [degreeOf_C, degreeOf_X_self]; decide), degreeOf_X_self]
    dsimp [c]
    rw [degreeOf_sub_left (by rw [hs', h₁]; decide), h₁]
  have ha2 : (a ^ 2).degreeOf 1 = 4 := by
    rw [degreeOf_pow_eq _ _ _ (ne_zero_of_degreeOf (by decide) ha'), ha']
  have hb2 : (b ^ 2).degreeOf 1 ≤ 0 := by
    simpa only [hb', mul_zero] using degreeOf_pow_le 1 b 2
  have hc2 : (c ^ 2).degreeOf 1 ≤ 2 := by
    simpa only [hc', mul_one] using degreeOf_pow_le 1 c 2
  have hd : (a ^ 2 + b ^ 2 + c ^ 2).degreeOf 1 = 4 := by
    have h₁ : (a ^ 2 + b ^ 2).degreeOf 1 = 4 := by
      rw [degreeOf_add_eq_of_degreeOf_lt (by omega), ha2]
    rw [degreeOf_add_eq_of_degreeOf_lt (by omega), h₁]
  have ht : (a ^ 2 + b ^ 2 + c ^ 2).totalDegree = 4 := by
    have hl := degreeOf_le_totalDegree (a ^ 2 + b ^ 2 + c ^ 2) 1
    have h₁ := totalDegree_pow a 2
    have h₂ := totalDegree_pow b 2
    have h₃ := totalDegree_pow c 2
    have h₄ := totalDegree_add (a ^ 2) (b ^ 2)
    have h₅ := totalDegree_add (a ^ 2 + b ^ 2) (c ^ 2)
    omega
  change (X 0 * (a ^ 2 + b ^ 2 + c ^ 2)).totalDegree = 5
  rw [totalDegree_mul_of_isDomain (X_ne_zero _) (ne_zero_of_degreeOf (by decide) hd),
    totalDegree_X, ht]

end
end Surreal.QuinticConstants

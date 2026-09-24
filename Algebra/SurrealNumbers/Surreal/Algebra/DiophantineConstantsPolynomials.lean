import Surreal.Algebra.DiophantineConstants
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Native polynomials and exact degrees of the constant-definition system

The degree and witness-count clauses of `odg:def:thm:constants`.
Variable 0 is the tested element; variables 1 through 5 are u, v, w, s, t.
The three integer polynomials have total degrees exactly 3, 3, and 7.
-/

namespace Surreal.DiophantineConstants

open MvPolynomial

noncomputable section

/-- The Pell equation, including the guard admitting x = 0. -/
def pellEquation : MvPolynomial (Fin 6) ℤ := X 0 * (X 1 ^ 2 - C 2 * X 2 ^ 2 - 1)

/-- Divisibility of the Pell coordinate by the tested element. -/
def divisibilityEquation : MvPolynomial (Fin 6) ℤ := X 0 * (X 2 - X 0 * X 3)

/-- The intersective-polynomial certificate excluding a zero Pell coordinate. -/
def certificateEquation : MvPolynomial (Fin 6) ℤ :=
  X 0 * (X 2 * X 4 - IntersectivePolynomial.value (X 5))

/-- The native polynomial evaluations are precisely the literal three equations. -/
theorem system_iff_polynomial_evaluations {R : Type*} [CommRing R] (x u v w s t : R) :
    System x u v w s t ↔
      pellEquation.eval₂ (Int.castRingHom R) ![x, u, v, w, s, t] = 0 ∧
      divisibilityEquation.eval₂ (Int.castRingHom R) ![x, u, v, w, s, t] = 0 ∧
      certificateEquation.eval₂ (Int.castRingHom R) ![x, u, v, w, s, t] = 0 := by
  simp [System, pellEquation, divisibilityEquation, certificateEquation, IntersectivePolynomial.value]

private theorem ne_zero_of_degree {p : MvPolynomial (Fin 6) ℤ} {n : ℕ}
    (hn : 0 < n) (h : p.totalDegree = n) : p ≠ 0 := by
  intro hp
  simp only [hp, totalDegree_zero] at h
  omega

private theorem degree_sub_right {p q : MvPolynomial (Fin 6) ℤ}
    (h : p.totalDegree < q.totalDegree) : (p - q).totalDegree = q.totalDegree := by
  rw [sub_eq_add_neg, totalDegree_add_eq_right_of_totalDegree_lt (by simpa using h), totalDegree_neg]

private theorem degree_sub_left {p q : MvPolynomial (Fin 6) ℤ}
    (h : q.totalDegree < p.totalDegree) : (p - q).totalDegree = p.totalDegree := by
  rw [sub_eq_add_neg, totalDegree_add_eq_left_of_totalDegree_lt (by simpa using h)]

private theorem quadratic_degree (i : Fin 6) (d : ℤ) :
    (X i ^ 2 - C d : MvPolynomial (Fin 6) ℤ).totalDegree = 2 := by
  rw [degree_sub_left (by simp only [totalDegree_C, totalDegree_X_pow]; decide), totalDegree_X_pow]

/-- The first equation has total degree exactly three. -/
theorem pellEquation_totalDegree : pellEquation.totalDegree = 3 := by
  let p : MvPolynomial (Fin 6) ℤ := X 1 ^ 2 - C 2 * X 2 ^ 2 - 1
  have hc : p.coeff (Finsupp.single 1 2) = 1 := by
    have hn : (0 : Fin 6 →₀ ℕ) ≠ Finsupp.single 1 2 := by
      intro h
      have h := congrArg (fun f : Fin 6 →₀ ℕ => f 1) h
      norm_num at h
    simp only [p, coeff_sub, coeff_C_mul, coeff_single_X_pow, coeff_one, if_neg hn]
    norm_num
    decide
  have hl : 2 ≤ p.totalDegree := by
    have h := le_totalDegree (mem_support_iff.mpr (show p.coeff (Finsupp.single 1 2) ≠ 0 by omega))
    simpa using h
  have hu : p.totalDegree ≤ 2 := by
    have hmul := totalDegree_mul (C (2 : ℤ) : MvPolynomial (Fin 6) ℤ) (X 2 ^ 2)
    have hsub := totalDegree_sub (X 1 ^ 2 : MvPolynomial (Fin 6) ℤ) (C 2 * X 2 ^ 2)
    have hsub' := totalDegree_sub (X 1 ^ 2 - C 2 * X 2 ^ 2 : MvPolynomial (Fin 6) ℤ) 1
    simp only [totalDegree_C, totalDegree_X_pow, zero_add, totalDegree_one] at hmul hsub hsub'
    dsimp [p]
    omega
  have hd : p.totalDegree = 2 := le_antisymm hu hl
  change (X 0 * p).totalDegree = 3
  rw [totalDegree_mul_of_isDomain (X_ne_zero _) (ne_zero_of_degree (by decide) hd), totalDegree_X, hd]

/-- The second equation also has total degree exactly three. -/
theorem divisibilityEquation_totalDegree : divisibilityEquation.totalDegree = 3 := by
  have hm : (X 0 * X 3 : MvPolynomial (Fin 6) ℤ).totalDegree = 2 := by
    rw [totalDegree_mul_of_isDomain (X_ne_zero _) (X_ne_zero _)]
    simp
  have hd : (X 2 - X 0 * X 3 : MvPolynomial (Fin 6) ℤ).totalDegree = 2 := by
    rw [degree_sub_right (by simp [hm]), hm]
  rw [divisibilityEquation, totalDegree_mul_of_isDomain (X_ne_zero _)
    (ne_zero_of_degree (by decide) hd), totalDegree_X, hd]

/-- The final certificate equation has total degree exactly seven. -/
theorem certificateEquation_totalDegree : certificateEquation.totalDegree = 7 := by
  have h13 := quadratic_degree 5 13
  have h17 := quadratic_degree 5 17
  have h221 := quadratic_degree 5 221
  have hmul : ((X 5 ^ 2 - C 13) * (X 5 ^ 2 - C 17) : MvPolynomial (Fin 6) ℤ).totalDegree = 4 := by
    rw [totalDegree_mul_of_isDomain (ne_zero_of_degree (by decide) h13)
      (ne_zero_of_degree (by decide) h17), h13, h17]
  have hv : (IntersectivePolynomial.value (X 5) : MvPolynomial (Fin 6) ℤ).totalDegree = 6 := by
    change (((X 5 ^ 2 - C 13) * (X 5 ^ 2 - C 17)) * (X 5 ^ 2 - C 221) :
      MvPolynomial (Fin 6) ℤ).totalDegree = 6
    rw [totalDegree_mul_of_isDomain (ne_zero_of_degree (by decide) hmul)
      (ne_zero_of_degree (by decide) h221), hmul, h221]
  have hsmall : (X 2 * X 4 : MvPolynomial (Fin 6) ℤ).totalDegree = 2 := by
    rw [totalDegree_mul_of_isDomain (X_ne_zero _) (X_ne_zero _)]
    simp
  have hd : (X 2 * X 4 - IntersectivePolynomial.value (X 5) :
      MvPolynomial (Fin 6) ℤ).totalDegree = 6 := by
    rw [degree_sub_right (by omega), hv]
  rw [certificateEquation, totalDegree_mul_of_isDomain (X_ne_zero _)
    (ne_zero_of_degree (by decide) hd), totalDegree_X, hd]

end
end Surreal.DiophantineConstants

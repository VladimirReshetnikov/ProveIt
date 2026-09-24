import Mathlib.Algebra.MvPolynomial.Expand
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Polynomials invariant under independent changes of sign

A polynomial over a characteristic-zero integral domain is a polynomial in
the squares of its variables exactly when changing the sign of any one
variable leaves it unchanged. The variable type need not be finite.

This is the algebraic step that removes the formal radicals from the signed
products in the Matiyasevich--Robinson relation-combining construction. This
module proves only the algebraic statement, with no arithmetic representation
theorem assumed.
-/

namespace Diophantine

open MvPolynomial

noncomputable section

variable {σ R : Type*} [CommRing R]

/-- Negate the selected variable, fixing the other variables and coefficients. -/
def signFlip (i : σ) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R := by
  classical
  exact bind₁ (fun j => if j = i then -X j else X j)

@[simp]
theorem signFlip_X [DecidableEq σ] (i j : σ) :
    signFlip (R := R) i (X j) = if j = i then -X j else X j := by
  classical
  simp [signFlip]

@[simp]
theorem signFlip_C (i : σ) (r : R) : signFlip i (C r) = C r := by
  simp [signFlip]

/-- The sign acquired by a monomial is determined by the selected exponent. -/
theorem signFlip_monomial (i : σ) (d : σ →₀ ℕ) (r : R) :
    signFlip i (monomial d r) = monomial d ((-1 : R) ^ d i * r) := by
  classical
  let s : σ → R := fun j => if j = i then -1 else 1
  have hs (j : σ) : (if j = i then -X j else X j : MvPolynomial σ R) =
      C (s j) * X j := by
    by_cases hji : j = i <;> simp [s, hji]
  have hprod : (∏ j ∈ d.support, s j ^ d j) = (-1 : R) ^ d i := by
    change d.prod (fun j n => s j ^ n) = _
    have heq : d.prod (fun j n => s j ^ n) =
        d.prod (fun j n => if j = i then (-1 : R) ^ n else 1) := by
      apply Finsupp.prod_congr
      intro j hj
      by_cases hji : j = i <;> simp [s, hji]
    rw [heq, Finsupp.prod_ite_eq']
    by_cases hi : i ∈ d.support
    · simp [hi]
    · have hdi : d i = 0 := by simpa using hi
      simp [hi, hdi]
  calc
    signFlip i (monomial d r) =
        C r * ∏ j ∈ d.support, (C (s j) * X j) ^ d j := by
      rw [signFlip, bind₁_monomial]
      simp_rw [hs]
    _ = C r * (C (∏ j ∈ d.support, s j ^ d j) *
        ∏ j ∈ d.support, (X j : MvPolynomial σ R) ^ d j) := by
      simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]
    _ = monomial d ((-1 : R) ^ d i * r) := by
      rw [hprod, monomial_eq, map_mul]
      dsimp [Finsupp.prod]
      ring

/-- Coefficients are multiplied by the parity sign of the selected exponent. -/
theorem coeff_signFlip (i : σ) (p : MvPolynomial σ R) (d : σ →₀ ℕ) :
    (signFlip i p).coeff d = (-1 : R) ^ d i * p.coeff d := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial e r =>
      by_cases he : e = d
      · subst e
        simp [signFlip_monomial]
      · simp [signFlip_monomial, he]
  | add p q hp hq =>
      simp only [map_add, coeff_add, hp, hq, mul_add]

/-- Expansion by two is invariant under any independent change of sign. -/
@[simp]
theorem signFlip_expand_two (i : σ) (p : MvPolynomial σ R) :
    signFlip i (expand 2 p) = expand 2 p := by
  classical
  have hhom : (signFlip (R := R) i).comp (expand 2) = expand 2 := by
    ext1 j
    by_cases hji : j = i <;> simp [hji]
  exact DFunLike.congr_fun hhom p

/-- Halve every exponent of every supported monomial. This reconstructs a
polynomial in the original variables from a polynomial in their squares. -/
def halveExponents (p : MvPolynomial σ R) : MvPolynomial σ R :=
  ∑ d ∈ p.support,
    monomial (d.mapRange (fun n => n / 2) (by decide)) (p.coeff d)

/-- A polynomial whose supported exponents are even is an expansion by two. -/
theorem expand_two_halveExponents (p : MvPolynomial σ R)
    (h : ∀ d ∈ p.support, ∀ i, 2 ∣ d i) :
    expand 2 (halveExponents p) = p := by
  classical
  have hhalf (d : σ →₀ ℕ) (hd : d ∈ p.support) :
      2 • d.mapRange (fun n => n / 2) (by decide) = d := by
    ext i
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    obtain ⟨k, hk⟩ := h d hd i
    omega
  calc
    expand 2 (halveExponents p) =
        ∑ d ∈ p.support,
          monomial (2 • d.mapRange (fun n => n / 2) (by decide)) (p.coeff d) := by
      simp only [halveExponents, map_sum, expand_monomial]
    _ = ∑ d ∈ p.support, monomial d (p.coeff d) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hhalf d hd]
    _ = p := p.as_sum.symm

variable [IsDomain R] [CharZero R]

/-- Sign invariance excludes every coefficient having an odd exponent. -/
theorem coeff_eq_zero_of_signFlip_invariant (p : MvPolynomial σ R)
    (h : ∀ i, signFlip i p = p) (d : σ →₀ ℕ) (i : σ)
    (hodd : ¬ 2 ∣ d i) : p.coeff d = 0 := by
  have heven : ¬ Even (d i) := fun hi => hodd hi.two_dvd
  have hcoeff : -(p.coeff d) = p.coeff d := by
    have hh := congrArg (fun q : MvPolynomial σ R => q.coeff d) (h i)
    simpa only [coeff_signFlip, neg_one_pow_eq_ite, if_neg heven,
      neg_one_mul] using hh
  have hzero : (2 : R) * p.coeff d = 0 := by
    rw [two_mul]
    calc
      p.coeff d + p.coeff d = p.coeff d + -(p.coeff d) :=
        congrArg (fun r : R => p.coeff d + r) hcoeff.symm
      _ = 0 := add_neg_cancel _
  exact (mul_eq_zero.mp hzero).resolve_left two_ne_zero

/-- Every supported exponent of a sign-invariant polynomial is even. -/
theorem two_dvd_exponent_of_signFlip_invariant (p : MvPolynomial σ R)
    (h : ∀ i, signFlip i p = p) (d : σ →₀ ℕ) (hd : d ∈ p.support) (i : σ) :
    2 ∣ d i := by
  by_contra hi
  exact (MvPolynomial.mem_support_iff.mp hd)
    (coeff_eq_zero_of_signFlip_invariant p h d i hi)

/-- Explicitly recover the polynomial in squares from independent sign invariance. -/
theorem expand_two_halveExponents_of_signFlip_invariant (p : MvPolynomial σ R)
    (h : ∀ i, signFlip i p = p) : expand 2 (halveExponents p) = p :=
  expand_two_halveExponents p (two_dvd_exponent_of_signFlip_invariant p h)

/-- Independent changes of sign characterize the image of expansion by two. -/
theorem signFlip_invariant_iff_exists_expand_two (p : MvPolynomial σ R) :
    (∀ i, signFlip i p = p) ↔ ∃ q : MvPolynomial σ R, expand 2 q = p := by
  constructor
  · intro hp
    exact ⟨halveExponents p, expand_two_halveExponents_of_signFlip_invariant p hp⟩
  · rintro ⟨q, rfl⟩ i
    exact signFlip_expand_two i q

end

end Diophantine

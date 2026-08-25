import FabiusFunction.FabiusSaddlePolynomialCoefficients
import FabiusFunction.FabiusSaddleJetClosedForm

/-!
# Closed form for the saddle exponent coefficients

`FabiusSaddleCoefficientRecurrence` defines the coefficient of `epsilon ^ m`
in the central saddle exponent, `epsilon = lambda ^ (-1/2)`, as

`E m t v = I^m * d (m-1) t * v^m / m !
            + I^(m+2) * s (m+1) * v^(m+2) / (m+2)!`,

where `d` is the bounded exponent jet and `s n = (-1)^(n+1) * n !` is the jet
slope.  The second summand still carries two factorials and a separate power of
`I`.  Both cancel: `I^(m+2) = -I^m`, `s (m+1) = (-1)^m * (m+1)!` and
`(m+1)! / (m+2)! = 1 / (m+2)`, so

`E m t v = I^m * (d (m-1) t * v^m / m ! + (-1)^(m+1) * v^(m+2) / (m+2))`.

Only one power of `I` remains, and the second summand is the universal, jet-free
tail `(-1)^(m+1) v^(m+2) / (m+2)`.  This is the shape in which the exponent
enters every downstream computation: after the Gaussian contraction the powers
of `I` recombine into the real coefficients of the expansion, and the jet-free
tail is what produces the pure rational numbers in them.

Combined with `negativeLaplaceBoundedExponentJet_eq_closedForm`, this makes the
saddle exponent completely explicit: for every order `m`, the coefficient of
`epsilon ^ m` is `I ^ m` times a polynomial in the Gaussian variable whose two
nonzero coefficients are a rational number and a finite rational combination of
`1 / log 2` and the normalized derivatives `Psi', …, Psi^(m)`.
-/

set_option autoImplicit false

open Complex Polynomial

namespace Fabius

noncomputable section

/-- The scalar coefficient of the jet-free tail, with its factorials and its
extra power of `I` cancelled.  This is the form in which the tail occurs inside
`negativeLaplaceExponentPolynomial`, where the division sits inside the
polynomial coefficient. -/
private theorem exponentTail_coeff (n : ℕ) :
    I ^ (n + 3) * ((negativeLaplaceJetSlope (n + 2) : ℝ) : ℂ) /
        (((n + 3).factorial : ℕ) : ℂ) =
      I ^ (n + 1) * ((-1 : ℂ) ^ n / ((n : ℂ) + 3)) := by
  have hfac : (((n + 2).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (n + 2)).ne'
  have hn3 : ((n : ℂ) + 3) ≠ 0 := by
    have h : ((n + 3 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa using h
  have hI : (I : ℂ) ^ (n + 3) = -(I ^ (n + 1)) := by
    rw [show n + 3 = (n + 1) + 2 by omega, pow_add, Complex.I_sq]
    ring
  have hsign : ((-1 : ℂ)) ^ (n + 2 + 1) = -((-1 : ℂ) ^ n) := by
    rw [show n + 2 + 1 = n + 3 by omega, pow_add,
      show ((-1 : ℂ)) ^ 3 = -1 by norm_num]
    ring
  rw [show (n + 3).factorial = (n + 3) * (n + 2).factorial from
    Nat.factorial_succ (n + 2)]
  unfold negativeLaplaceJetSlope
  rw [hI]
  push_cast
  rw [hsign]
  field_simp

/-- The same cancellation in the association used by
`negativeLaplaceExponentCoefficient`, where the division sits outermost. -/
private theorem exponentTail_identity (n : ℕ) (z : ℂ) :
    I ^ (n + 3) * ((negativeLaplaceJetSlope (n + 2) : ℝ) : ℂ) *
        z ^ (n + 3) / (((n + 3).factorial : ℕ) : ℂ) =
      I ^ (n + 1) * ((-1 : ℂ) ^ n * z ^ (n + 3) / ((n : ℂ) + 3)) := by
  rw [show I ^ (n + 3) * ((negativeLaplaceJetSlope (n + 2) : ℝ) : ℂ) *
        z ^ (n + 3) / (((n + 3).factorial : ℕ) : ℂ) =
      I ^ (n + 3) * ((negativeLaplaceJetSlope (n + 2) : ℝ) : ℂ) /
        (((n + 3).factorial : ℕ) : ℂ) * z ^ (n + 3) by ring,
    exponentTail_coeff n]
  ring

/-- Closed form of the scalar saddle exponent coefficient: one power of `I`
multiplying a jet term and a universal jet-free tail. -/
theorem negativeLaplaceExponentCoefficient_succ_eq (n : ℕ) (t v : ℝ) :
    negativeLaplaceExponentCoefficient (n + 1) t v =
      I ^ (n + 1) *
        ((negativeLaplaceBoundedExponentJet n t : ℂ) * (v : ℂ) ^ (n + 1) /
            (((n + 1).factorial : ℕ) : ℂ) +
          (-1 : ℂ) ^ n * (v : ℂ) ^ (n + 3) / ((n : ℂ) + 3)) := by
  simp only [negativeLaplaceExponentCoefficient]
  rw [exponentTail_identity n (v : ℂ)]
  ring

/-- Closed form of the saddle exponent polynomial. -/
theorem negativeLaplaceExponentPolynomial_succ_eq (n : ℕ) (t : ℝ) :
    negativeLaplaceExponentPolynomial (n + 1) t =
      C (I ^ (n + 1)) *
        (C ((negativeLaplaceBoundedExponentJet n t : ℂ) /
              (((n + 1).factorial : ℕ) : ℂ)) * X ^ (n + 1) +
          C ((-1 : ℂ) ^ n / ((n : ℂ) + 3)) * X ^ (n + 3)) := by
  apply Polynomial.funext
  intro z
  simp only [negativeLaplaceExponentPolynomial, eval_add, eval_mul, eval_C,
    eval_X, eval_pow]
  rw [exponentTail_coeff n]
  ring

/-- The tail of the exponent coefficient does not see the periodic correction:
it is the same at every argument `t`.  It does depend on the order `m`, being
`(-1)^(m+1) v^(m+2) / (m+2)`; what is uniform is its independence of the jets,
not the monomial itself. -/
theorem negativeLaplaceExponentCoefficient_tail_indep (n : ℕ) (t u v : ℝ) :
    negativeLaplaceExponentCoefficient (n + 1) t v -
        negativeLaplaceExponentCoefficient (n + 1) u v =
      I ^ (n + 1) *
        ((negativeLaplaceBoundedExponentJet n t : ℂ) -
            (negativeLaplaceBoundedExponentJet n u : ℂ)) *
          (v : ℂ) ^ (n + 1) / (((n + 1).factorial : ℕ) : ℂ) := by
  rw [negativeLaplaceExponentCoefficient_succ_eq n t v,
    negativeLaplaceExponentCoefficient_succ_eq n u v]
  ring

end

end Fabius

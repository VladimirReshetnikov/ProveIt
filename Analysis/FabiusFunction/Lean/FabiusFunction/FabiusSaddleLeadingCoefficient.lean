import FabiusFunction.FabiusSaddleExpansionCoefficients
import FabiusFunction.FabiusSaddleExponentClosedForm

/-!
# The leading coefficient of every saddle mass coefficient

The mass coefficient of order `lambda⁻ʲ` is a polynomial in the bounded
exponent jets `d 0, …, d (2*j-1)`, and the last of those, `d (2*j-1)`, is the
only source of the `(2*j)`-nd derivative of the periodic correction.  This
module shows that the coefficient of `d (2*j-1)` is exactly

`(-1)^j / (2^j * j !)`,

for every `j`, so the highest-derivative term of the `j`-th coefficient of the
small-argument expansion is `(-1)^j Psi^(2j) / (2^j * j ! * (log 2)^(2j))`.

Two elementary facts do all the work.

*The exponential recurrence is affine in its top exponent coefficient.*  Because
the `j = n` summand of `expCoeff E (n+1)` is `(n+1) * E (n+1) * expCoeff E 0`
and `expCoeff E 0 = 1`, the difference `expCoeff E (n+1) - E (n+1)` depends on
`E` only through `E 0, …, E n`.  That is `expCoeff_sub_self_congr`.

*Only one monomial of the top exponent polynomial carries a jet.*  By
`negativeLaplaceExponentPolynomial_succ_eq` the order-`m` exponent polynomial is
`I^m` times `d (m-1) * X^m / m ! + (-1)^(m+1) * X^(m+2) / (m+2)`, whose second
summand is jet-free.  So changing `d (2*j-1)` alone changes the order-`2*j`
exponent polynomial by a single monomial `C (I^(2j) * delta / (2j)!) * X^(2j)`,
and the Gaussian contraction of `X^(2j)` is `(2j-1)!!`.  Since
`(2j)! = (2j)!! * (2j-1)!! = 2^j * j ! * (2j-1)!!`, the double factorials cancel
and `I^(2j) = (-1)^j` supplies the sign.

The statement is made about an arbitrary jet sequence, because "the coefficient
of `d (2*j-1)`" is not expressible about a single fixed family; the Fabius case
is recovered by `fabiusSaddleMassCoefficientComplex_eq_saddleJet`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius.SaddleExpansion

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The exponential recurrence, with its top term separated off. -/
theorem expCoeff_succ_eq_add (E : ℕ → R) (n : ℕ) :
    expCoeff E (n + 1) =
      E (n + 1) +
        ((n + 1 : ℚ)⁻¹) • (∑ j ∈ Finset.range n,
          ((j : R) + 1) * E (j + 1) * expCoeff E (n - j)) := by
  have hscalar : ((n + 1 : ℚ)⁻¹) •
      (((n : R) + 1) * E (n + 1) * expCoeff E 0) = E (n + 1) := by
    rw [expCoeff_zero, mul_one,
      show ((n : R) + 1) = algebraMap ℚ R (n + 1 : ℚ) by norm_num,
      Algebra.smul_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀, map_one,
      one_mul]
    exact_mod_cast Nat.succ_ne_zero n
  rw [expCoeff_succ, Finset.sum_range_succ, Nat.sub_self, smul_add, hscalar]
  exact add_comm _ _

/-- **The exponential recurrence is affine in its top exponent coefficient.**
The difference `expCoeff E (n+1) - E (n+1)` sees only `E 0, …, E n`. -/
theorem expCoeff_sub_self_congr {E F : ℕ → R} (n : ℕ)
    (h : ∀ j, j ≤ n → E j = F j) :
    expCoeff E (n + 1) - E (n + 1) = expCoeff F (n + 1) - F (n + 1) := by
  rw [expCoeff_succ_eq_add E n, expCoeff_succ_eq_add F n,
    add_sub_cancel_left, add_sub_cancel_left]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < n := Finset.mem_range.1 hj
  rw [h (j + 1) (by omega),
    expCoeff_congr (n - j) (fun k hk => h k (by omega))]

end

end Fabius.SaddleExpansion

namespace Fabius

open Complex Polynomial SaddleExpansion

noncomputable section

/-- The saddle exponent polynomials attached to an arbitrary sequence of jets.
At the Fabius jets this is `negativeLaplaceExponentPolynomial`. -/
def saddleJetExponentPolynomial (d : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 0
  | n + 1 =>
      C (I ^ (n + 1) * d n / (((n + 1).factorial : ℕ) : ℂ)) * X ^ (n + 1) +
        C (I ^ (n + 1) * (-1 : ℂ) ^ n / ((n : ℂ) + 3)) * X ^ (n + 3)

@[simp] theorem saddleJetExponentPolynomial_zero (d : ℕ → ℂ) :
    saddleJetExponentPolynomial d 0 = 0 := rfl

/-- One step of the exponent family. -/
theorem saddleJetExponentPolynomial_succ (d : ℕ → ℂ) (n : ℕ) :
    saddleJetExponentPolynomial d (n + 1) =
      C (I ^ (n + 1) * d n / (((n + 1).factorial : ℕ) : ℂ)) * X ^ (n + 1) +
        C (I ^ (n + 1) * (-1 : ℂ) ^ n / ((n : ℂ) + 3)) * X ^ (n + 3) := rfl

/-- Two jet sequences agreeing below an index give the same exponent
polynomials up to that index. -/
theorem saddleJetExponentPolynomial_congr {d e : ℕ → ℂ} (N : ℕ)
    (h : ∀ m, m < N → d m = e m) :
    ∀ k, k ≤ N → saddleJetExponentPolynomial d k =
      saddleJetExponentPolynomial e k := by
  intro k hk
  cases k with
  | zero => rfl
  | succ n =>
      rw [saddleJetExponentPolynomial_succ, saddleJetExponentPolynomial_succ,
        h n (by omega)]

/-- Changing one jet changes one monomial of the corresponding exponent
polynomial.  The jet-free tail cancels. -/
theorem saddleJetExponentPolynomial_succ_sub (d e : ℕ → ℂ) (n : ℕ) :
    saddleJetExponentPolynomial d (n + 1) -
        saddleJetExponentPolynomial e (n + 1) =
      C (I ^ (n + 1) * (d n - e n) / (((n + 1).factorial : ℕ) : ℂ)) *
        X ^ (n + 1) := by
  rw [saddleJetExponentPolynomial_succ, saddleJetExponentPolynomial_succ]
  apply Polynomial.funext
  intro z
  simp only [eval_sub, eval_add, eval_mul, eval_C, eval_X, eval_pow]
  ring

/-- At the Fabius jets, the generic exponent family is the concrete one. -/
theorem saddleJetExponentPolynomial_eq_negativeLaplace (t : ℝ) (m : ℕ) :
    saddleJetExponentPolynomial
        (fun n => (negativeLaplaceBoundedExponentJet n t : ℂ)) m =
      negativeLaplaceExponentPolynomial m t := by
  cases m with
  | zero => rw [saddleJetExponentPolynomial_zero,
      negativeLaplaceExponentPolynomial_zero]
  | succ n =>
      rw [saddleJetExponentPolynomial_succ,
        negativeLaplaceExponentPolynomial_succ_eq]
      apply Polynomial.funext
      intro z
      simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
      ring

/-- The Gaussian mass coefficient of an arbitrary jet sequence. -/
def saddleJetMassCoefficient (d : ℕ → ℂ) (j : ℕ) : ℂ :=
  gaussianPolynomialContraction (expCoeff (saddleJetExponentPolynomial d) (2 * j))

/-- At the Fabius jets, the generic mass coefficient is the concrete one. -/
theorem fabiusSaddleMassCoefficientComplex_eq_saddleJet (t : ℝ) (j : ℕ) :
    fabiusSaddleMassCoefficientComplex j t =
      saddleJetMassCoefficient
        (fun n => (negativeLaplaceBoundedExponentJet n t : ℂ)) j := by
  unfold fabiusSaddleMassCoefficientComplex saddleJetMassCoefficient
  congr 1
  apply expCoeff_congr (2 * j)
  intro m _hm
  exact (saddleJetExponentPolynomial_eq_negativeLaplace t m).symm

/-- The normalized Gaussian moment of order `2 * (j+1)` divided by
`(2 * (j+1))!` is `1 / (2 ^ (j+1) * (j+1)!)`: the odd double factorials
cancel. -/
theorem normalizedGaussianMoment_div_factorial (j : ℕ) :
    normalizedGaussianMoment (2 * (j + 1)) /
        (((2 * (j + 1)).factorial : ℕ) : ℂ) =
      1 / ((2 : ℂ) ^ (j + 1) * (((j + 1).factorial : ℕ) : ℂ)) := by
  have hoddC : ((Nat.doubleFactorial (2 * j + 1) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos (2 * j + 1)).ne'
  have hfacC : (((j + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (j + 1)).ne'
  have hfac : (2 * (j + 1)).factorial =
      2 ^ (j + 1) * (j + 1).factorial * Nat.doubleFactorial (2 * j + 1) := by
    have h1 : (2 * (j + 1)).factorial =
        Nat.doubleFactorial (2 * (j + 1)) *
          Nat.doubleFactorial (2 * j + 1) := by
      have h2 := Nat.factorial_eq_mul_doubleFactorial (2 * j + 1)
      simpa [show 2 * j + 1 + 1 = 2 * (j + 1) by ring] using h2
    rw [h1, Nat.doubleFactorial_two_mul]
  rw [normalizedGaussianMoment_even,
    show 2 * (j + 1) - 1 = 2 * j + 1 by omega, hfac]
  push_cast
  field_simp

/-- **The coefficient of the top jet in the mass coefficient of order `j+1` is
`(-1)^(j+1) / (2^(j+1) * (j+1)!)`.**  The two jet sequences are required to
agree below index `2*j+1`, so the only difference is in the top jet. -/
theorem saddleJetMassCoefficient_succ_sub (j : ℕ) (d e : ℕ → ℂ)
    (h : ∀ m, m < 2 * j + 1 → d m = e m) :
    saddleJetMassCoefficient d (j + 1) - saddleJetMassCoefficient e (j + 1) =
      (-1 : ℂ) ^ (j + 1) / ((2 : ℂ) ^ (j + 1) * (((j + 1).factorial : ℕ) : ℂ)) *
        (d (2 * j + 1) - e (2 * j + 1)) := by
  have hlow : ∀ k, k ≤ 2 * j + 1 →
      saddleJetExponentPolynomial d k = saddleJetExponentPolynomial e k :=
    saddleJetExponentPolynomial_congr (2 * j + 1) h
  have haffine := expCoeff_sub_self_congr
    (E := saddleJetExponentPolynomial d) (F := saddleJetExponentPolynomial e)
    (2 * j + 1) hlow
  have hexp :
      expCoeff (saddleJetExponentPolynomial d) (2 * j + 1 + 1) -
          expCoeff (saddleJetExponentPolynomial e) (2 * j + 1 + 1) =
        C (I ^ (2 * j + 1 + 1) * (d (2 * j + 1) - e (2 * j + 1)) /
            (((2 * j + 1 + 1).factorial : ℕ) : ℂ)) * X ^ (2 * j + 1 + 1) := by
    rw [← saddleJetExponentPolynomial_succ_sub d e (2 * j + 1)]
    linear_combination haffine
  have hmass : saddleJetMassCoefficient d (j + 1) -
      saddleJetMassCoefficient e (j + 1) =
      I ^ (2 * j + 1 + 1) * (d (2 * j + 1) - e (2 * j + 1)) /
          (((2 * j + 1 + 1).factorial : ℕ) : ℂ) *
        normalizedGaussianMoment (2 * j + 1 + 1) := by
    unfold saddleJetMassCoefficient
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring, ← map_sub, hexp,
      Polynomial.C_mul', map_smul, gaussianPolynomialContraction_X_pow,
      smul_eq_mul]
  have hI : (I : ℂ) ^ (2 * (j + 1)) = (-1 : ℂ) ^ (j + 1) := by
    rw [pow_mul, Complex.I_sq]
  have key : I ^ (2 * (j + 1)) * (d (2 * j + 1) - e (2 * j + 1)) /
        (((2 * (j + 1)).factorial : ℕ) : ℂ) *
      normalizedGaussianMoment (2 * (j + 1)) =
      (-1 : ℂ) ^ (j + 1) * (d (2 * j + 1) - e (2 * j + 1)) *
        (normalizedGaussianMoment (2 * (j + 1)) /
          (((2 * (j + 1)).factorial : ℕ) : ℂ)) := by
    rw [hI]
    ring
  rw [hmass, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, key,
    normalizedGaussianMoment_div_factorial j]
  ring

/-- The Fabius specialization: the coefficient of the top jet in the
order-`(j+1)` mass coefficient. -/
theorem fabiusSaddleMassCoefficientComplex_succ_sub (j : ℕ) (t u : ℝ)
    (h : ∀ m, m < 2 * j + 1 →
      negativeLaplaceBoundedExponentJet m t =
        negativeLaplaceBoundedExponentJet m u) :
    fabiusSaddleMassCoefficientComplex (j + 1) t -
        fabiusSaddleMassCoefficientComplex (j + 1) u =
      (-1 : ℂ) ^ (j + 1) / ((2 : ℂ) ^ (j + 1) * (((j + 1).factorial : ℕ) : ℂ)) *
        ((negativeLaplaceBoundedExponentJet (2 * j + 1) t : ℂ) -
          (negativeLaplaceBoundedExponentJet (2 * j + 1) u : ℂ)) := by
  rw [fabiusSaddleMassCoefficientComplex_eq_saddleJet,
    fabiusSaddleMassCoefficientComplex_eq_saddleJet]
  exact saddleJetMassCoefficient_succ_sub j _ _ fun m hm => by
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) (h m hm)

end

end Fabius

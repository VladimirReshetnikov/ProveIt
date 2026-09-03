import FabiusFunction.SaddleLogExpansionAlgebra
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred

/-!
# Moment--cumulant algebra

This module turns the ordinary-coefficient formal exponential and logarithm
recurrences of `Fabius.SaddleExpansion` into the natural transforms for
exponential generating functions.  For a sequence `a`, `factorialNormalize a`
is the coefficient sequence `a_n / n!`, while `factorialDenormalize` restores
ordinary moments by multiplying the coefficient of degree `n` by `n!`.

The complete Bell transform exponentiates a factorially normalized cumulant
sequence.  Its inverse, `momentCumulant`, takes the formal logarithm of a
factorially normalized moment sequence.  Both transforms are defined over an
arbitrary commutative rational algebra: no field, topology, order, or
nontriviality assumption is used.  Their all-index inverse laws retain the
unavoidable formal normalizations at degree zero: moments have zeroth term
one and cumulants have zeroth term zero.

## Main results

* `factorialNormalize_factorialDenormalize` and its converse identify the two
  changes of coefficient convention as inverse equivalences.
* `completeBellPolynomial` is the all-orders complete Bell transform from
  cumulants to moments.
* `momentCumulant` is the inverse logarithmic transform from moments to
  cumulants.
* `completeBellPolynomial_factorialDenormalize` and
  `momentCumulant_factorialDenormalize` connect these exponential-generating
  transforms directly to the ordinary `expCoeff` and `logCoeff` recurrences.
* `factorialNormalize_completeBellPolynomial` and
  `factorialNormalize_momentCumulant` expose the same connection in the
  normalization-first direction.
* `completeBellPolynomial_momentCumulant` and
  `momentCumulant_completeBellPolynomial` are the unconditional all-index
  inverse formulas.
* `completeBellPolynomial_momentCumulant_of_zero_eq_one` and
  `momentCumulant_completeBellPolynomial_of_zero_eq_zero` are the corresponding
  function-level inverse laws for normalized moment and cumulant sequences.
* `completeBellPolynomial_succ` is the classical complete Bell recurrence.
* `momentCumulant_succ_recurrence` and `momentCumulant_recurrence` are its
  corresponding normalized-moment forms.
* `map_completeBellPolynomial` and `map_momentCumulant` express functoriality
  under morphisms of commutative rational algebras.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open SaddleExpansion

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Divide the coefficient of degree `n` by `n!`, converting an exponential-
generating sequence into ordinary power-series coefficients. -/
def factorialNormalize (a : ℕ → R) (n : ℕ) : R :=
  ((n.factorial : ℚ)⁻¹) • a n

/-- Multiply the coefficient of degree `n` by `n!`, undoing
`factorialNormalize`. -/
def factorialDenormalize (a : ℕ → R) (n : ℕ) : R :=
  (n.factorial : ℚ) • a n

/-- Factorial normalization after denormalization recovers every coefficient. -/
@[simp]
theorem factorialNormalize_factorialDenormalize (a : ℕ → R) :
    factorialNormalize (factorialDenormalize a) = a := by
  funext n
  have hn : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [factorialNormalize, factorialDenormalize, ← mul_smul,
    inv_mul_cancel₀ hn, one_smul]

/-- Factorial denormalization after normalization recovers every coefficient. -/
@[simp]
theorem factorialDenormalize_factorialNormalize (a : ℕ → R) :
    factorialDenormalize (factorialNormalize a) = a := by
  funext n
  have hn : (n.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  rw [factorialDenormalize, factorialNormalize, ← mul_smul,
    mul_inv_cancel₀ hn, one_smul]

/-- The complete Bell transform: `completeBellPolynomial κ n` is the `n`-th
moment obtained by exponentiating the exponential generating series of the
cumulants `κ`.  Equivalently, it is `n!` times the coefficient of degree
`n` in `exp (∑ j ≥ 1, κ_j X^j / j!)`; the supplied value `κ 0` is
irrelevant. -/
def completeBellPolynomial (κ : ℕ → R) (n : ℕ) : R :=
  factorialDenormalize (expCoeff (factorialNormalize κ)) n

/-- The moment--cumulant transform: `momentCumulant μ n` is `n!` times the
coefficient of degree `n` in the formal logarithm of
`1 + ∑ j ≥ 1, μ_j X^j / j!`; the supplied value `μ 0` is irrelevant. -/
def momentCumulant (μ : ℕ → R) (n : ℕ) : R :=
  factorialDenormalize (logCoeff (factorialNormalize μ)) n

/-- Normalizing a complete Bell transform recovers its ordinary exponential
coefficient family. -/
@[simp]
theorem factorialNormalize_completeBellPolynomial (κ : ℕ → R) :
    factorialNormalize (completeBellPolynomial κ) =
      expCoeff (factorialNormalize κ) := by
  change factorialNormalize
      (factorialDenormalize (expCoeff (factorialNormalize κ))) = _
  exact factorialNormalize_factorialDenormalize _

/-- Normalizing a moment--cumulant transform recovers the ordinary formal
logarithmic coefficient family. -/
@[simp]
theorem factorialNormalize_momentCumulant (μ : ℕ → R) :
    factorialNormalize (momentCumulant μ) =
      logCoeff (factorialNormalize μ) := by
  change factorialNormalize
      (factorialDenormalize (logCoeff (factorialNormalize μ))) = _
  exact factorialNormalize_factorialDenormalize _

/-- Applying the complete Bell transform to a factorially denormalized
ordinary exponent sequence is exactly factorial denormalization of the
ordinary exponential coefficients. -/
theorem completeBellPolynomial_factorialDenormalize (E : ℕ → R) :
    completeBellPolynomial (factorialDenormalize E) =
      factorialDenormalize (expCoeff E) := by
  funext n
  change factorialDenormalize
    (expCoeff (factorialNormalize (factorialDenormalize E))) n = _
  rw [factorialNormalize_factorialDenormalize]

/-- Applying the moment--cumulant transform to a factorially denormalized
ordinary moment sequence is exactly factorial denormalization of the
ordinary logarithmic coefficients. -/
theorem momentCumulant_factorialDenormalize (a : ℕ → R) :
    momentCumulant (factorialDenormalize a) =
      factorialDenormalize (logCoeff a) := by
  funext n
  change factorialDenormalize
    (logCoeff (factorialNormalize (factorialDenormalize a))) n = _
  rw [factorialNormalize_factorialDenormalize]

/-- The zeroth complete Bell polynomial is one, independently of the zeroth
cumulant supplied by the caller. -/
@[simp]
theorem completeBellPolynomial_zero (κ : ℕ → R) :
    completeBellPolynomial κ 0 = 1 := by
  simp [completeBellPolynomial, factorialDenormalize]

/-- The zeroth formal cumulant is zero, independently of the zeroth moment
supplied by the caller. -/
@[simp]
theorem momentCumulant_zero (μ : ℕ → R) : momentCumulant μ 0 = 0 := by
  simp [momentCumulant, factorialDenormalize]

private theorem natCast_succ_mul_inv_factorial_smul (j : ℕ) (x : R) :
    (j + 1 : R) * (((j + 1).factorial : ℚ)⁻¹ • x) =
      ((j.factorial : ℚ)⁻¹ • x) := by
  have hjfac : (j.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hsucc : (j + 1 : ℚ) ≠ 0 := by positivity
  have hq :
      (j + 1 : ℚ) * ((j + 1).factorial : ℚ)⁻¹ =
        (j.factorial : ℚ)⁻¹ := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp [hjfac, hsucc]
  rw [Algebra.smul_def, Algebra.smul_def,
    show (j + 1 : R) = algebraMap ℚ R (j + 1 : ℚ) by norm_num,
    ← mul_assoc, ← map_mul, hq]

private theorem factorial_mul_inv_factorial_smul_eq_choose
    (n j : ℕ) (hj : j ≤ n) (x : R) :
    ((n.factorial : ℚ) * (j.factorial : ℚ)⁻¹) • x =
      (n.choose j : R) * (((n - j).factorial : ℚ) • x) := by
  have hjfac : (j.factorial : ℚ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero j
  have hfactorial :
      (n.choose j : ℚ) * (j.factorial : ℚ) * ((n - j).factorial : ℚ) =
        (n.factorial : ℚ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hj
  have hratio :
      (n.factorial : ℚ) * (j.factorial : ℚ)⁻¹ =
        (n.choose j : ℚ) * ((n - j).factorial : ℚ) := by
    rw [← hfactorial]
    field_simp [hjfac]
  rw [hratio, mul_smul, Algebra.smul_def]
  norm_num

/-- The complete Bell polynomials satisfy their classical successor
recurrence

`B_(n+1)(κ) = ∑ j ≤ n, choose n j * κ_(j+1) * B_(n-j)(κ)`.

The proof is the formal differential equation for the exponential series,
with factorial normalization converting its ordinary convolution into the
binomial convolution. -/
theorem completeBellPolynomial_succ (κ : ℕ → R) (n : ℕ) :
    completeBellPolynomial κ (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : R) * κ (j + 1) * completeBellPolynomial κ (n - j) := by
  rw [completeBellPolynomial, factorialDenormalize, expCoeff_succ, smul_smul]
  have hsucc : (n + 1 : ℚ) ≠ 0 := by positivity
  have hfactorial :
      ((n + 1).factorial : ℚ) * (n + 1 : ℚ)⁻¹ =
        (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp [hsucc]
  rw [hfactorial, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := by
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [factorialNormalize, natCast_succ_mul_inv_factorial_smul,
    smul_mul_assoc, smul_smul,
    factorial_mul_inv_factorial_smul_eq_choose n j hjle,
    ← mul_smul_comm, ← mul_assoc]
  rfl

/-- Exponentiating the cumulants extracted from `μ` recovers `μ` at every
positive index and installs the canonical zeroth moment `1`. -/
theorem completeBellPolynomial_momentCumulant (μ : ℕ → R) (n : ℕ) :
    completeBellPolynomial (momentCumulant μ) n =
      if n = 0 then 1 else μ n := by
  change factorialDenormalize
      (expCoeff
        (factorialNormalize
          (factorialDenormalize (logCoeff (factorialNormalize μ))))) n = _
  rw [factorialNormalize_factorialDenormalize]
  change (n.factorial : ℚ) • expCoeff (logCoeff (factorialNormalize μ)) n = _
  rw [expCoeff_logCoeff_eq_ite]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [if_neg hn]
    exact congrFun (factorialDenormalize_factorialNormalize μ) n

/-- Taking cumulants of the complete Bell transform of `κ` recovers `κ`
at every positive index and installs the canonical zeroth cumulant `0`. -/
theorem momentCumulant_completeBellPolynomial (κ : ℕ → R) (n : ℕ) :
    momentCumulant (completeBellPolynomial κ) n =
      if n = 0 then 0 else κ n := by
  change factorialDenormalize
      (logCoeff
        (factorialNormalize
          (factorialDenormalize (expCoeff (factorialNormalize κ))))) n = _
  rw [factorialNormalize_factorialDenormalize]
  change (n.factorial : ℚ) • logCoeff (expCoeff (factorialNormalize κ)) n = _
  rw [logCoeff_expCoeff_eq_ite]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [if_neg hn]
    exact congrFun (factorialDenormalize_factorialNormalize κ) n

/-- On moment sequences normalized by `μ 0 = 1`, the complete Bell transform
and the moment--cumulant transform are mutually inverse as functions. -/
theorem completeBellPolynomial_momentCumulant_of_zero_eq_one
    (μ : ℕ → R) (hμ : μ 0 = 1) :
    completeBellPolynomial (momentCumulant μ) = μ := by
  funext n
  rw [completeBellPolynomial_momentCumulant]
  by_cases hn : n = 0
  · subst n
    simpa using hμ.symm
  · simp [hn]

/-- On cumulant sequences normalized by `κ 0 = 0`, the moment--cumulant
transform and the complete Bell transform are mutually inverse as functions. -/
theorem momentCumulant_completeBellPolynomial_of_zero_eq_zero
    (κ : ℕ → R) (hκ : κ 0 = 0) :
    momentCumulant (completeBellPolynomial κ) = κ := by
  funext n
  rw [momentCumulant_completeBellPolynomial]
  by_cases hn : n = 0
  · subst n
    simpa using hκ.symm
  · simp [hn]

/-- The classical moment--cumulant recurrence in successor form:
`mu_(n+1) = ∑ j ≤ n, choose(n,j) * kappa_(j+1) * mu_(n-j)`. -/
theorem momentCumulant_succ_recurrence
    (μ : ℕ → R) (hμ0 : μ 0 = 1) (n : ℕ) :
    μ (n + 1) =
      ∑ j ∈ Finset.range (n + 1),
        (n.choose j : R) * momentCumulant μ (j + 1) * μ (n - j) := by
  have h := completeBellPolynomial_succ (momentCumulant μ) n
  rw [completeBellPolynomial_momentCumulant_of_zero_eq_one μ hμ0] at h
  exact h

/-- The classical moment--cumulant recurrence indexed by the cumulant order:
`mu_N = ∑ k in [1,N], choose(N-1,k-1) * kappa_k * mu_(N-k)`. -/
theorem momentCumulant_recurrence
    (μ : ℕ → R) (hμ0 : μ 0 = 1)
    (N : ℕ) (hN : 1 ≤ N) :
    μ N =
      ∑ k ∈ Finset.Icc 1 N,
        (Nat.choose (N - 1) (k - 1) : R) *
          momentCumulant μ k * μ (N - k) := by
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  simpa [add_comm] using momentCumulant_succ_recurrence μ hμ0 n

/-- The complete Bell transform commutes with morphisms of commutative
rational algebras. -/
theorem map_completeBellPolynomial {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (κ : ℕ → R) (n : ℕ) :
    f (completeBellPolynomial κ n) =
      completeBellPolynomial (fun j ↦ f (κ j)) n := by
  simp only [completeBellPolynomial, factorialDenormalize, map_smul,
    map_expCoeff]
  rw [show (fun j ↦ f (factorialNormalize κ j)) =
      factorialNormalize (fun j ↦ f (κ j)) by
    funext j
    simp [factorialNormalize]]

/-- The moment--cumulant transform commutes with morphisms of commutative
rational algebras. -/
theorem map_momentCumulant {S : Type*} [CommRing S] [Algebra ℚ S]
    (f : R →ₐ[ℚ] S) (μ : ℕ → R) (n : ℕ) :
    f (momentCumulant μ n) = momentCumulant (fun j ↦ f (μ j)) n := by
  simp only [momentCumulant, factorialDenormalize, map_smul, map_logCoeff]
  rw [show (fun j ↦ f (factorialNormalize μ j)) =
      factorialNormalize (fun j ↦ f (μ j)) by
    funext j
    simp [factorialNormalize]]

end

end Fabius

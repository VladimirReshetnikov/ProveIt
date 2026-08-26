import FabiusFunction.SaddleExpansionAlgebra
import Mathlib.Algebra.Polynomial.Div

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius.SaddleExpansion

noncomputable section

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-!
# Exact finite remainders for saddle exponential coefficients

This module turns the formal coefficient identity for `expCoeff` into a
finite polynomial identity.  When the exponent has zero constant term,
substituting its degree-`L-1` truncation into the degree-`L-1` exponential
polynomial differs from the recursive coefficient polynomial by an exact
multiple of `X ^ L`.  The canonical quotient is defined by iterating
`Polynomial.divX`, so its dependence on parameterized coefficients remains
algebraic and can be bounded uniformly downstream.  The underlying polynomial
facts are exposed here as well: an initial coefficient gap makes iterated
`divX` exact after multiplication by the matching power of `X`, and this
iteration commutes with coefficientwise ring maps.
-/

/-- The order-`L-1` polynomial truncation of a formal exponent. -/
def exponentTruncPolynomial (E : ℕ → R) (L : ℕ) : Polynomial R :=
  PowerSeries.trunc L (exponentSeries E)

/-- Substitute the truncated exponent into the order-`L-1` exponential
polynomial. -/
def finiteExpSubstitutionPolynomial (E : ℕ → R) (L : ℕ) : Polynomial R :=
  (PowerSeries.trunc L (PowerSeries.exp R)).comp
    (exponentTruncPolynomial E L)

/-- Polynomial made from the recursively generated exponential
coefficients through order `L-1`. -/
def expCoeffTruncPolynomial (E : ℕ → R) (L : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range L, Polynomial.monomial k (expCoeff E k)

/-- The finite exponential substitution defect.  Its first `L` coefficients
vanish when the exponent has zero constant term. -/
def finiteExpSubstitutionDefect (E : ℕ → R) (L : ℕ) : Polynomial R :=
  finiteExpSubstitutionPolynomial E L - expCoeffTruncPolynomial E L

omit [Algebra ℚ R] in
/-- The constant coefficient of the truncated exponent is `E 0`, provided
the truncation order `L` is positive. -/
lemma constantCoeff_exponentTruncPolynomial
    (E : ℕ → R) (L : ℕ) (hL : 0 < L) :
    (exponentTruncPolynomial E L).coeff 0 = E 0 := by
  simp [exponentTruncPolynomial, PowerSeries.coeff_trunc, hL,
    coeff_exponentSeries]

omit [Algebra ℚ R] in
/-- Truncating the exponent does not disturb low-order coefficients of its
powers: for `k < L` and any exponent `d`, the `k`th power-series coefficient
of `exponentTruncPolynomial E L ^ d`, read as a power series, equals that of
`exponentSeries E ^ d`. -/
lemma coeff_pow_exponentTruncPolynomial_eq
    (E : ℕ → R) (L d k : ℕ) (hk : k < L) :
    PowerSeries.coeff k
        (((exponentTruncPolynomial E L : Polynomial R) : PowerSeries R) ^ d) =
      PowerSeries.coeff k ((exponentSeries E) ^ d) := by
  have htrunc := PowerSeries.trunc_trunc_pow (exponentSeries E) L d
  have hcoeff := congrArg (fun p : Polynomial R => p.coeff k) htrunc
  simpa only [exponentTruncPolynomial, PowerSeries.coeff_trunc,
    if_pos hk] using hcoeff

/-- Below the truncation order the finite substitution reproduces the
recursive coefficients: if `E 0 = 0` then for every `k < L` the `k`th
coefficient of `finiteExpSubstitutionPolynomial E L` is `expCoeff E k`.
Nothing is claimed about coefficients of order `L` or higher. -/
lemma coeff_finiteExpSubstitutionPolynomial_eq_expCoeff
    (E : ℕ → R) (hEzero : E 0 = 0) (L k : ℕ) (hk : k < L) :
    (finiteExpSubstitutionPolynomial E L).coeff k = expCoeff E k := by
  have hconst : PowerSeries.constantCoeff (exponentSeries E) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simpa using hEzero
  have hhas : PowerSeries.HasSubst (exponentSeries E) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hconst
  have hsupport : Function.support (fun d : ℕ =>
      PowerSeries.coeff d (PowerSeries.exp R) •
        PowerSeries.coeff k ((exponentSeries E) ^ d)) ⊆
      (Finset.range L : Set ℕ) := by
    intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.mem_coe, Finset.mem_range]
    by_contra hnot
    have hLd : L ≤ d := Nat.le_of_not_gt hnot
    have hkd : k < d := hk.trans_le hLd
    have hzero : PowerSeries.coeff k ((exponentSeries E) ^ d) = 0 := by
      apply PowerSeries.coeff_of_lt_order
      exact (by exact_mod_cast hkd : (k : ENat) < (d : ENat)).trans_le
        (PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hconst)
    exact hd (by simp [hzero])
  have hfull :
      PowerSeries.coeff k
          ((PowerSeries.exp R).subst (exponentSeries E)) =
        ∑ d ∈ Finset.range L,
          PowerSeries.coeff d (PowerSeries.exp R) *
            PowerSeries.coeff k ((exponentSeries E) ^ d) := by
    rw [PowerSeries.coeff_subst' hhas,
      finsum_eq_sum_of_support_subset _ hsupport]
    simp only [smul_eq_mul]
  cases L with
  | zero => omega
  | succ l =>
      rw [finiteExpSubstitutionPolynomial, Polynomial.comp,
        Polynomial.eval₂_eq_sum_range' Polynomial.C
          (PowerSeries.natDegree_trunc_lt (PowerSeries.exp R) l)
          (exponentTruncPolynomial E (l + 1)),
        Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul]
      have hsum :
          (∑ d ∈ Finset.range (l + 1),
            (PowerSeries.trunc (l + 1) (PowerSeries.exp R)).coeff d *
              (exponentTruncPolynomial E (l + 1) ^ d).coeff k) =
          ∑ d ∈ Finset.range (l + 1),
            PowerSeries.coeff d (PowerSeries.exp R) *
              PowerSeries.coeff k ((exponentSeries E) ^ d) := by
        apply Finset.sum_congr rfl
        intro d hd
        have hdL : d < l + 1 := Finset.mem_range.mp hd
        rw [PowerSeries.coeff_trunc, if_pos hdL]
        congr 1
        rw [← Polynomial.coeff_coe, Polynomial.coe_pow]
        exact coeff_pow_exponentTruncPolynomial_eq E (l + 1) d k hk
      rw [hsum, ← hfull, ← expSeries_eq_exp_subst E hEzero,
        coeff_expSeries]

/-- For an exponent with vanishing constant term, `X ^ L` divides the finite
exponential substitution defect; equivalently every coefficient of
`finiteExpSubstitutionDefect E L` below order `L` vanishes.  This is what
justifies dividing by `X ^ L` in
`X_pow_mul_finiteExpSubstitutionQuotient` below. -/
theorem X_pow_dvd_finiteExpSubstitutionDefect
    (E : ℕ → R) (hEzero : E 0 = 0) (L : ℕ) :
    Polynomial.X ^ L ∣ finiteExpSubstitutionDefect E L := by
  rw [Polynomial.X_pow_dvd_iff]
  intro k hk
  rw [finiteExpSubstitutionDefect, Polynomial.coeff_sub,
    coeff_finiteExpSubstitutionPolynomial_eq_expCoeff E hEzero L k hk,
    expCoeffTruncPolynomial, Polynomial.finsetSum_coeff]
  have hk_mem : k ∈ Finset.range L := Finset.mem_range.mpr hk
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [Polynomial.coeff_monomial, hbk]
  · intro hnot
    exact (hnot hk_mem).elim

/-- Canonical iterated-`divX` quotient; when `E 0 = 0`, this removes the
defect's first `L` zero coefficients. -/
def finiteExpSubstitutionQuotient (E : ℕ → R) (L : ℕ) : Polynomial R :=
  (Polynomial.divX^[L]) (finiteExpSubstitutionDefect E L)

/-- Multiplying by `X ^ L` reverses `L` applications of `divX` when the first
`L` coefficients of the polynomial vanish. -/
theorem X_pow_mul_iterate_divX_eq_of_coeff_zero
    {S : Type*} [CommRing S] (p : Polynomial S) (L : ℕ)
    (hzero : ∀ k < L, p.coeff k = 0) :
    Polynomial.X ^ L * (Polynomial.divX^[L]) p = p := by
  induction L generalizing p with
  | zero => simp
  | succ L ih =>
      have hp0 : p.coeff 0 = 0 := hzero 0 (by omega)
      have hdiv : ∀ k < L, (Polynomial.divX p).coeff k = 0 := by
        intro k hk
        rw [Polynomial.coeff_divX]
        exact hzero (k + 1) (by omega)
      rw [Function.iterate_succ_apply]
      rw [pow_succ']
      rw [mul_assoc, ih (Polynomial.divX p) hdiv]
      simpa [hp0] using Polynomial.X_mul_divX_add p

/-- Dividing a polynomial by `X` commutes with a coefficientwise ring map. -/
theorem map_divX {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (p : Polynomial A) :
    p.divX.map f = (p.map f).divX := by
  ext d
  simp [Polynomial.coeff_divX]

/-- Every finite iterate of `divX` commutes with a coefficientwise ring map. -/
theorem map_iterate_divX {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (L : ℕ) (p : Polynomial A) :
    ((Polynomial.divX^[L]) p).map f =
      (Polynomial.divX^[L]) (p.map f) := by
  induction L generalizing p with
  | zero => simp
  | succ L ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        ih, map_divX]

/-- Exact factorization of the finite exponential defect by the first
omitted power. -/
theorem X_pow_mul_finiteExpSubstitutionQuotient
    (E : ℕ → R) (hEzero : E 0 = 0) (L : ℕ) :
    Polynomial.X ^ L * finiteExpSubstitutionQuotient E L =
      finiteExpSubstitutionDefect E L := by
  apply X_pow_mul_iterate_divX_eq_of_coeff_zero
  intro k hk
  exact (Polynomial.X_pow_dvd_iff.mp
    (X_pow_dvd_finiteExpSubstitutionDefect E hEzero L)) k hk

/-- Evaluated finite exponential substitution equals its recursively
generated truncation plus an exact `x^L` remainder. -/
theorem eval_finiteExpSubstitutionPolynomial_eq
    (E : ℕ → R) (hEzero : E 0 = 0) (L : ℕ) (x : R) :
    (finiteExpSubstitutionPolynomial E L).eval x =
      (expCoeffTruncPolynomial E L).eval x +
        x ^ L * (finiteExpSubstitutionQuotient E L).eval x := by
  have hfactor := X_pow_mul_finiteExpSubstitutionQuotient E hEzero L
  have heval := congrArg (Polynomial.eval x) hfactor
  simp only [Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X] at heval
  unfold finiteExpSubstitutionDefect at heval
  rw [Polynomial.eval_sub] at heval
  rw [heval]
  ring

/-- The recursive coefficient polynomial evaluates to the expected finite
power sum. -/
theorem eval_expCoeffTruncPolynomial
    (E : ℕ → R) (L : ℕ) (x : R) :
    (expCoeffTruncPolynomial E L).eval x =
      ∑ k ∈ Finset.range L, x ^ k * expCoeff E k := by
  unfold expCoeffTruncPolynomial
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Polynomial.eval_monomial]
  ring

omit [Algebra ℚ R] in
/-- Evaluation of the truncated exponent polynomial. -/
theorem eval_exponentTruncPolynomial
    (E : ℕ → R) (L : ℕ) (x : R) :
    (exponentTruncPolynomial E L).eval x =
      ∑ k ∈ Finset.range L, x ^ k * E k := by
  unfold exponentTruncPolynomial
  rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [Polynomial.eval_monomial, coeff_exponentSeries]
  ring

/-- Explicit finite Taylor form of the substituted exponential
polynomial. -/
theorem eval_finiteExpSubstitutionPolynomial
    (E : ℕ → R) (L : ℕ) (x : R) :
    (finiteExpSubstitutionPolynomial E L).eval x =
      ∑ q ∈ Finset.range L,
        algebraMap ℚ R (1 / q.factorial) *
          (∑ k ∈ Finset.range L, x ^ k * E k) ^ q := by
  rw [finiteExpSubstitutionPolynomial, Polynomial.eval_comp,
    eval_exponentTruncPolynomial]
  rw [PowerSeries.trunc_apply, Nat.Ico_zero_eq_range,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro q _hq
  rw [Polynomial.eval_monomial, PowerSeries.coeff_exp]

/-- Fully expanded exact finite-remainder identity.  The finite Taylor
polynomial in the truncated exponent equals the recursively generated
coefficient sum plus the canonical remainder divisible by `x ^ L`. -/
theorem finiteExpSubstitution_sum_eq_expCoeff_sum_add_remainder
    (E : ℕ → R) (hEzero : E 0 = 0) (L : ℕ) (x : R) :
    (∑ q ∈ Finset.range L,
        algebraMap ℚ R (1 / q.factorial) *
          (∑ k ∈ Finset.range L, x ^ k * E k) ^ q) =
      (∑ k ∈ Finset.range L, x ^ k * expCoeff E k) +
        x ^ L * (finiteExpSubstitutionQuotient E L).eval x := by
  calc
    (∑ q ∈ Finset.range L,
        algebraMap ℚ R (1 / q.factorial) *
          (∑ k ∈ Finset.range L, x ^ k * E k) ^ q) =
        (finiteExpSubstitutionPolynomial E L).eval x :=
      (eval_finiteExpSubstitutionPolynomial E L x).symm
    _ = (expCoeffTruncPolynomial E L).eval x +
          x ^ L * (finiteExpSubstitutionQuotient E L).eval x :=
      eval_finiteExpSubstitutionPolynomial_eq E hEzero L x
    _ = (∑ k ∈ Finset.range L, x ^ k * expCoeff E k) +
          x ^ L * (finiteExpSubstitutionQuotient E L).eval x := by
      rw [eval_expCoeffTruncPolynomial]

end

end Fabius.SaddleExpansion

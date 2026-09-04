import FabiusFunction.AppellSequence
import FabiusFunction.BernoulliFormalLog
import FabiusFunction.NorlundPolynomials
import FabiusFunction.UnitSeriesBellCoefficients
import Mathlib.Algebra.Polynomial.Roots

/-!
# Nörlund polynomials of arbitrary scalar order

Let `B(t) = t/(exp(t)-1)`.  For an arbitrary scalar `α` in a commutative
rational algebra, form the normalized series

`U_α(t) = exp(α log B(t))`.

Its factorially weighted coefficients are the input to the existing Appell
polynomial construction.  Thus the resulting `generalizedNorlund α n` are
actual polynomials and have generating function `U_α(t) exp(x t)`.
No positivity, integrality, or nonzero assumption is imposed on the order.
In particular, zero and negative orders are included in the definition.

The construction agrees, as a polynomial equality over `ℚ`, with the
existing `norlund` at every natural order.  Its Appell derivative, translation,
convolution, and degree properties follow from the shared polynomial and
exponential algebra.

All statements here concern formal series and polynomials.  They do not
assert analytic convergence or choose an analytic logarithm branch.
-/

set_option autoImplicit false

open PowerSeries

noncomputable section

namespace Fabius

variable {A : Type*} [CommRing A] [Algebra ℚ A]

private theorem scaledBernoulliLog_constantCoeff (α : A) :
    constantCoeff (α • PowerSeries.logOf (bernoulliPowerSeries A)) = 0 := by
  rw [PowerSeries.constantCoeff_smul,
    PowerSeries.constantCoeff_logOf (constantCoeff_bernoulliPowerSeries A), smul_zero]

/-- The arbitrary-order Bernoulli kernel, defined by formal exponentiation
of its normalized logarithm: `U_α = exp(α log(t/(exp(t)-1)))`. -/
def generalizedNorlundKernel (α : A) : A⟦X⟧ :=
  (exp A).subst (α • PowerSeries.logOf (bernoulliPowerSeries A))

/-- Every arbitrary-order Bernoulli kernel has constant coefficient one. -/
@[simp] theorem constantCoeff_generalizedNorlundKernel (α : A) :
    constantCoeff (generalizedNorlundKernel α) = 1 :=
  constantCoeff_exp_subst (scaledBernoulliLog_constantCoeff α)

/-- Order zero gives the unit kernel. -/
@[simp] theorem generalizedNorlundKernel_zero :
    generalizedNorlundKernel (0 : A) = 1 := by
  rw [generalizedNorlundKernel, zero_smul, subst_zero_eq_C_constantCoeff,
    constantCoeff_exp, map_one]

/-- Order one gives the original Bernoulli kernel. -/
@[simp] theorem generalizedNorlundKernel_one :
    generalizedNorlundKernel (1 : A) = bernoulliPowerSeries A := by
  rw [generalizedNorlundKernel, one_smul,
    exp_subst_logOf (constantCoeff_bernoulliPowerSeries A)]

/-- Adding arbitrary scalar orders multiplies their kernels. -/
theorem generalizedNorlundKernel_add (α β : A) :
    generalizedNorlundKernel (α + β) =
      generalizedNorlundKernel α * generalizedNorlundKernel β := by
  rw [generalizedNorlundKernel, add_smul,
    exp_subst_add (scaledBernoulliLog_constantCoeff α) (scaledBernoulliLog_constantCoeff β)]
  rfl

/-- Natural scalar orders coincide with ordinary natural powers of the
Bernoulli kernel, in every commutative rational algebra. -/
theorem generalizedNorlundKernel_natCast (m : ℕ) :
    generalizedNorlundKernel (m : A) = bernoulliPowerSeries A ^ m := by
  induction m with
  | zero => rw [Nat.cast_zero, generalizedNorlundKernel_zero, pow_zero]
  | succ m ih =>
      rw [Nat.cast_add, Nat.cast_one, generalizedNorlundKernel_add, ih,
        generalizedNorlundKernel_one, pow_succ]

/-- Nörlund polynomials of arbitrary scalar order.  The Appell coefficient
sequence is extracted from `exp(α log B)`, independently of any Bell formula. -/
def generalizedNorlund (α : A) (n : ℕ) : Polynomial A :=
  Appell.poly (factorialDenormalize fun k => coeff k (generalizedNorlundKernel α)) n

private theorem generalizedNorlundInput_zero (α : A) :
    (factorialDenormalize fun k => coeff k (generalizedNorlundKernel α)) 0 = 1 := by
  rw [factorialDenormalize, Nat.factorial_zero, Nat.cast_one, one_smul,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_generalizedNorlundKernel]

/-- The degree-zero polynomial is one for every scalar order. -/
@[simp] theorem generalizedNorlund_zero (α : A) : generalizedNorlund α 0 = 1 := by
  rw [generalizedNorlund, Appell.poly_zero, generalizedNorlundInput_zero, Polynomial.C_1]

/-- Every arbitrary-order Nörlund polynomial is monic. -/
theorem generalizedNorlund_monic (α : A) (n : ℕ) : (generalizedNorlund α n).Monic :=
  Appell.monic_poly (generalizedNorlundInput_zero α) n

/-- Over a nontrivial coefficient algebra, the `n`-th Nörlund polynomial
has degree exactly `n`, for every scalar order. -/
theorem natDegree_generalizedNorlund [Nontrivial A] (α : A) (n : ℕ) :
    (generalizedNorlund α n).natDegree = n :=
  Appell.natDegree_poly (generalizedNorlundInput_zero α) n

/-- The Appell derivative law for arbitrary scalar order. -/
theorem derivative_generalizedNorlund_succ (α : A) (n : ℕ) :
    Polynomial.derivative (generalizedNorlund α (n + 1)) =
      Polynomial.C ((n : A) + 1) * generalizedNorlund α n :=
  Appell.derivative_poly _ n

private theorem egfA_geometric (x : A) :
    egfA A (fun n => x ^ n) = rescale x (exp A) := by
  ext n
  rw [coeff_egfA, coeff_rescale, coeff_exp]
  ring

/-- The full exponential generating function of the arbitrary-order Nörlund
polynomials, including its degree-zero coefficient. -/
theorem egfA_generalizedNorlund_eval (α x : A) :
    egfA A (fun n => (generalizedNorlund α n).eval x) =
      generalizedNorlundKernel α * rescale x (exp A) := by
  have hvalues : (fun n => (generalizedNorlund α n).eval x) =
      Bell.binomialConv (fun n => x ^ n)
        (factorialDenormalize fun n => coeff n (generalizedNorlundKernel α)) := by
    funext n
    exact Appell.eval_poly _ x n
  rw [hvalues, ← egfA_mul, egfA_geometric, egfA_factorialDenormalize_coeff_eq, mul_comm]

/-- Polynomial translation for arbitrary scalar order, valid also in degree zero. -/
theorem generalizedNorlund_eval_add (α x y : A) (n : ℕ) :
    (generalizedNorlund α n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : A) *
        ((generalizedNorlund α k).eval x * y ^ (n - k)) := by
  have h : egfA A (fun n => (generalizedNorlund α n).eval (x + y)) =
      egfA A (Bell.binomialConv (fun n => (generalizedNorlund α n).eval x)
        (fun n => y ^ n)) := by
    rw [← egfA_mul, egfA_generalizedNorlund_eval, egfA_generalizedNorlund_eval,
      egfA_geometric, ← exp_mul_exp_eq_exp_add, mul_assoc]
  have hn := congrFun (seq_eq_of_egfA_eq A h) n
  rw [Bell.binomialConv_eq_sum_range] at hn
  exact hn

/-- Nörlund convolution for arbitrary scalar orders: both the orders and
the evaluation parameters add.  In particular, zero and negative orders
participate in the same identity. -/
theorem generalizedNorlund_add_eval_add (α β x y : A) (n : ℕ) :
    (generalizedNorlund (α + β) n).eval (x + y) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : A) *
        ((generalizedNorlund α k).eval x * (generalizedNorlund β (n - k)).eval y) := by
  have h : egfA A (fun n => (generalizedNorlund (α + β) n).eval (x + y)) =
      egfA A (Bell.binomialConv (fun n => (generalizedNorlund α n).eval x)
        (fun n => (generalizedNorlund β n).eval y)) := by
    rw [← egfA_mul, egfA_generalizedNorlund_eval, egfA_generalizedNorlund_eval,
      egfA_generalizedNorlund_eval, generalizedNorlundKernel_add,
      ← exp_mul_exp_eq_exp_add]
    ring
  have hn := congrFun (seq_eq_of_egfA_eq A h) n
  rw [Bell.binomialConv_eq_sum_range] at hn
  exact hn

/-- The arbitrary-order construction agrees as an actual polynomial with
the existing rational Nörlund family at every natural order. -/
theorem generalizedNorlund_natCast (m n : ℕ) :
    generalizedNorlund (m : ℚ) n = norlund m n := by
  apply Polynomial.funext
  intro x
  have h : egfA ℚ (fun n => (generalizedNorlund (m : ℚ) n).eval x) =
      egfA ℚ (fun n => (norlund m n).eval x) := by
    rw [egfA_generalizedNorlund_eval, generalizedNorlundKernel_natCast, egfA_norlund_eval]
  exact congrFun (seq_eq_of_egfA_eq ℚ h) n

/-- The cumulants of the arbitrary-order Nörlund generating function.
The positive Bernoulli convention makes the uniform positive-degree formula
give `x - α/2` in degree one; degree zero is explicitly zero. -/
def generalizedNorlundCumulant (α x : A) (n : ℕ) : A :=
  if n = 0 then 0 else
    (if n = 1 then x else 0) - α * algebraMap ℚ A (bernoulli' n / (n : ℚ))

/-- The Nörlund cumulant sequence is normalized to vanish in degree zero. -/
@[simp] theorem generalizedNorlundCumulant_zero (α x : A) :
    generalizedNorlundCumulant α x 0 = 0 := by
  simp [generalizedNorlundCumulant]

/-- The linear Nörlund cumulant is `x - α/2`, with the ordinary Bernoulli
sign convention accounted for explicitly. -/
@[simp] theorem generalizedNorlundCumulant_one (α x : A) :
    generalizedNorlundCumulant α x 1 = x - α * algebraMap ℚ A (1 / 2) := by
  simp [generalizedNorlundCumulant, bernoulli'_one]

/-- From degree two onward the cumulants are `-α B_n/n`, using ordinary
Bernoulli numbers. -/
theorem generalizedNorlundCumulant_of_two_le (α x : A) (n : ℕ) (hn : 2 ≤ n) :
    generalizedNorlundCumulant α x n = -α * algebraMap ℚ A (bernoulli n / (n : ℚ)) := by
  rw [generalizedNorlundCumulant, if_neg (by omega), if_neg (by omega),
    ← bernoulli_eq_bernoulli'_of_ne_one (by omega : n ≠ 1)]
  ring

/-- The explicit Nörlund cumulants recover the actual formal logarithm of
the generating function, rather than merely specifying an assumed expansion. -/
theorem bellWeightSeries_generalizedNorlundCumulant (α x : A) :
    bellWeightSeries A (generalizedNorlundCumulant α x) =
      α • PowerSeries.logOf (bernoulliPowerSeries A) + x • (X : A⟦X⟧) := by
  ext n
  rw [bellWeightSeries, coeff_egfA, map_add, PowerSeries.coeff_smul,
    PowerSeries.coeff_smul, smul_eq_mul, smul_eq_mul,
    coeff_logOf_bernoulliPowerSeries_algebra A n, coeff_X]
  by_cases hn : n = 0
  · subst n
    simp
  · simp only [generalizedNorlundCumulant, hn, if_false, map_neg]
    have hlinear : algebraMap ℚ A (1 / n.factorial) * (if n = 1 then x else 0) =
        x * (if n = 1 then 1 else 0) := by
      by_cases hn1 : n = 1
      · subst n
        simp
      · simp [hn1]
    have hratio : algebraMap ℚ A (1 / n.factorial) *
        algebraMap ℚ A (bernoulli' n / (n : ℚ)) =
        algebraMap ℚ A (bernoulli' n / ((n : ℚ) * n.factorial)) := by
      rw [← map_mul]
      congr 1
      rw [div_mul_div_comm, one_mul, mul_comm (n.factorial : ℚ) (n : ℚ)]
    rw [mul_sub, hlinear]
    calc
      x * (if n = 1 then 1 else 0) -
          algebraMap ℚ A (1 / n.factorial) *
            (α * algebraMap ℚ A (bernoulli' n / (n : ℚ))) =
        x * (if n = 1 then 1 else 0) - α *
          (algebraMap ℚ A (1 / n.factorial) *
            algebraMap ℚ A (bernoulli' n / (n : ℚ))) := by ring
      _ = α * -algebraMap ℚ A (bernoulli' n / ((n : ℚ) * n.factorial)) +
          x * (if n = 1 then 1 else 0) := by
        rw [hratio]
        ring

/-- The arbitrary-order Nörlund polynomials are the complete Bell
polynomials in the explicitly computed cumulants, including degree zero. -/
theorem generalizedNorlund_eval_eq_completeBell (α x : A) (n : ℕ) :
    (generalizedNorlund α n).eval x =
      Bell.complete (generalizedNorlundCumulant α x) n := by
  have hx : constantCoeff (x • (X : A⟦X⟧)) = 0 := by
    rw [PowerSeries.constantCoeff_smul, constantCoeff_X, smul_zero]
  have h : egfA A (fun n => (generalizedNorlund α n).eval x) =
      egfA A (Bell.complete (generalizedNorlundCumulant α x)) := by
    rw [egfA_generalizedNorlund_eval, generalizedNorlundKernel, rescale_eq_subst,
      ← exp_subst_add (scaledBernoulliLog_constantCoeff α) hx,
      ← bellWeightSeries_generalizedNorlundCumulant, exp_subst_bellWeightSeries]
  exact congrFun (seq_eq_of_egfA_eq A h) n

end Fabius

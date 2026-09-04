import FabiusFunction.BellPolynomialMoments
import FabiusFunction.ExpAddLog
import FabiusFunction.SaddleLogExpansionPowerSeries

/-!
# The formal logarithm of the Bernoulli kernel

For `B(t) = t/(exp(t)-1)`, normalized by `B(0)=1`, this module proves

`log B(t) = -t/2 - ∑_{n ≥ 2} bernoulli n * t^n / (n * n!)`.

The logarithm is Mathlib's `PowerSeries.logOf`, defined by substitution into
the universal formal logarithm.  Its coefficients are derived from the
already-proved logarithm of the reciprocal kernel `(exp(t)-1)/t`.
The existing `SaddleExpansion.logSeries_eq_logOf` identifies that coefficient
recurrence with Mathlib's logarithm; the logarithm product law supplies the
minus sign.

The distinction between the two Bernoulli conventions matters in degree one.
The formula valid in every positive degree uses `bernoulli'`, whose first
value is `1/2`.  The ordinary numbers `bernoulli`, with first value `-1/2`,
give the displayed formula only from degree two onward.  Degree zero is
explicitly zero.

The rational identities are transported coefficientwise to every commutative
`ℚ`-algebra, including those with zero divisors.  The transport uses the
naturality of formal substitution and of the universal logarithm, so no new
coefficient expansion is assumed.  No convergence radius or identification
with an analytic logarithm is asserted here.

## Main declarations

* `constantCoeff_bernoulliPowerSeries`: the kernel has unit constant coefficient.
* `bernoulliPowerSeries_mul_massSeries_expm1Div`: the two kernels are inverses.
* `logOf_bernoulliPowerSeries`: the exact formal logarithm series.
* `coeff_logOf_bernoulliPowerSeries`: the all-index formula, with a separate
  zero case and the positive Bernoulli convention.
* `coeff_one_logOf_bernoulliPowerSeries`: the linear coefficient is `-1/2`.
* `coeff_logOf_bernoulliPowerSeries_of_two_le`: the ordinary-Bernoulli form
  in every degree at least two.
* `map_logOf`, `map_bernoulliPowerSeries`: coefficient base change for the
  formal logarithm and the Bernoulli kernel.
* `logOf_bernoulliPowerSeries_algebra`,
  `coeff_logOf_bernoulliPowerSeries_algebra`, and
  `coeff_logOf_bernoulliPowerSeries_algebra_of_two_le`: the same identities
  over every commutative rational algebra.
-/

set_option autoImplicit false

open PowerSeries

namespace Fabius

/-- The Bernoulli kernel is normalized to have constant coefficient one
over every commutative rational algebra. -/
@[simp] theorem constantCoeff_bernoulliPowerSeries
    (A : Type*) [CommRing A] [Algebra ℚ A] :
    constantCoeff (bernoulliPowerSeries A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, bernoulliPowerSeries, coeff_mk]
  simp

/-- The Bernoulli kernel `t/(exp(t)-1)` and the explicitly constructed
series `(exp(t)-1)/t` multiply to one. -/
theorem bernoulliPowerSeries_mul_massSeries_expm1Div :
    bernoulliPowerSeries ℚ * SaddleExpansion.massSeries expm1DivCoefficient = 1 := by
  apply mul_left_cancel₀ (show (X : ℚ⟦X⟧) ≠ 0 from X_ne_zero)
  calc
    X * (bernoulliPowerSeries ℚ * SaddleExpansion.massSeries expm1DivCoefficient) =
        bernoulliPowerSeries ℚ * (X * SaddleExpansion.massSeries expm1DivCoefficient) := by
      ring
    _ = bernoulliPowerSeries ℚ * (exp ℚ - 1) := by rw [X_mul_massSeries_expm1Div]
    _ = X := bernoulliPowerSeries_mul_exp_sub_one ℚ
    _ = X * 1 := (mul_one X).symm

/-- The logarithm of the Bernoulli kernel is the negative of the known
Bernoulli logarithm of its reciprocal.  This is an identity of formal
series, not an assumed coefficient expansion. -/
theorem logOf_bernoulliPowerSeries :
    PowerSeries.logOf (bernoulliPowerSeries ℚ) = -PowerSeries.mk bernoulliLogCoefficient := by
  have hB := constantCoeff_bernoulliPowerSeries ℚ
  have hG : constantCoeff (SaddleExpansion.massSeries expm1DivCoefficient) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, SaddleExpansion.coeff_massSeries,
      expm1DivCoefficient_zero]
  have hGlog :
      PowerSeries.logOf (SaddleExpansion.massSeries expm1DivCoefficient) =
        PowerSeries.mk bernoulliLogCoefficient := by
    ext n
    rw [← SaddleExpansion.logSeries_eq_logOf expm1DivCoefficient expm1DivCoefficient_zero,
      SaddleExpansion.coeff_logSeries, coeff_mk, expm1Div_logCoeff_eq_bernoulli]
  have hsum : PowerSeries.logOf (bernoulliPowerSeries ℚ) +
      PowerSeries.logOf (SaddleExpansion.massSeries expm1DivCoefficient) = 0 := by
    rw [← Fabius.logOf_mul hB hG, bernoulliPowerSeries_mul_massSeries_expm1Div,
      PowerSeries.logOf_eq, sub_self, subst_zero_of_constantCoeff_zero constantCoeff_log]
  rw [hGlog] at hsum
  calc
    PowerSeries.logOf (bernoulliPowerSeries ℚ) =
        (PowerSeries.logOf (bernoulliPowerSeries ℚ) + PowerSeries.mk bernoulliLogCoefficient) -
          PowerSeries.mk bernoulliLogCoefficient := (add_sub_cancel_right _ _).symm
    _ = -PowerSeries.mk bernoulliLogCoefficient := by rw [hsum, zero_sub]

/-- Every coefficient of the normalized formal logarithm of the Bernoulli
kernel.  Positive degrees use `bernoulli'`, whose first value is `1/2`;
the constant coefficient is zero. -/
theorem coeff_logOf_bernoulliPowerSeries (n : ℕ) :
    coeff n (PowerSeries.logOf (bernoulliPowerSeries ℚ)) =
      if n = 0 then 0 else -(bernoulli' n / ((n : ℚ) * n.factorial)) := by
  rw [logOf_bernoulliPowerSeries, map_neg, coeff_mk, bernoulliLogCoefficient]
  split_ifs <;> simp only [neg_zero]

/-- The linear coefficient of `log(t/(exp(t)-1))` is `-1/2`. -/
theorem coeff_one_logOf_bernoulliPowerSeries :
    coeff 1 (PowerSeries.logOf (bernoulliPowerSeries ℚ)) = -(1 / 2 : ℚ) := by
  rw [coeff_logOf_bernoulliPowerSeries]
  norm_num [bernoulli'_one]

/-- From degree two onward the coefficient uses the ordinary Bernoulli
numbers: `[t^n] log(t/(exp(t)-1)) = -B_n/(n*n!)`. -/
theorem coeff_logOf_bernoulliPowerSeries_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    coeff n (PowerSeries.logOf (bernoulliPowerSeries ℚ)) =
      -(bernoulli n / ((n : ℚ) * n.factorial)) := by
  rw [coeff_logOf_bernoulliPowerSeries, if_neg (by omega),
    ← bernoulli_eq_bernoulli'_of_ne_one (by omega : n ≠ 1)]

section BaseChange

variable {A D : Type*} [CommRing A] [Algebra ℚ A] [CommRing D] [Algebra ℚ D]

/-- Coefficient base change commutes with the normalized formal logarithm.
The unit constant coefficient makes its defining substitution admissible. -/
theorem map_logOf (f : A →+* D) {s : A⟦X⟧} (hs : constantCoeff s = 1) :
    (PowerSeries.logOf s).map f = PowerSeries.logOf (s.map f) := by
  rw [PowerSeries.logOf_eq]
  calc
    ((log A).subst (s - 1)).map f =
        ((log A).map f).subst ((s - 1).map f) :=
      PowerSeries.map_subst (hasSubst_sub_one hs) (log A)
    _ = PowerSeries.logOf (s.map f) := by
      rw [PowerSeries.map_log, map_sub, map_one, ← PowerSeries.logOf_eq]

/-- The Bernoulli kernel is preserved by coefficient homomorphisms between
commutative rational algebras. -/
theorem map_bernoulliPowerSeries (f : A →+* D) :
    (bernoulliPowerSeries A).map f = bernoulliPowerSeries D := by
  ext n
  simp only [coeff_map, bernoulliPowerSeries, coeff_mk, RingHom.map_rat_algebraMap]

end BaseChange

section RationalAlgebra

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The formal logarithm of the Bernoulli kernel over any commutative
rational algebra is obtained by mapping its proved rational coefficients. -/
theorem logOf_bernoulliPowerSeries_algebra :
    PowerSeries.logOf (bernoulliPowerSeries A) =
      -PowerSeries.mk (fun n => algebraMap ℚ A (bernoulliLogCoefficient n)) := by
  have hB := constantCoeff_bernoulliPowerSeries ℚ
  have h := congrArg (PowerSeries.map (algebraMap ℚ A)) logOf_bernoulliPowerSeries
  rw [map_logOf _ hB, map_bernoulliPowerSeries, map_neg] at h
  calc
    PowerSeries.logOf (bernoulliPowerSeries A) =
        -(PowerSeries.mk bernoulliLogCoefficient).map (algebraMap ℚ A) := h
    _ = -PowerSeries.mk (fun n => algebraMap ℚ A (bernoulliLogCoefficient n)) := rfl

/-- Every coefficient of the normalized Bernoulli logarithm after base
change.  The constant term is zero; positive degrees use `bernoulli'`. -/
theorem coeff_logOf_bernoulliPowerSeries_algebra (n : ℕ) :
    coeff n (PowerSeries.logOf (bernoulliPowerSeries A)) =
      algebraMap ℚ A
        (if n = 0 then 0 else -(bernoulli' n / ((n : ℚ) * n.factorial))) := by
  rw [logOf_bernoulliPowerSeries_algebra, map_neg, coeff_mk, bernoulliLogCoefficient]
  split_ifs <;> simp only [map_zero, neg_zero, map_neg]

/-- In every degree at least two, the formal Bernoulli logarithm over a
commutative rational algebra uses the ordinary Bernoulli convention. -/
theorem coeff_logOf_bernoulliPowerSeries_algebra_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    coeff n (PowerSeries.logOf (bernoulliPowerSeries A)) =
      algebraMap ℚ A (-(bernoulli n / ((n : ℚ) * n.factorial))) := by
  rw [coeff_logOf_bernoulliPowerSeries_algebra, if_neg (by omega),
    ← bernoulli_eq_bernoulli'_of_ne_one (by omega : n ≠ 1)]

end RationalAlgebra

end Fabius

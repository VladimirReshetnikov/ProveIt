import FabiusFunction.LagrangeInversion
import FabiusFunction.LagrangeInversionUniqueness
import FabiusFunction.CauchyPolynomials
import FabiusFunction.BellComposition
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Offset Lagrange–Bürmann, the logarithmic diagonal, and low-order reversion

Three results of the combinatorial-coefficient-calculus manuscript, all formal-power-series
statements, all built on the corpus's Lagrange–Bürmann module `FabiusFunction.LagrangeInversion`
(which is not re-proved here).

## `thm:merged-offset-lagrange` (offset Lagrange–Bürmann)

The manuscript's `u = a + t Φ(u)`, `Φ(a) ≠ 0`, with `[t^n] H(u) = (1/n) [z^{n-1}] H'(a+z) Φ(a+z)^n`.
Its proof is the translation `w = u − a`, `φ(w) = Φ(a + w)`, `K(w) = H(a + w)`, after which the
statement *is* the basic Lagrange–Bürmann formula for `w = t φ(w)`.  The formalization choice:

* `Lagrange.coeff_subst_derivative_of_eq_C_add` is that reduction in the abstract: for any
  `a : R` and any series `Φa`, `Ha` (read as `Φ(a + w)`, `H(a + w)` — the translates are *given*),
  every `u` with `u = C a + X · Φa(u − C a)` and `Φa(u − C a)` invertible satisfies
  `n · [t^n] Ha(u − C a) = [z^{n-1}] Ha' · Φa^n`.  This is the manuscript proof verbatim.
* The translation itself, `Φ ↦ Φ(a + z)`, is not a power-series substitution in Mathlib's sense:
  `PowerSeries.subst` needs a nilpotent constant term and `C a + X` has constant term `a`.  So the
  concrete form takes `Φ` and `H` to be **polynomials**, where `Φ(a + z)` is `Polynomial.taylor a Φ`
  (`OffsetLagrange.taylorShift`) and `H(u)` is `Polynomial.aeval u H`.  Under `IsUnit (Φ.eval a)`
  (the manuscript's `Φ(a) ≠ 0`, in the form a general commutative `ℚ`-algebra needs) the solution
  `u` is *constructed* (`OffsetLagrange.offsetSolution`), satisfies the equation
  (`offsetSolution_eq`), is the unique such series (`eq_offsetSolution_of_eq`), and obeys
  `n · [t^n] H(u) = [z^{n-1}] H'(a+z) Φ(a+z)^n` (`natCast_mul_coeff_aeval_offsetSolution`) together
  with the divided form (`coeff_aeval_offsetSolution`).
* Uniqueness rests on the corpus's `Lagrange.eq_solution_of_eq_X_mul_subst`
  (`FabiusFunction.LagrangeInversionUniqueness`): every solution of `g = z φ(g)` is the canonical
  `Lagrange.solution`.

The manuscript's analytic clause (convergence of the same formula for analytic `H`, `Φ`) is not
formalized: it is an analytic inverse-function-theorem statement, outside the scope of this
formal-power-series module.

## `prop:merged-cauchy-diagonal` (logarithmic diagonal)

`[x^{n-1}] (x/log(1+x))^n = 1/(n-1)!`, over `ℚ`.  The compositional inverse of `log(1+x)` is
`e^x − 1`, whose coefficients are `1/n!`; the corpus already has `x/log(1+x)` as
`Fabius.tOverLog`, its reciprocal `logDivSeries ℚ`, and `log_subst_exp_sub_one`.  The equation
`e^t − 1 = t · φ(e^t − 1)` with `φ = tOverLog` (`exp_sub_one_eq_X_mul_tOverLog_subst`) is the
Lagrange functional equation, and `Lagrange.coeff_subst_id` gives `n · [t^n](e^t − 1) = [t^{n-1}] φ^n`
directly: `coeff_tOverLog_pow_eq_div_factorial` (`= n/n!`) and `coeff_tOverLog_pow` (`= 1/(n-1)!`).

## `prop:merged-low-order-reversion` (direct reversion through degree five)

For `F = z + a₂z² + a₃z³ + a₄z⁴ + a₅z⁵ + O(z⁶)` the compositional inverse is
`z − a₂z² + (2a₂² − a₃)z³ + (−5a₂³ + 5a₂a₃ − a₄)z⁴ + (14a₂⁴ − 21a₂²a₃ + 3a₃² + 6a₂a₄ − a₅)z⁵ + O(z⁶)`.
The manuscript's undetermined-coefficients proof is followed exactly: writing the inverse as
`G = X · Q`, the coefficients of `F(G)` through degree five are read off the truncated
substitution expansion (`LowOrderReversion.coeff_subst_eq_sum`, from the corpus's
`coeff_mul_subst_eq`) and the explicit low-order product coefficients (`coeff_one_mul_eq`,
`coeff_two_mul_eq`, `coeff_three_mul_eq`); the triangular system is then solved.  The statement is
proved for *any* right inverse `G` with zero constant term (`coeff_of_subst_eq_X` and its four
projections), and specialized to Mathlib's `PowerSeries.substInvOfIsUnit`
(`normalizedInverse`, `coeff_two_normalizedInverse`, …, `coeff_five_normalizedInverse`).  As the
manuscript remarks, no division occurs, so this section is over an arbitrary commutative ring
rather than a `ℚ`-algebra.  The four displayed polynomials were checked symbolically (sympy)
before being proved; they are correct as printed.

## Main results

* `Lagrange.coeff_subst_derivative_of_eq_C_add`.
* `OffsetLagrange.taylorShift`, `subst_taylorShift`, `derivative_taylorShift`,
  `constantCoeff_taylorShift`, `offsetSolution`, `offsetSolution_eq`, `eq_offsetSolution_of_eq`,
  `natCast_mul_coeff_aeval_offsetSolution`, `coeff_aeval_offsetSolution`.
* `exp_sub_one_eq_X_mul_tOverLog_subst`, `coeff_tOverLog_pow_eq_div_factorial`,
  `coeff_tOverLog_pow`.
* `LowOrderReversion.coeff_of_subst_eq_X`, `coeff_two_of_subst_eq_X`, …,
  `coeff_five_of_subst_eq_X`, `normalizedInverse`, `coeff_two_normalizedInverse`, …,
  `coeff_five_normalizedInverse`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

/-! ### The abstract offset form -/

namespace Lagrange

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- **`thm:merged-offset-lagrange`, abstract translation form.**  If `Φa` and `Ha` are the
translates `Φ(a + w)`, `H(a + w)` (given as series), and `u = a + t Φa(u − a)` with `Φa(u − a)`
invertible, then `n · [t^n] Ha(u − a) = [z^{n-1}] Ha'(z) Φa(z)^n`.  This is the manuscript's proof:
put `w = u − a` and apply Lagrange–Bürmann to `w = t Φa(w)`. -/
theorem coeff_subst_derivative_of_eq_C_add {a : R} {Φa Ha u v : R⟦X⟧}
    (hu : u = PowerSeries.C a + X * Φa.subst (u - PowerSeries.C a))
    (hv : Φa.subst (u - PowerSeries.C a) * v = 1) (n : ℕ) (hn : 1 ≤ n) :
    (n : R) * coeff n (Ha.subst (u - PowerSeries.C a)) =
      coeff (n - 1) (d⁄dX R Ha * Φa ^ n) := by
  have hg : u - PowerSeries.C a = X * Φa.subst (u - PowerSeries.C a) := by
    linear_combination hu
  exact coeff_subst_derivative hg rfl hv Ha n hn

end Lagrange

/-! ### The offset equation for polynomial data -/

namespace OffsetLagrange

variable {R : Type*} [CommRing R] [Algebra ℚ R]
variable (a : R)

/-- The translate `H(a + z)` of a polynomial `H`, as a power series: `Polynomial.taylor a H`
coerced into `R⟦X⟧`. -/
noncomputable def taylorShift (H : Polynomial R) : R⟦X⟧ :=
  ((Polynomial.taylor a H : Polynomial R) : R⟦X⟧)

/-- The constant term of `Φ(a + z)` is `Φ(a)`. -/
theorem constantCoeff_taylorShift (H : Polynomial R) :
    constantCoeff (taylorShift a H) = H.eval a := by
  rw [taylorShift, Polynomial.constantCoeff_coe, Polynomial.taylor_coeff_zero]

/-- Substituting a series `g` with zero constant term into `H(a + z)` evaluates `H` at `a + g`. -/
theorem subst_taylorShift {g : R⟦X⟧} (hg : HasSubst g) (H : Polynomial R) :
    (taylorShift a H).subst g = Polynomial.aeval (PowerSeries.C a + g) H := by
  have hX : Polynomial.aeval g (Polynomial.X + Polynomial.C a) = PowerSeries.C a + g := by
    rw [Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
      ← PowerSeries.C_eq_algebraMap, add_comm]
  rw [taylorShift, subst_coe hg, Polynomial.taylor_apply, Polynomial.aeval_comp, hX]

/-- The derivative of the translate is the translate of the derivative:
`(H(a + z))' = H'(a + z)`. -/
theorem derivative_taylorShift (H : Polynomial R) :
    d⁄dX R (taylorShift a H) = taylorShift a (Polynomial.derivative H) := by
  unfold taylorShift
  rw [derivative_coe, Polynomial.taylor_apply, Polynomial.taylor_apply,
    Polynomial.derivative_comp, Polynomial.derivative_X_add_C, one_mul]

variable (Φ : Polynomial R)

/-- The reciprocal of the weight `Φ(a + z)`, which exists because `Φ(a)` is a unit. -/
noncomputable def taylorShiftInv (hΦ : IsUnit (Φ.eval a)) : R⟦X⟧ :=
  PowerSeries.invOfUnit (taylorShift a Φ) hΦ.unit

/-- `Φ(a + z) · Φ(a + z)⁻¹ = 1`, the hypothesis the unconditional Lagrange API needs. -/
theorem taylorShift_mul_taylorShiftInv (hΦ : IsUnit (Φ.eval a)) :
    taylorShift a Φ * taylorShiftInv a Φ hΦ = 1 := by
  unfold taylorShiftInv
  exact PowerSeries.mul_invOfUnit _ _
    (by rw [constantCoeff_taylorShift]; exact hΦ.unit_spec.symm)

/-- **The solution `u` of `u = a + t Φ(u)`**, constructed as `a` plus the canonical Lagrange
solution of `w = t Φ(a + w)`. -/
noncomputable def offsetSolution (hΦ : IsUnit (Φ.eval a)) : R⟦X⟧ :=
  PowerSeries.C a +
    Lagrange.solution (taylorShift a Φ) (taylorShiftInv a Φ hΦ)
      (taylorShift_mul_taylorShiftInv a Φ hΦ)

/-- The unfolding lemma for `offsetSolution` (a definition with arguments does not fold under
`rw [← offsetSolution]`). -/
theorem offsetSolution_def (hΦ : IsUnit (Φ.eval a)) :
    offsetSolution a Φ hΦ = PowerSeries.C a +
      Lagrange.solution (taylorShift a Φ) (taylorShiftInv a Φ hΦ)
        (taylorShift_mul_taylorShiftInv a Φ hΦ) := rfl

/-- **The functional equation** `u = a + t Φ(u)`. -/
theorem offsetSolution_eq (hΦ : IsUnit (Φ.eval a)) :
    offsetSolution a Φ hΦ = PowerSeries.C a + X * Polynomial.aeval (offsetSolution a Φ hΦ) Φ := by
  have hs := Lagrange.hasSubst_solution (taylorShift a Φ) (taylorShiftInv a Φ hΦ)
    (taylorShift_mul_taylorShiftInv a Φ hΦ)
  have heq := Lagrange.solution_eq (taylorShift a Φ) (taylorShiftInv a Φ hΦ)
    (taylorShift_mul_taylorShiftInv a Φ hΦ)
  rw [subst_taylorShift a hs Φ, ← offsetSolution_def a Φ hΦ] at heq
  exact congrArg (fun z => PowerSeries.C a + z) heq

/-- The constant term of the solution is `a`. -/
theorem constantCoeff_offsetSolution (hΦ : IsUnit (Φ.eval a)) :
    constantCoeff (offsetSolution a Φ hΦ) = a := by
  rw [offsetSolution_def, map_add, constantCoeff_C, Lagrange.solution,
    constantCoeff_substInvOfIsUnit, add_zero]

/-- **Uniqueness:** every series `u` with `u = a + t Φ(u)` is `offsetSolution`. -/
theorem eq_offsetSolution_of_eq (hΦ : IsUnit (Φ.eval a)) {u : R⟦X⟧}
    (hu : u = PowerSeries.C a + X * Polynomial.aeval u Φ) : u = offsetSolution a Φ hΦ := by
  have hc : constantCoeff (u - PowerSeries.C a) = 0 := by
    rw [map_sub, constantCoeff_C, hu, map_add, constantCoeff_C, Lagrange.constantCoeff_X_mul,
      add_zero, sub_self]
  have hs : HasSubst (u - PowerSeries.C a) := HasSubst.of_constantCoeff_zero' hc
  have hcancel : PowerSeries.C a + (u - PowerSeries.C a) = u := by ring
  have hg : u - PowerSeries.C a = X * (taylorShift a Φ).subst (u - PowerSeries.C a) := by
    rw [subst_taylorShift a hs Φ, hcancel]
    linear_combination hu
  have h := Lagrange.eq_solution_of_eq_X_mul_subst (taylorShift_mul_taylorShiftInv a Φ hΦ) hg
  rw [offsetSolution_def, ← h]
  ring

/-- **`thm:merged-offset-lagrange`, division-free form, for polynomial `Φ` and `H`:**
`n · [t^n] H(u) = [z^{n-1}] H'(a + z) Φ(a + z)^n`, where `u = a + t Φ(u)`. -/
theorem natCast_mul_coeff_aeval_offsetSolution (hΦ : IsUnit (Φ.eval a)) (H : Polynomial R)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : R) * coeff n (Polynomial.aeval (offsetSolution a Φ hΦ) H) =
      coeff (n - 1) (taylorShift a (Polynomial.derivative H) * taylorShift a Φ ^ n) := by
  have hs := Lagrange.hasSubst_solution (taylorShift a Φ) (taylorShiftInv a Φ hΦ)
    (taylorShift_mul_taylorShiftInv a Φ hΦ)
  have hmain := Lagrange.coeff_solution_subst_derivative (taylorShift a Φ) (taylorShiftInv a Φ hΦ)
    (taylorShift_mul_taylorShiftInv a Φ hΦ) (taylorShift a H) n hn
  rw [subst_taylorShift a hs H, ← offsetSolution_def a Φ hΦ, derivative_taylorShift a H] at hmain
  exact hmain

/-- **`thm:merged-offset-lagrange`, divided form:**
`[t^n] H(u) = (1/n) [z^{n-1}] H'(a + z) Φ(a + z)^n`. -/
theorem coeff_aeval_offsetSolution (hΦ : IsUnit (Φ.eval a)) (H : Polynomial R)
    (n : ℕ) (hn : 1 ≤ n) :
    coeff n (Polynomial.aeval (offsetSolution a Φ hΦ) H) =
      algebraMap ℚ R (1 / (n : ℚ)) *
        coeff (n - 1) (taylorShift a (Polynomial.derivative H) * taylorShift a Φ ^ n) := by
  have h := natCast_mul_coeff_aeval_offsetSolution a Φ hΦ H n hn
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hinv : algebraMap ℚ R (1 / (n : ℚ)) * (n : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R) n, ← map_mul, one_div, inv_mul_cancel₀ hnQ, map_one]
  calc coeff n (Polynomial.aeval (offsetSolution a Φ hΦ) H)
      = (algebraMap ℚ R (1 / (n : ℚ)) * (n : R)) *
          coeff n (Polynomial.aeval (offsetSolution a Φ hΦ) H) := by rw [hinv, one_mul]
    _ = algebraMap ℚ R (1 / (n : ℚ)) *
          ((n : R) * coeff n (Polynomial.aeval (offsetSolution a Φ hΦ) H)) := by rw [mul_assoc]
    _ = algebraMap ℚ R (1 / (n : ℚ)) *
          coeff (n - 1) (taylorShift a (Polynomial.derivative H) * taylorShift a Φ ^ n) := by
        rw [h]

end OffsetLagrange

/-! ### The logarithmic diagonal -/

/-- `φ(e^t − 1)` is invertible, with inverse `(log(1+t)/t)(e^t − 1)`, where `φ = t/log(1+t)`. -/
theorem tOverLog_subst_mul_logDivSeries_subst :
    tOverLog.subst (exp ℚ - 1) * (logDivSeries ℚ).subst (exp ℚ - 1) = 1 := by
  have hE : HasSubst (exp ℚ - 1) := HasSubst.exp_sub_one
  rw [← subst_mul hE, mul_comm, logDivSeries_mul_tOverLog, ← coe_substAlgHom hE, map_one]

/-- `(e^t − 1) · (log(1+t)/t)(e^t − 1) = t`, which is `log(1 + (e^t − 1)) = t` with the factor
`t` of the logarithm split off. -/
theorem exp_sub_one_mul_logDivSeries_subst :
    (exp ℚ - 1) * (logDivSeries ℚ).subst (exp ℚ - 1) = X := by
  have hE : HasSubst (exp ℚ - 1) := HasSubst.exp_sub_one
  have h := log_subst_exp_sub_one (A := ℚ)
  rw [← X_mul_logDivSeries (A := ℚ), subst_mul hE, subst_X hE] at h
  exact h

/-- `e^t − 1 = t · φ(e^t − 1)` with `φ = t/log(1+t)`: the Lagrange functional equation whose
solution is `e^t − 1`, because `log(1 + (e^t − 1)) = t`. -/
theorem exp_sub_one_eq_X_mul_tOverLog_subst :
    exp ℚ - 1 = X * tOverLog.subst (exp ℚ - 1) := by
  calc exp ℚ - 1
      = (exp ℚ - 1) * (tOverLog.subst (exp ℚ - 1) * (logDivSeries ℚ).subst (exp ℚ - 1)) := by
        rw [tOverLog_subst_mul_logDivSeries_subst, mul_one]
    _ = ((exp ℚ - 1) * (logDivSeries ℚ).subst (exp ℚ - 1)) * tOverLog.subst (exp ℚ - 1) := by
        ring
    _ = X * tOverLog.subst (exp ℚ - 1) := by rw [exp_sub_one_mul_logDivSeries_subst]

/-- **`prop:merged-cauchy-diagonal`, as Lagrange inversion delivers it:**
`[x^{n-1}] (x/log(1+x))^n = n · [t^n](e^t − 1) = n/n!`. -/
theorem coeff_tOverLog_pow_eq_div_factorial (n : ℕ) (hn : 1 ≤ n) :
    coeff (n - 1) (tOverLog ^ n) = (n : ℚ) / (n.factorial : ℚ) := by
  have h := Lagrange.coeff_subst_id exp_sub_one_eq_X_mul_tOverLog_subst rfl
    tOverLog_subst_mul_logDivSeries_subst n hn
  have hc : coeff n (exp ℚ - 1) = 1 / (n.factorial : ℚ) := by
    rw [map_sub, coeff_exp, coeff_one, if_neg (by omega), sub_zero, Algebra.algebraMap_self_apply]
  rw [← h, hc, mul_one_div]

/-- **`prop:merged-cauchy-diagonal`.**  `[x^{n-1}] (x/log(1+x))^n = 1/(n-1)!` for `n ≥ 1`. -/
theorem coeff_tOverLog_pow (n : ℕ) (hn : 1 ≤ n) :
    coeff (n - 1) (tOverLog ^ n) = 1 / ((n - 1).factorial : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [coeff_tOverLog_pow_eq_div_factorial (m + 1) hn, Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hm1 : ((m : ℚ) + 1) ≠ 0 := by positivity
  rw [← div_div, div_self hm1]

/-! ### Direct reversion through degree five -/

namespace LowOrderReversion

variable {R : Type*} [CommRing R]

/-- `[X¹](p q) = p₀ q₁ + p₁ q₀`. -/
theorem coeff_one_mul_eq (p q : R⟦X⟧) :
    coeff 1 (p * q) = coeff 0 p * coeff 1 q + coeff 1 p * coeff 0 q := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ] <;> ring

/-- `[X²](p q) = p₀ q₂ + p₁ q₁ + p₂ q₀`. -/
theorem coeff_two_mul_eq (p q : R⟦X⟧) :
    coeff 2 (p * q) = coeff 0 p * coeff 2 q + coeff 1 p * coeff 1 q + coeff 2 p * coeff 0 q := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ] <;> ring

/-- `[X³](p q) = p₀ q₃ + p₁ q₂ + p₂ q₁ + p₃ q₀`. -/
theorem coeff_three_mul_eq (p q : R⟦X⟧) :
    coeff 3 (p * q) = coeff 0 p * coeff 3 q + coeff 1 p * coeff 2 q + coeff 2 p * coeff 1 q +
      coeff 3 p * coeff 0 q := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ] <;> ring

/-- The truncated substitution expansion, `[X^k] F(G) = ∑_{d ≤ k} [X^d] F · [X^k] G^d`, when `G`
has zero constant term (the `g = 1` case of the corpus's `coeff_mul_subst_eq`). -/
theorem coeff_subst_eq_sum {G : R⟦X⟧} (hG : constantCoeff G = 0) (F : R⟦X⟧) (k : ℕ) :
    coeff k (F.subst G) = ∑ d ∈ Finset.range (k + 1), coeff d F * coeff k (G ^ d) := by
  have h := coeff_mul_subst_eq R hG 1 F k
  simpa only [one_mul] using h

/-- **`prop:merged-low-order-reversion`, for any right inverse.**  If `F` has constant term `0`
and linear coefficient `1`, then every `G` with zero constant term and `F(G) = X` has
`[X¹] G = 1`, `[X²] G = −a₂`, `[X³] G = 2a₂² − a₃`, `[X⁴] G = −5a₂³ + 5a₂a₃ − a₄` and
`[X⁵] G = 14a₂⁴ − 21a₂²a₃ + 3a₃² + 6a₂a₄ − a₅`, where `aᵢ = [Xⁱ] F`.  The proof is the
manuscript's: write `G = X·Q`, expand `F(G)` through degree five, and solve the triangular
system. -/
theorem coeff_of_subst_eq_X {F G : R⟦X⟧} (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1)
    (hG : constantCoeff G = 0) (hFG : F.subst G = X) :
    coeff 1 G = 1 ∧
    coeff 2 G = -coeff 2 F ∧
    coeff 3 G = 2 * coeff 2 F ^ 2 - coeff 3 F ∧
    coeff 4 G = -(5 * coeff 2 F ^ 3) + 5 * coeff 2 F * coeff 3 F - coeff 4 F ∧
    coeff 5 G = 14 * coeff 2 F ^ 4 - 21 * coeff 2 F ^ 2 * coeff 3 F + 3 * coeff 3 F ^ 2 +
      6 * coeff 2 F * coeff 4 F - coeff 5 F := by
  obtain ⟨Q, hQ⟩ := X_dvd_iff.mpr hG
  -- coefficients of `G` and of the powers `G^d = X^d Q^d`
  have hGc : ∀ i : ℕ, coeff (i + 1) G = coeff i Q := fun i => by rw [hQ, coeff_succ_X_mul]
  have hpow : ∀ k d : ℕ, coeff (k + d) (G ^ d) = coeff k (Q ^ d) := fun k d => by
    rw [hQ, mul_pow, coeff_X_pow_mul', if_pos (Nat.le_add_left d k), Nat.add_sub_cancel]
  have hG1 : coeff 1 G = coeff 0 Q := hGc 0
  have hG2 : coeff 2 G = coeff 1 Q := hGc 1
  have hG3 : coeff 3 G = coeff 2 Q := hGc 2
  have hG4 : coeff 4 G = coeff 3 Q := hGc 3
  have hG5 : coeff 5 G = coeff 4 Q := hGc 4
  have hp11 : coeff 1 (G ^ 1) = coeff 0 (Q ^ 1) := hpow 0 1
  have hp21 : coeff 2 (G ^ 1) = coeff 1 (Q ^ 1) := hpow 1 1
  have hp22 : coeff 2 (G ^ 2) = coeff 0 (Q ^ 2) := hpow 0 2
  have hp31 : coeff 3 (G ^ 1) = coeff 2 (Q ^ 1) := hpow 2 1
  have hp32 : coeff 3 (G ^ 2) = coeff 1 (Q ^ 2) := hpow 1 2
  have hp33 : coeff 3 (G ^ 3) = coeff 0 (Q ^ 3) := hpow 0 3
  have hp41 : coeff 4 (G ^ 1) = coeff 3 (Q ^ 1) := hpow 3 1
  have hp42 : coeff 4 (G ^ 2) = coeff 2 (Q ^ 2) := hpow 2 2
  have hp43 : coeff 4 (G ^ 3) = coeff 1 (Q ^ 3) := hpow 1 3
  have hp44 : coeff 4 (G ^ 4) = coeff 0 (Q ^ 4) := hpow 0 4
  have hp51 : coeff 5 (G ^ 1) = coeff 4 (Q ^ 1) := hpow 4 1
  have hp52 : coeff 5 (G ^ 2) = coeff 3 (Q ^ 2) := hpow 3 2
  have hp53 : coeff 5 (G ^ 3) = coeff 2 (Q ^ 3) := hpow 2 3
  have hp54 : coeff 5 (G ^ 4) = coeff 1 (Q ^ 4) := hpow 1 4
  have hp55 : coeff 5 (G ^ 5) = coeff 0 (Q ^ 5) := hpow 0 5
  -- the data of `F` and of `X`
  have hF0' : coeff 0 F = 0 := by rw [coeff_zero_eq_constantCoeff_apply]; exact hF0
  have hX : ∀ k : ℕ, 2 ≤ k → coeff k (X : R⟦X⟧) = 0 := fun k hk => by
    rw [coeff_X, if_neg (by omega)]
  have hX2 : coeff 2 (X : R⟦X⟧) = 0 := hX 2 (by norm_num)
  have hX3 : coeff 3 (X : R⟦X⟧) = 0 := hX 3 (by norm_num)
  have hX4 : coeff 4 (X : R⟦X⟧) = 0 := hX 4 (by norm_num)
  have hX5 : coeff 5 (X : R⟦X⟧) = 0 := hX 5 (by norm_num)
  have heq : ∀ k : ℕ, coeff k (F.subst G) = coeff k X := fun k => by rw [hFG]
  -- degree 1: `Q` has constant term `1`
  have e1 : coeff 0 Q = 1 := by
    have h := heq 1
    rw [coeff_subst_eq_sum hG, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hp11] at h
    simp only [hF0', hF1, zero_mul, zero_add, one_mul, pow_one, coeff_one_X] at h
    linear_combination h
  -- the low-order coefficients of the powers of `Q`
  have q0 : ∀ d : ℕ, coeff 0 (Q ^ d) = 1 := fun d => by
    rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply, e1,
      one_pow]
  have q12 : coeff 1 (Q ^ 2) = 2 * coeff 1 Q := by
    rw [pow_two, coeff_one_mul_eq, e1]; ring
  have q22 : coeff 2 (Q ^ 2) = 2 * coeff 2 Q + coeff 1 Q ^ 2 := by
    rw [pow_two, coeff_two_mul_eq, e1]; ring
  have q32 : coeff 3 (Q ^ 2) = 2 * coeff 3 Q + 2 * coeff 1 Q * coeff 2 Q := by
    rw [pow_two, coeff_three_mul_eq, e1]; ring
  have q13 : coeff 1 (Q ^ 3) = 3 * coeff 1 Q := by
    rw [pow_succ, coeff_one_mul_eq, q0, q12, e1]; ring
  have q23 : coeff 2 (Q ^ 3) = 3 * coeff 2 Q + 3 * coeff 1 Q ^ 2 := by
    rw [pow_succ, coeff_two_mul_eq, q0, q12, q22, e1]; ring
  have q14 : coeff 1 (Q ^ 4) = 4 * coeff 1 Q := by
    rw [pow_succ, coeff_one_mul_eq, q0, q13, e1]; ring
  -- degree 2
  have e2 : coeff 1 Q = -coeff 2 F := by
    have h := heq 2
    rw [coeff_subst_eq_sum hG, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hp21, hp22, hX2] at h
    simp only [hF0', hF1, zero_mul, zero_add, one_mul, mul_one, pow_one, q0] at h
    linear_combination h
  -- degree 3
  have e3 : coeff 2 Q = 2 * coeff 2 F ^ 2 - coeff 3 F := by
    have h := heq 3
    rw [coeff_subst_eq_sum hG, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      hp31, hp32, hp33, hX3] at h
    simp only [hF0', hF1, zero_mul, zero_add, one_mul, mul_one, pow_one, q0, q12, e2] at h
    linear_combination h
  -- degree 4
  have e4 : coeff 3 Q = -(5 * coeff 2 F ^ 3) + 5 * coeff 2 F * coeff 3 F - coeff 4 F := by
    have h := heq 4
    rw [coeff_subst_eq_sum hG, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, zero_add, hp41, hp42, hp43, hp44, hX4] at h
    simp only [hF0', hF1, zero_mul, zero_add, one_mul, mul_one, pow_one, q0, q22, q13, e2,
      e3] at h
    linear_combination h
  -- degree 5
  have e5 : coeff 4 Q = 14 * coeff 2 F ^ 4 - 21 * coeff 2 F ^ 2 * coeff 3 F + 3 * coeff 3 F ^ 2 +
      6 * coeff 2 F * coeff 4 F - coeff 5 F := by
    have h := heq 5
    rw [coeff_subst_eq_sum hG, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero, zero_add, hp51, hp52, hp53, hp54, hp55,
      hX5] at h
    simp only [hF0', hF1, zero_mul, zero_add, one_mul, mul_one, pow_one, q0, q32, q23, q14, e2,
      e3, e4] at h
    linear_combination h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hG1, e1]
  · rw [hG2, e2]
  · rw [hG3, e3]
  · rw [hG4, e4]
  · rw [hG5, e5]

/-- `[X¹] G = 1` for any right inverse `G` of a normalized `F`. -/
theorem coeff_one_of_subst_eq_X {F G : R⟦X⟧} (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1)
    (hG : constantCoeff G = 0) (hFG : F.subst G = X) : coeff 1 G = 1 :=
  (coeff_of_subst_eq_X hF0 hF1 hG hFG).1

/-- `[X²] G = −a₂`. -/
theorem coeff_two_of_subst_eq_X {F G : R⟦X⟧} (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1)
    (hG : constantCoeff G = 0) (hFG : F.subst G = X) : coeff 2 G = -coeff 2 F :=
  (coeff_of_subst_eq_X hF0 hF1 hG hFG).2.1

/-- `[X³] G = 2a₂² − a₃`. -/
theorem coeff_three_of_subst_eq_X {F G : R⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F = 1) (hG : constantCoeff G = 0) (hFG : F.subst G = X) :
    coeff 3 G = 2 * coeff 2 F ^ 2 - coeff 3 F :=
  (coeff_of_subst_eq_X hF0 hF1 hG hFG).2.2.1

/-- `[X⁴] G = −5a₂³ + 5a₂a₃ − a₄`. -/
theorem coeff_four_of_subst_eq_X {F G : R⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F = 1) (hG : constantCoeff G = 0) (hFG : F.subst G = X) :
    coeff 4 G = -(5 * coeff 2 F ^ 3) + 5 * coeff 2 F * coeff 3 F - coeff 4 F :=
  (coeff_of_subst_eq_X hF0 hF1 hG hFG).2.2.2.1

/-- `[X⁵] G = 14a₂⁴ − 21a₂²a₃ + 3a₃² + 6a₂a₄ − a₅`. -/
theorem coeff_five_of_subst_eq_X {F G : R⟦X⟧} (hF0 : constantCoeff F = 0)
    (hF1 : coeff 1 F = 1) (hG : constantCoeff G = 0) (hFG : F.subst G = X) :
    coeff 5 G = 14 * coeff 2 F ^ 4 - 21 * coeff 2 F ^ 2 * coeff 3 F + 3 * coeff 3 F ^ 2 +
      6 * coeff 2 F * coeff 4 F - coeff 5 F :=
  (coeff_of_subst_eq_X hF0 hF1 hG hFG).2.2.2.2

/-! #### Mathlib's compositional inverse -/

variable (F : R⟦X⟧)

/-- **The compositional inverse** of a series `F = z + a₂z² + …` (constant term `0`, linear
coefficient `1`): Mathlib's `PowerSeries.substInvOfIsUnit`, whose unit hypothesis is trivial. -/
noncomputable def normalizedInverse (hF1 : coeff 1 F = 1) : R⟦X⟧ :=
  substInvOfIsUnit F (by rw [hF1]; exact isUnit_one)

/-- The inverse has zero constant term. -/
theorem constantCoeff_normalizedInverse (hF1 : coeff 1 F = 1) :
    constantCoeff (normalizedInverse F hF1) = 0 := by
  unfold normalizedInverse
  exact constantCoeff_substInvOfIsUnit F _

/-- `F(G) = X` for the compositional inverse `G`. -/
theorem subst_normalizedInverse (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1) :
    F.subst (normalizedInverse F hF1) = X := by
  unfold normalizedInverse
  exact subst_substInvOfIsUnit_right F hF0 _

/-- **`prop:merged-low-order-reversion`, `[X²]`:** `[X²] F⁻¹ = −a₂`. -/
theorem coeff_two_normalizedInverse (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1) :
    coeff 2 (normalizedInverse F hF1) = -coeff 2 F :=
  coeff_two_of_subst_eq_X hF0 hF1 (constantCoeff_normalizedInverse F hF1)
    (subst_normalizedInverse F hF0 hF1)

/-- **`prop:merged-low-order-reversion`, `[X³]`:** `[X³] F⁻¹ = 2a₂² − a₃`. -/
theorem coeff_three_normalizedInverse (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1) :
    coeff 3 (normalizedInverse F hF1) = 2 * coeff 2 F ^ 2 - coeff 3 F :=
  coeff_three_of_subst_eq_X hF0 hF1 (constantCoeff_normalizedInverse F hF1)
    (subst_normalizedInverse F hF0 hF1)

/-- **`prop:merged-low-order-reversion`, `[X⁴]`:** `[X⁴] F⁻¹ = −5a₂³ + 5a₂a₃ − a₄`. -/
theorem coeff_four_normalizedInverse (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1) :
    coeff 4 (normalizedInverse F hF1) =
      -(5 * coeff 2 F ^ 3) + 5 * coeff 2 F * coeff 3 F - coeff 4 F :=
  coeff_four_of_subst_eq_X hF0 hF1 (constantCoeff_normalizedInverse F hF1)
    (subst_normalizedInverse F hF0 hF1)

/-- **`prop:merged-low-order-reversion`, `[X⁵]`:**
`[X⁵] F⁻¹ = 14a₂⁴ − 21a₂²a₃ + 3a₃² + 6a₂a₄ − a₅`. -/
theorem coeff_five_normalizedInverse (hF0 : constantCoeff F = 0) (hF1 : coeff 1 F = 1) :
    coeff 5 (normalizedInverse F hF1) =
      14 * coeff 2 F ^ 4 - 21 * coeff 2 F ^ 2 * coeff 3 F + 3 * coeff 3 F ^ 2 +
        6 * coeff 2 F * coeff 4 F - coeff 5 F :=
  coeff_five_of_subst_eq_X hF0 hF1 (constantCoeff_normalizedInverse F hF1)
    (subst_normalizedInverse F hF0 hF1)

end LowOrderReversion

end Fabius

import PolynomialFormulas.QuinticRadicalPrimrec

/-!
# Executable coefficient infrastructure for integer sextics

This file supplies the degree-six analogue of the elementary coefficient layer
used by the verified quintic decision.  It deliberately stops before the two
imprimitivity resolvents: those are built in later modules.

An arbitrary integer sextic is represented by seven coefficients.  When its
leading coefficient is nonzero, `monicize` constructs the integral monic
sextic

`F(Y) = Y⁶ + a₅Y⁵ + a₄a₆Y⁴ + ⋯ + a₀a₆⁵`,

which satisfies `F(a₆x) = a₆⁵ f(x)`.  The construction is proved primitive
recursive coordinate by coordinate.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.SexticRadicalDecidability

open QuinticRadicalDecidability
open QuinticRadicalPrimrec

/-- Coefficients `a₀, ..., a₆` of an integer polynomial, in ascending order. -/
abbrev Coefficients := QuinticRadicalDecidability.IntegerSextic

namespace Coefficients

/-- Exact degree-six inputs have a nonzero final coefficient. -/
def IsSextic (a : Coefficients) : Prop := a 6 ≠ 0

/-- Executable recognition of exact degree-six inputs. -/
def isSexticB (a : Coefficients) : Bool := !decide (a 6 = 0)

@[simp] theorem isSexticB_eq_true (a : Coefficients) :
    a.isSexticB = true ↔ a.IsSextic := by
  simp [isSexticB, IsSextic]

theorem isSexticB_primrec : Primrec isSexticB := by
  have hzero : PrimrecPred (fun a : Coefficients ↦ a 6 = 0) :=
    Primrec.eq.comp
      (QuinticRadicalPrimrec.IntegerSextic.coeff_primrec 6)
      (Primrec.const 0)
  change Primrec fun a : Coefficients ↦ !decide (a 6 = 0)
  exact hzero.not.decide.of_eq fun a ↦ by simp

/-- The rational polynomial represented by the integer coefficient tuple. -/
noncomputable def ratPolynomial (a : Coefficients) : ℚ[X] :=
  a.polynomial.map (Int.castRingHom ℚ)

theorem ratPolynomial_natDegree_eq_six (a : Coefficients) (ha : a.IsSextic) :
    a.ratPolynomial.natDegree = 6 := by
  rw [ratPolynomial, natDegree_map_eq_of_injective]
  · exact a.polynomial_natDegree_eq_six ha
  · exact Int.cast_injective

end Coefficients

/-! ## Integral monic sextics -/

/-- The six nonleading coefficients of a monic integral sextic. -/
abbrev MonicSextic := Fin 6 → ℤ

namespace MonicSextic

/-- The monic polynomial `X⁶ + b₅X⁵ + ⋯ + b₀`. -/
noncomputable def polynomial (f : MonicSextic) : ℤ[X] :=
  X ^ 6 + Polynomial.C (f 5) * X ^ 5 + Polynomial.C (f 4) * X ^ 4 +
    Polynomial.C (f 3) * X ^ 3 + Polynomial.C (f 2) * X ^ 2 +
    Polynomial.C (f 1) * X + Polynomial.C (f 0)

/-- Direct evaluation of a monic sextic in a rational argument. -/
def evalRat (f : MonicSextic) (x : ℚ) : ℚ :=
  x ^ 6 + ∑ i : Fin 6, f i * x ^ (i : ℕ)

@[simp] theorem polynomial_aeval (f : MonicSextic) (x : ℚ) :
    aeval x f.polynomial = f.evalRat x := by
  simp [polynomial, evalRat, Fin.sum_univ_succ]
  ring

theorem polynomial_monic (f : MonicSextic) : f.polynomial.Monic := by
  simp only [polynomial]
  monicity!

theorem polynomial_natDegree (f : MonicSextic) : f.polynomial.natDegree = 6 := by
  simp only [polynomial]
  compute_degree!

/-- The rational image of a monic integral sextic. -/
noncomputable def ratPolynomial (f : MonicSextic) : ℚ[X] :=
  f.polynomial.map (Int.castRingHom ℚ)

theorem ratPolynomial_monic (f : MonicSextic) : f.ratPolynomial.Monic :=
  f.polynomial_monic.map _

theorem ratPolynomial_natDegree (f : MonicSextic) :
    f.ratPolynomial.natDegree = 6 := by
  rw [ratPolynomial, natDegree_map_eq_of_injective]
  · exact f.polynomial_natDegree
  · exact Int.cast_injective

end MonicSextic

/-! ## Monicization -/

/-- Integral monicization of an exact integer sextic.  The exponent is chosen
so that evaluation at `a₆x` clears all denominators uniformly. -/
def monicize (a : Coefficients) : MonicSextic :=
  fun i ↦ a i.castSucc * a 6 ^ (5 - (i : ℕ))

@[simp] theorem monicize_apply (a : Coefficients) (i : Fin 6) :
    monicize a i = a i.castSucc * a 6 ^ (5 - (i : ℕ)) := rfl

theorem monicize_apply_primrec (i : Fin 6) :
    Primrec fun a : Coefficients ↦ monicize a i := by
  exact (int_mul_primrec.comp
    (QuinticRadicalPrimrec.IntegerSextic.coeff_primrec i.castSucc)
    ((int_pow_const_primrec (5 - (i : ℕ))).comp
      (QuinticRadicalPrimrec.IntegerSextic.coeff_primrec 6))).of_eq fun _ ↦ rfl

theorem monicize_primrec : Primrec monicize := by
  apply Primrec.fin_curry.mpr
  have h : Primrec₂ fun i : Fin 6 ↦ fun a : Coefficients ↦ monicize a i :=
    Primrec.fin_curry₁.mpr monicize_apply_primrec
  exact h.swap

/-- The defining denominator-clearing identity for sextic monicization. -/
theorem monicize_evalRat (a : Coefficients) (x : ℚ) :
    (monicize a).evalRat ((a 6 : ℚ) * x) =
      (a 6 : ℚ) ^ 5 * a.evalRat x := by
  simp [MonicSextic.evalRat, monicize,
    QuinticRadicalDecidability.IntegerSextic.evalRat, Fin.sum_univ_succ]
  ring

end LeanProofs.PolynomialFormulas.SexticRadicalDecidability

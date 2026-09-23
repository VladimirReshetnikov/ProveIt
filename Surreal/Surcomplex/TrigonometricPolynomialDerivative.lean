import Surreal.Surcomplex.TrigonometricAngularStability

/-!
# Fine derivatives of actual Laurent trigonometric polynomials

The exact real Cayley numerator identifies the formal Fourier derivative
with the actual fine derivative. Simple roots of the numerator give simple
angular roots. These close the differentiation obligations in
`trigonometry:thm:stability` without differentiating an unproved infinite sum.
-/

universe u

namespace Surreal.Surcomplex

open Foundations Polynomial Filter Topology

noncomputable section

/-- The real trigonometric polynomial on finite angles, extended by zero outside its domain. -/
def trigonometricFunction (p : LaurentPolynomial Surcomplex.{u}) (x : SignSequence.{u}) :
    SignSequence.{u} := by
  classical
  exact if hx : SignSequence.IsFinite x then (trigonometricPolynomial p ⟨x, hx⟩).re else 0

@[simp] theorem trigonometricFunction_eq (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) :
    trigonometricFunction p a.val = (trigonometricPolynomial p a).re := by
  unfold trigonometricFunction
  split
  · rfl
  · next h => exact False.elim (h a.property)

/-- Coefficient addition realizes the sum of the two actual real trigonometric functions. -/
theorem trigonometricFunction_add (p q : LaurentPolynomial Surcomplex.{u}) (x : SignSequence.{u}) :
    trigonometricFunction (p + q) x = trigonometricFunction p x + trigonometricFunction q x := by
  classical
  by_cases hx : SignSequence.IsFinite x
  · simp only [trigonometricFunction, dif_pos hx, trigonometricPolynomial,
      LaurentPolynomial.smeval_add, QuadraticAlgebra.re_add]
  · simp only [trigonometricFunction, dif_neg hx, add_zero]

/-- The rational Cayley pullback is an ordinary quotient of native real polynomials. -/
theorem trigonometricCayley_eq_div (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ)
    (hN : ∀ n ∈ p.coeff.support, n.natAbs ≤ N) (x : SignSequence.{u}) :
    trigonometricCayley p a x =
      (trigonometricNumerator p a N).eval x / (trigonometricDenominator N).eval x := by
  rw [eval_trigonometricNumerator p a N hN]
  change trigonometricCayley p a x =
    (trigonometricDenominator N).eval x * trigonometricCayley p a x /
      (trigonometricDenominator N).eval x
  rw [mul_div_cancel_left₀ _ (trigonometricDenominator_eval_pos N x).ne']

/-- The quotient rule computes the derivative throughout the real rational chart. -/
theorem fineHasDerivAt_trigonometricCayley (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (N : ℕ)
    (hN : ∀ n ∈ p.coeff.support, n.natAbs ≤ N) (x : SignSequence.{u}) :
    FineHasDerivAt (trigonometricCayley p a)
      (((trigonometricNumerator p a N).derivative.eval x * (trigonometricDenominator N).eval x -
        (trigonometricNumerator p a N).eval x * (trigonometricDenominator N).derivative.eval x) /
        ((trigonometricDenominator N).eval x) ^ 2) x := by
  have hd := (FineHasDerivAt.polynomial (trigonometricNumerator p a N) x).div
    (FineHasDerivAt.polynomial (trigonometricDenominator N) x)
    (trigonometricDenominator_eval_pos N x).ne'
  exact hd.congr_of_eventuallyEq (Eventually.of_forall fun y =>
    (trigonometricCayley_eq_div p a N hN y).symm)

/-- The common denominator contributes no linear term at the chart center. -/
@[simp] theorem trigonometricDenominator_derivative_eval_zero (N : ℕ) :
    (trigonometricDenominator N : Polynomial SignSequence.{u}).derivative.eval 0 = 0 := by
  simp [trigonometricDenominator, derivative_pow, derivative_mul]

/-- The chart derivative at its center is precisely the formal Fourier derivative. -/
theorem fineHasDerivAt_trigonometricCayley_zero (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (trigonometricCayley p a) (trigonometricFourierDerivative p a) 0 := by
  obtain ⟨N, hN⟩ := LaurentCayley.exists_frequency_bound p
  have hd := fineHasDerivAt_trigonometricCayley p a N hN 0
  have hden : (trigonometricDenominator N : Polynomial SignSequence.{u}).eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, trigonometricDenominator_coeff_zero]
  have hnum : (trigonometricNumerator p a N).derivative.eval 0 =
      trigonometricFourierDerivative p a := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simpa using trigonometricNumerator_coeff_one p a N hN
  rw [trigonometricDenominator_derivative_eval_zero, hden, hnum] at hd
  simpa using hd

private theorem fineHasDerivAt_half (x : SignSequence.{u}) :
    FineHasDerivAt (fun y : SignSequence.{u} => y / 2) (1 / 2) x := by
  convert (FineHasDerivAt.id x).div (FineHasDerivAt.const 2 x) (by norm_num) using 1
  norm_num

private theorem tanFunction_zero : tanFunction (0 : SignSequence.{u}) = 0 := by
  simpa using tanFunction_eq_finiteTan (0 : SignSequence.FiniteElement.{u})

/-- The forward rational coordinate has derivative one at the origin. -/
theorem fineHasDerivAt_angularCayleyCoordinate_zero :
    FineHasDerivAt (fun x : SignSequence.{u} => 2 * tanFunction (x / 2)) 1 0 := by
  have hc : cosFunction (0 : SignSequence.{u}) ≠ 0 := by
    have he := cosFunction_eq_finiteCos (0 : SignSequence.FiniteElement.{u})
    have he' : cosFunction (0 : SignSequence.{u}) = 1 := by simpa using he
    rw [he']
    exact one_ne_zero
  have ht : FineHasDerivAt tanFunction (1 : SignSequence.{u}) 0 := by
    simpa only [tanFunction_zero, zero_pow (by omega : 2 ≠ 0), add_zero] using
      fineHasDerivAt_tanFunction 0 SignSequence.finite_zero hc
  have ht' : FineHasDerivAt tanFunction (1 : SignSequence.{u}) ((0 : SignSequence.{u}) / 2) := by
    simpa only [zero_div] using ht
  have hcomp := ht'.comp (f := fun y : SignSequence.{u} => y / 2)
    (fineHasDerivAt_half (0 : SignSequence.{u}))
  have hm := (FineHasDerivAt.const (2 : SignSequence.{u}) 0).mul hcomp
  convert hm using 1 <;> norm_num [Function.comp_def]

/-- Near a finite center, the ambient function agrees with its exact rational chart. -/
theorem trigonometricFunction_shift_of_infinitesimal (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) (x : SignSequence.{u})
    (hx : SignSequence.IsInfinitesimal x) :
    trigonometricFunction p (a.val + x) = trigonometricCayley p a (2 * tanFunction (x / 2)) := by
  let h : SignSequence.FiniteElement.{u} := ⟨x, SignSequence.finite_of_infinitesimal hx⟩
  have ht : tanFunction (x / 2) = finiteTan (finiteHalf h) := by
    simpa only [val_finiteHalf] using tanFunction_eq_finiteTan (finiteHalf h)
  rw [ht]
  change trigonometricFunction p (a + h).val = trigonometricCayley p a (angularCayleyCoordinate h)
  rw [trigonometricFunction_eq, trigonometricCayley_coordinate p a h hx]

/-- The Fourier derivative is the native fine derivative at every finite actual angle. -/
theorem fineHasDerivAt_trigonometricFunction (p : LaurentPolynomial Surcomplex.{u})
    (a : SignSequence.FiniteElement.{u}) :
    FineHasDerivAt (trigonometricFunction p) (trigonometricFourierDerivative p a) a.val := by
  have houter : FineHasDerivAt (trigonometricCayley p a) (trigonometricFourierDerivative p a)
      (2 * tanFunction ((0 : SignSequence.{u}) / 2)) := by
    simpa only [zero_div, tanFunction_zero, mul_zero] using
      fineHasDerivAt_trigonometricCayley_zero p a
  have hc := houter.comp (f := fun x : SignSequence.{u} => 2 * tanFunction (x / 2))
    fineHasDerivAt_angularCayleyCoordinate_zero
  have he : (trigonometricCayley p a ∘ (fun x : SignSequence.{u} => 2 * tanFunction (x / 2)))
      =ᶠ[𝓝 0] (fun x => trigonometricFunction p (a.val + x)) := by
    filter_upwards [SignSequence.infinitesimals_mem_nhds_zero] with x hx
    exact (trigonometricFunction_shift_of_infinitesimal p a x hx).symm
  have hd := hc.congr_of_eventuallyEq he
  simpa only [FineHasDerivAt, mul_one, zero_add, add_zero] using hd

/-- The inverse angular chart has its ordinary rational derivative at all actual inputs. -/
theorem fineHasDerivAt_angularCayleyInverse (x : SignSequence.{u}) :
    FineHasDerivAt (fun y => (angularCayleyInverse y).val)
      (1 / (1 + (x / 2) ^ 2)) x := by
  have hc := (fineHasDerivAt_arctanFunction (x / 2)).comp
    (f := fun y : SignSequence.{u} => y / 2) (fineHasDerivAt_half x)
  have hm := (FineHasDerivAt.const (2 : SignSequence.{u}) x).mul hc
  convert hm using 1
  · ext y
    simp only [angularCayleyInverse_val, Function.comp_def]
  · ring

/-- A simple numerator root gives a nonzero actual angular derivative. -/
theorem trigonometricFourierDerivative_ne_zero_of_simple_numerator
    (p : LaurentPolynomial Surcomplex.{u}) (a : SignSequence.FiniteElement.{u})
    (N : ℕ) (hN : ∀ n ∈ p.coeff.support, n.natAbs ≤ N) (x : SignSequence.{u})
    (hr : (trigonometricNumerator p a N).IsRoot x)
    (hm : (trigonometricNumerator p a N).rootMultiplicity x = 1) :
    trigonometricFourierDerivative p (a + angularCayleyInverse x) ≠ 0 := by
  have hP : trigonometricNumerator p a N ≠ 0 := by
    intro he
    rw [he, rootMultiplicity_zero] at hm
    omega
  have hPd : (trigonometricNumerator p a N).derivative.eval x ≠ 0 := by
    intro hd
    have hh := (one_lt_rootMultiplicity_iff_isRoot hP).mpr ⟨hr, hd⟩
    rw [hm] at hh
    omega
  have hD := (trigonometricDenominator_eval_pos N x).ne'
  have hrat := fineHasDerivAt_trigonometricCayley p a N hN x
  have hnonzero :
      ((trigonometricNumerator p a N).derivative.eval x * (trigonometricDenominator N).eval x -
        (trigonometricNumerator p a N).eval x * (trigonometricDenominator N).derivative.eval x) /
        ((trigonometricDenominator N).eval x) ^ 2 ≠ 0 := by
    rw [hr.eq_zero, zero_mul, sub_zero]
    exact div_ne_zero (mul_ne_zero hPd hD) (pow_ne_zero _ hD)
  have hinner := (FineHasDerivAt.const a.val x).add (fineHasDerivAt_angularCayleyInverse x)
  have houter := fineHasDerivAt_trigonometricFunction p (a + angularCayleyInverse x)
  have hcomp := houter.comp (f := fun y : SignSequence.{u} => a.val + (angularCayleyInverse y).val)
    hinner
  have he : (trigonometricFunction p ∘
      (fun y : SignSequence.{u} => a.val + (angularCayleyInverse y).val)) = trigonometricCayley p a := by
    funext y
    change trigonometricFunction p (a + angularCayleyInverse y).val = _
    rw [trigonometricFunction_eq, trigonometricCayley_inverse]
  rw [he] at hcomp
  have hder := hcomp.unique hrat
  intro hz
  rw [hz, zero_mul] at hder
  exact hnonzero hder.symm

end
end Surreal.Surcomplex

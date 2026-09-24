import Surreal.Surcomplex.SineSquareLaurent
import Surreal.Surcomplex.SineSquareStabilityErrors

/-!
# Sharpness of angular root stability

This proves `trigonometry:prop:sharp` with actual Laurent-polynomial
witnesses from the source's sine-square family. Every positive surreal
exponent `κ` and every `σ > 2κ` admit a perturbation attaining both error
bounds. At `σ = 2κ`, an explicit perturbation removes every root from the
original neighborhood. No restriction on the rank of the exponents is used.
-/

universe u

namespace Surreal.Surcomplex.SineSquare

open Foundations

noncomputable section

/-- A positive infinitesimal angle at any prescribed positive surreal valuation. -/
def monomialAngle (k : SignSequence.{u}) (hk : 0 < k) : SignSequence.FiniteElement.{u} :=
  ⟨SignSequence.tMonomial k, SignSequence.finite_of_infinitesimal
    ((SignSequence.isInfinitesimal_iff_valuation_pos _).mpr
      (by rw [SignSequence.valuation_tMonomial]; exact WithTop.coe_pos.mpr hk))⟩

@[simp] theorem valuation_monomialAngle (k : SignSequence.{u}) (hk : 0 < k) :
    SignSequence.valuation (monomialAngle k hk).val = ↑k := SignSequence.valuation_tMonomial k

theorem infinitesimal_monomialAngle (k : SignSequence.{u}) (hk : 0 < k) :
    SignSequence.IsInfinitesimal (monomialAngle k hk).val := by
  rw [SignSequence.isInfinitesimal_iff_valuation_pos, valuation_monomialAngle]
  exact WithTop.coe_pos.mpr hk

/-- Both stability exponents are attained in the exact class of finite Laurent
trigonometric polynomials, for every `κ > 0` and `σ > 2κ`. -/
theorem exists_exact_stability_errors (k s : SignSequence.{u}) (hk : 0 < k) (hs : 2 * k < s) :
    ∃ (p g : LaurentPolynomial Surcomplex.{u}) (a : SignSequence.FiniteElement.{u})
      (A h : SignSequence.{u}),
      (∀ n : ℤ, IsFinite (p.coeff n)) ∧
      (∀ n : ℤ, (s : WithTop SignSequence.{u}) ≤ valuation (g.coeff n)) ∧
      valuation (g.coeff 0) = ↑s ∧
      trigonometricFunction p a.val = 0 ∧
      FineHasDerivAt (trigonometricFunction p) A a.val ∧
      SignSequence.valuation A = ↑k ∧
      (k : WithTop SignSequence.{u}) < SignSequence.valuation h ∧
      trigonometricFunction (p + g) (a.val + h) = 0 ∧
      SignSequence.valuation h = ↑(s - k) ∧
      SignSequence.valuation (h + trigonometricFunction g a.val / A) = ↑(2 * s - 3 * k) := by
  have hr : 0 < s - k := by linarith
  have hkr : k < s - k := by linarith
  let a := monomialAngle k hk
  let h := monomialAngle (s - k) hr
  have ha : SignSequence.IsInfinitesimal a.val := infinitesimal_monomialAngle k hk
  have hh : SignSequence.IsInfinitesimal h.val := infinitesimal_monomialAngle (s - k) hr
  have hva : SignSequence.valuation a.val = ↑k := valuation_monomialAngle k hk
  have hvh : SignSequence.valuation h.val = ↑(s - k) := valuation_monomialAngle (s - k) hr
  have hAv : SignSequence.valuation (slope a) = ↑k := (valuation_slope a ha).trans hva
  obtain ⟨hd, he⟩ := exact_error_valuations a h ha hh k (s - k) hva hvh hkr
  have hks : k + (s - k) = s := by ring
  have hrs : 2 * (s - k) - k = 2 * s - 3 * k := by ring
  rw [hks] at hd
  rw [hrs] at he
  refine ⟨fourier (finiteSin a ^ 2), constant (perturbation a h), a, slope a, h.val,
    fourier_finite _ (SignSequence.finite_pow (isFinite_finiteSin a) 2),
    constant_coefficient_valuation _ s hd, ?_, ?_, fineHasDerivAt_fourier _ a,
    hAv, ?_, ?_, hvh, ?_⟩
  · rwa [constant_coefficient_zero_valuation]
  · rw [trigonometricFunction_fourier, function_eval, sub_self]
  · rw [hvh, WithTop.coe_lt_coe]
    exact hkr
  · change trigonometricFunction (fourier (finiteSin a ^ 2) + constant (perturbation a h))
      (a + h).val = 0
    rw [trigonometricFunction_add, trigonometricFunction_fourier, trigonometricFunction_constant]
    exact perturbed_root a h
  · rwa [trigonometricFunction_constant]

/-- Equality in the threshold does not preserve a root, even though the original
root has a nonzero native fine derivative and all Fourier coefficients are finite. -/
theorem exists_threshold_counterexample (k : SignSequence.{u}) (hk : 0 < k) :
    ∃ (p g : LaurentPolynomial Surcomplex.{u}) (a : SignSequence.FiniteElement.{u})
      (A : SignSequence.{u}),
      (∀ n : ℤ, IsFinite (p.coeff n)) ∧
      (∀ n : ℤ, (2 * k : SignSequence.{u}) ≤ valuation (g.coeff n)) ∧
      valuation (g.coeff 0) = ↑(2 * k) ∧
      trigonometricFunction p a.val = 0 ∧
      FineHasDerivAt (trigonometricFunction p) A a.val ∧
      SignSequence.valuation A = ↑k ∧
      ∀ y : SignSequence.{u}, (k : WithTop SignSequence.{u}) < SignSequence.valuation y →
        trigonometricFunction (p + g) (a.val + y) ≠ 0 := by
  let a := monomialAngle k hk
  have ha : SignSequence.IsInfinitesimal a.val := infinitesimal_monomialAngle k hk
  have hva : SignSequence.valuation a.val = ↑k := valuation_monomialAngle k hk
  have hd := threshold_valuation a ha k hva
  refine ⟨fourier (finiteSin a ^ 2), constant (finiteSin a ^ 2), a, slope a,
    fourier_finite _ (SignSequence.finite_pow (isFinite_finiteSin a) 2),
    constant_coefficient_valuation _ (2 * k) hd, ?_, ?_, fineHasDerivAt_fourier _ a,
    (valuation_slope a ha).trans hva, ?_⟩
  · rwa [constant_coefficient_zero_valuation]
  · rw [trigonometricFunction_fourier, function_eval, sub_self]
  · intro y hy
    have hyi : SignSequence.IsInfinitesimal y :=
      (SignSequence.isInfinitesimal_iff_valuation_pos _).mpr
        ((show (0 : WithTop SignSequence.{u}) ≤ ↑k from WithTop.coe_nonneg.mpr hk.le).trans_lt hy)
    let z : SignSequence.FiniteElement.{u} :=
      ⟨a.val + y, SignSequence.finite_add a.property (SignSequence.finite_of_infinitesimal hyi)⟩
    change trigonometricFunction (fourier (finiteSin a ^ 2) + constant (finiteSin a ^ 2)) z.val ≠ 0
    rw [trigonometricFunction_add, trigonometricFunction_fourier, trigonometricFunction_constant]
    exact threshold_no_root a ha k hva hk.le y hy

end
end Surreal.Surcomplex.SineSquare

import Surreal.HahnSeries.NonpositivePolynomialDegree

/-!
# Faithful polynomial evaluation in Hahn support rings

The polynomial-to-Hahn bridge for `odg:def:rem:rootneeded`. Negative
Hahn order makes evaluation injective; a zero constant term makes
constant extraction agree with evaluation of the polynomial at zero.
-/

namespace Surreal.HahnSeries

noncomputable section

variable {Γ K : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ] [Field K]

/-- Evaluate coefficient-field polynomials at an element of the support ring. -/
def supportPolynomialEval (f : nonpositiveSupportSubring Γ K) :
    Polynomial K →+* nonpositiveSupportSubring Γ K :=
  Polynomial.eval₂RingHom nonpositiveConstants f

@[simp] theorem supportPolynomialEval_C (f : nonpositiveSupportSubring Γ K) (c : K) :
    supportPolynomialEval f (Polynomial.C c) = nonpositiveConstants c := by
  simp [supportPolynomialEval]

@[simp] theorem supportPolynomialEval_X (f : nonpositiveSupportSubring Γ K) :
    supportPolynomialEval f Polynomial.X = f := by simp [supportPolynomialEval]

/-- Negative-order series are transcendental, so polynomial evaluation is faithful. -/
theorem supportPolynomialEval_injective (f : nonpositiveSupportSubring Γ K)
    (hf : f.val.order < 0) : Function.Injective (supportPolynomialEval f) := by
  have hker (P : Polynomial K) (h : supportPolynomialEval f P = 0) : P = 0 := by
    by_contra hp
    have hv := congrArg Subtype.val h
    change (P.eval₂ nonpositiveConstants f).val = 0 at hv
    rw [nonpositiveSupport_eval_val] at hv
    exact (polynomial_eval_negative_order P hp f.val hf).1 hv
  intro P Q h
  exact sub_eq_zero.mp (hker (P - Q) (by rw [map_sub, h, sub_self]))

/-- At a zero-constant series, constant extraction is polynomial evaluation at zero. -/
theorem constantCoeff_supportPolynomialEval (f : nonpositiveSupportSubring Γ K)
    (hf : nonpositiveConstantCoeff f = 0) (P : Polynomial K) :
    nonpositiveConstantCoeff (supportPolynomialEval f P) = P.eval 0 := by
  change nonpositiveConstantCoeff (P.eval₂ _ f) = _
  rw [Polynomial.hom_eval₂, hf]
  have hi : (nonpositiveConstantCoeff (Γ := Γ) (R := K)).comp nonpositiveConstants =
      RingHom.id K := by ext c; exact nonpositiveConstantCoeff_constants c
  rw [hi, Polynomial.eval₂_id]

end
end Surreal.HahnSeries

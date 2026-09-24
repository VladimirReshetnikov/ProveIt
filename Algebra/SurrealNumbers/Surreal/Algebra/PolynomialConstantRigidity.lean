import Surreal.Algebra.QuadraticNormRigidity
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Constant polynomial Pell solutions

The polynomial-ring rigidity used by the counterexample in
`odg:def:rem:rootneeded`. Extending coefficients to an algebraic closure
allows factorization; polynomial units are constants, and degree descends
the result to the original coefficient field.
-/

namespace Surreal.PolynomialConstantRigidity

open Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Every polynomial unit equals the constant given by evaluation at zero. -/
theorem unit_eq_constant (p : K[X]) (hp : IsUnit p) : p = C (p.eval 0) := by
  obtain ⟨a, _, rfl⟩ := Polynomial.isUnit_iff.mp hp
  simp

/-- Polynomial Pell solutions at a nonzero constant level have constant coordinates. -/
theorem pell_constant (D c : K) (hD : D ≠ 0) (hc : c ≠ 0) (x y : K[X])
    (h : x ^ 2 - C D * y ^ 2 = C c) : x = C (x.eval 0) ∧ y = C (y.eval 0) := by
  let E := AlgebraicClosure K
  let φ : K →+* E := algebraMap K E
  let ψ := Polynomial.mapRingHom φ
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (φ D) zero_lt_two
  have hr0 : r ≠ 0 := by
    intro hz
    have hd : φ D = 0 := by simpa [hz] using hr.symm
    exact hD ((map_eq_zero_iff φ φ.injective).mp hd)
  have he : ψ x ^ 2 - C (r ^ 2) * ψ y ^ 2 = C (φ c) := by
    rw [hr]
    have hm := congrArg ψ h
    simp only [map_sub, map_pow, map_mul] at hm
    change x.map φ ^ 2 - (C D).map φ * y.map φ ^ 2 = (C c).map φ at hm
    simp only [Polynomial.map_C] at hm
    exact hm
  have hh := QuadraticNormRigidity.coordinates_constant (Polynomial.aeval (0 : E))
    (fun p hp => by simpa using unit_eq_constant p hp)
    r (φ c) hr0 ((map_ne_zero_iff φ φ.injective).mpr hc) (ψ x) (ψ y) he
  have descend (p : K[X]) (hp : ψ p = C ((ψ p).eval 0)) : p = C (p.eval 0) := by
    have hd : p.natDegree = 0 := by
      rw [← natDegree_map (p := p) φ]
      change (ψ p).natDegree = 0
      rw [hp, natDegree_C]
    simpa only [coeff_zero_eq_eval_zero] using eq_C_of_natDegree_eq_zero hd
  exact ⟨descend x (by simpa using hh.1), descend y (by simpa using hh.2)⟩

end
end Surreal.PolynomialConstantRigidity

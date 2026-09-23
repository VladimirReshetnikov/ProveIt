import Surreal.Foundations.SignSequencePolynomialStability

/-!
# The second-order error in a simple polynomial root

The polynomial precursor of `trigonometry:eq:stabilitysecond` follows from
an exact finite quadratic remainder and the actual surreal valuation laws.
Combined with scaled simple-root lifting, this gives both stated exponents
for finite polynomials. The trigonometric chart and sharpness examples
remain separate obligations.
-/

universe u

namespace Surreal.Foundations.SignSequence

open Polynomial

noncomputable section

/-- Finite coefficients evaluated at a finite actual surreal give a finite value. -/
theorem finite_polynomial_eval (P : Polynomial SignSequence.{u})
    (hP : ∀ n, IsFinite (P.coeff n)) (x : SignSequence.{u}) (hx : IsFinite x) :
    IsFinite (P.eval x) := by
  let x' : FiniteElement.{u} := ⟨x, hx⟩
  have he : finiteElementInclusion ((finitePolynomial P hP).eval x') = P.eval x := by
    rw [← eval₂_at_apply, ← eval_map, map_finitePolynomial, finiteElementInclusion_apply]
  rw [← he, finiteElementInclusion_apply]
  exact ((finitePolynomial P hP).eval x').2

/-- Products add any specified finite lower valuation bounds, including when a factor is zero. -/
theorem valuation_mul_ge_of_ge (x y a b : SignSequence.{u})
    (hx : (a : WithTop SignSequence.{u}) ≤ valuation x)
    (hy : (b : WithTop SignSequence.{u}) ≤ valuation y) :
    (a + b : SignSequence.{u}) ≤ valuation (x * y) := by
  rw [valuation_mul, WithTop.coe_add]
  exact add_le_add hx hy

/-- Division subtracts the specified finite denominator valuation from a lower bound. -/
theorem valuation_div_ge_of_ge (x y a b : SignSequence.{u})
    (hx : (a : WithTop SignSequence.{u}) ≤ valuation x) (hy : valuation y = ↑b) :
    (a - b : SignSequence.{u}) ≤ valuation (x / y) := by
  rw [valuation_div, hy]
  cases he : valuation x with
  | top => simp
  | coe c =>
    rw [he, WithTop.coe_le_coe] at hx
    change ((a - b : SignSequence.{u}) : WithTop SignSequence.{u}) ≤ ↑(c - b)
    exact_mod_cast sub_le_sub_right hx b

/-- At any sufficiently small root, the linear Newton correction has the second-order bound. -/
theorem polynomial_root_correction_valuation
    (P : Polynomial SignSequence.{u}) (A k s h : SignSequence.{u})
    (hA : valuation A = ↑k) (hk : 0 ≤ k) (hs : 2 * k < s)
    (h1 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 1 - A))
    (hh : ∀ n, IsFinite (P.coeff (n + 2)))
    (hv : (s - k : SignSequence.{u}) ≤ valuation h) (hroot : P.IsRoot h) :
    (2 * s - 3 * k : SignSequence.{u}) ≤ valuation (h + P.coeff 0 / A) := by
  have hA0 : A ≠ 0 := by
    intro he
    rw [he, valuation_zero] at hA
    exact WithTop.top_ne_coe hA
  have hr : 0 ≤ s - k := by linarith
  have hf : IsFinite h := (isFinite_iff_valuation_nonneg h).mpr
    ((show (0 : WithTop SignSequence.{u}) ≤ (s - k : SignSequence.{u}) by
      exact_mod_cast hr).trans hv)
  have hQ : ∀ n, IsFinite (P.divX.divX.coeff n) := by
    intro n
    simpa only [coeff_divX, Nat.add_assoc] using hh n
  have hQf := finite_polynomial_eval P.divX.divX hQ h hf
  have hQv : (0 : WithTop SignSequence.{u}) ≤ valuation (P.divX.divX.eval h) :=
    (isFinite_iff_valuation_nonneg _).mp hQf
  have hb := valuation_mul_ge_of_ge (P.coeff 1 - A) h s (s - k) h1 hv
  have hsq : (2 * (s - k) : SignSequence.{u}) ≤ valuation (h ^ 2) := by
    simpa only [pow_two, two_mul] using valuation_mul_ge_of_ge h h (s - k) (s - k) hv hv
  have hq : (2 * (s - k) : SignSequence.{u}) ≤ valuation (h ^ 2 * P.divX.divX.eval h) := by
    simpa only [add_zero] using valuation_mul_ge_of_ge (h ^ 2) (P.divX.divX.eval h)
      (2 * (s - k)) 0 hsq hQv
  have hb' : (2 * (s - k) : SignSequence.{u}) ≤ valuation ((P.coeff 1 - A) * h) :=
    (show ((2 * (s - k) : SignSequence.{u}) : WithTop SignSequence.{u}) ≤
      (s + (s - k) : SignSequence.{u}) by exact_mod_cast (by linarith : 2 * (s - k) ≤ s + (s - k))).trans hb
  have hsum := (le_min hb' hq).trans
    (min_valuation_le_add ((P.coeff 1 - A) * h) (h ^ 2 * P.divX.divX.eval h))
  have hvdiv := valuation_div_ge_of_ge _ A (2 * (s - k)) k hsum hA
  have he : h + P.coeff 0 / A = -(((P.coeff 1 - A) * h + h ^ 2 * P.divX.divX.eval h) / A) := by
    have heq := hroot.eq_zero
    rw [FinitePolynomial.eval_constant_linear_quadratic] at heq
    field_simp
    linear_combination heq
  rw [he, valuation_neg]
  convert hvdiv using 1
  congr 1
  ring

/-- The full polynomial precursor: simple-root persistence, the two valuation bounds,
and uniqueness throughout `v(h)>κ`, without restricting the value group to rank one. -/
theorem polynomial_root_stability
    (P : Polynomial SignSequence.{u}) (A k s : SignSequence.{u})
    (hA : valuation A = ↑k) (hk : 0 ≤ k) (hs : 2 * k < s)
    (h0 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 0))
    (h1 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 1 - A))
    (hh : ∀ n, IsFinite (P.coeff (n + 2))) :
    ∃ h : SignSequence.{u}, (k : WithTop SignSequence.{u}) < valuation h ∧ P.IsRoot h ∧
      P.rootMultiplicity h = 1 ∧ (s - k : SignSequence.{u}) ≤ valuation h ∧
      (2 * s - 3 * k : SignSequence.{u}) ≤ valuation (h + P.coeff 0 / A) ∧
      ∀ y, (k : WithTop SignSequence.{u}) < valuation y → P.IsRoot y → y = h := by
  obtain ⟨h, hv', hv, hr, hm, hu⟩ :=
    exists_unique_polynomial_root_in_open_neighborhood P A k s hA hk hs h0 h1 hh
  exact ⟨h, hv', hr, hm, hv, polynomial_root_correction_valuation P A k s h hA hk hs h1 hh hv hr, hu⟩

end
end Surreal.Foundations.SignSequence

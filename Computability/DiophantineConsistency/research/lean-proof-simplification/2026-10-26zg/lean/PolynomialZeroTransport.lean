import DiophantineConsistency.NaturalExpressionSemiring

/-!
Integer-polynomial identities preserve the equality of natural split values
in every additive-cancellative commutative semiring. No ring structure on the
semantic carrier, and no standardness assumption on internal naturals, is used.
-/
namespace DiophantineConsistency.Expr
variable {σ R : Type*}

/-- The two natural-coefficient polynomials are a signed presentation of the
existing integer polynomial, coefficient by coefficient. -/
theorem map_splitNatural_sub (e : Expr σ) :
    MvPolynomial.map (Nat.castRingHom ℤ) e.splitNatural.1.toPolynomial -
      MvPolynomial.map (Nat.castRingHom ℤ) e.splitNatural.2.toPolynomial =
        e.toPolynomial := by
  induction e with
  | constant a =>
      simpa only [splitNatural, NatExpr.toPolynomial, toPolynomial,
        MvPolynomial.map_C, Nat.coe_castRingHom, map_sub] using
        congrArg (MvPolynomial.C (σ := σ)) (Int.toNat_sub_toNat_neg a)
  | var i => simp [splitNatural, NatExpr.toPolynomial, toPolynomial]
  | add p q hp hq =>
      simp only [splitNatural, NatExpr.toPolynomial, toPolynomial, map_add]
      rw [← hp, ← hq]
      ring
  | sub p q hp hq =>
      simp only [splitNatural, NatExpr.toPolynomial, toPolynomial, map_add]
      rw [← hp, ← hq]
      ring
  | mul p q hp hq =>
      simp only [splitNatural, NatExpr.toPolynomial, toPolynomial, map_add, map_mul]
      rw [← hp, ← hq]
      ring

/-- Equality over integers gives a subtraction-free cross-sum identity over
natural coefficients. This theorem has no cancellation hypothesis on R. -/
theorem splitNatural_cross_sum (e f : Expr σ) (h : e.toPolynomial = f.toPolynomial) :
    e.splitNatural.1.toPolynomial + f.splitNatural.2.toPolynomial =
      f.splitNatural.1.toPolynomial + e.splitNatural.2.toPolynomial := by
  apply MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective
  simp only [map_add]
  apply sub_eq_sub_iff_add_eq_add.mp
  simpa only [map_splitNatural_sub] using h

/-- Apply an ordinary natural-coefficient evaluation homomorphism. -/
theorem splitNatural_eval_cross_sum [CommSemiring R] (e f : Expr σ)
    (h : e.toPolynomial = f.toPolynomial) (v : σ → R) :
    e.splitNatural.1.evalSemiring v + f.splitNatural.2.evalSemiring v =
      f.splitNatural.1.evalSemiring v + e.splitNatural.2.evalSemiring v := by
  have he := congrArg (MvPolynomial.eval₂Hom (Nat.castRingHom R) v)
    (splitNatural_cross_sum e f h)
  simpa only [map_add, MvPolynomial.coe_eval₂Hom, NatExpr.eval₂_toPolynomial] using he

/-- The public semantic transport law. Additive cancellation is essential. -/
theorem splitNatural_zero_iff_of_polynomial_eq [CommSemiring R] [IsCancelAdd R]
    (e f : Expr σ) (h : e.toPolynomial = f.toPolynomial) (v : σ → R) :
    (e.splitNatural.1.evalSemiring v = e.splitNatural.2.evalSemiring v) ↔
      (f.splitNatural.1.evalSemiring v = f.splitNatural.2.evalSemiring v) := by
  have hc := splitNatural_eval_cross_sum e f h v
  constructor
  · intro he
    rw [he, add_comm _ (e.splitNatural.2.evalSemiring v)] at hc
    exact (add_left_cancel hc).symm
  · intro hf
    rw [hf, add_comm _ (e.splitNatural.2.evalSemiring v)] at hc
    exact add_right_cancel hc

#print axioms map_splitNatural_sub
#print axioms splitNatural_cross_sum
#print axioms splitNatural_zero_iff_of_polynomial_eq
end DiophantineConsistency.Expr

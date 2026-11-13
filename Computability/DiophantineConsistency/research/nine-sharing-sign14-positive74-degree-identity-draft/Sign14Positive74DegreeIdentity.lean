import DiophantineConsistency.Sign14Positive74ObjectEndpoint
import DiophantineConsistency.Sign14Positive74ExpressionBridge
import DiophantineConsistency.ModelCoding

/-! SOURCE ONLY: actual positive74-to-natural86 polynomial shift identity. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74DegreeIdentity

theorem shifted_polynomial (p : Fin 4 → ℤ) :
    MvPolynomial.eval₂ MvPolynomial.C (fun i : Fin 14 => MvPolynomial.X i + 1)
      (Sign14Positive74.expression p).toPolynomial =
        (Sign14Optimized86Expression.expression p).toPolynomial := by
  have hc : Int.castRingHom (MvPolynomial (Fin 14) ℤ) = MvPolynomial.C := Subsingleton.elim _ _
  have h := Sign14Positive74ExpressionBridge.eval_shift (R := MvPolynomial (Fin 14) ℤ)
    p (fun i => MvPolynomial.X i)
  simpa only [ModelCoding.evalRing_eq_eval₂, hc, MvPolynomial.eval₂_eta] using h
end DiophantineConsistency.Sign14Positive74DegreeIdentity
#print axioms DiophantineConsistency.Sign14Positive74DegreeIdentity.shifted_polynomial

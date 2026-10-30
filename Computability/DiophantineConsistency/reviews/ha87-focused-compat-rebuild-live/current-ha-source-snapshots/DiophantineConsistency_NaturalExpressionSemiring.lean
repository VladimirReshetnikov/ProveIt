import DiophantineConsistency.NaturalExpression

/-! # Finite natural expressions over arbitrary semirings -/
namespace DiophantineConsistency.NatExpr
variable {σ : Type*}

def evalSemiring {R : Type*} [Semiring R] (v : σ → R) : NatExpr σ → R
  | .constant n => n
  | .var i => v i
  | .add p q => p.evalSemiring v+q.evalSemiring v
  | .mul p q => p.evalSemiring v*q.evalSemiring v

theorem evalSemiring_nat (e : NatExpr σ) (v : σ → ℕ) : e.evalSemiring v=e.eval v := by
  induction e <;> simp_all [evalSemiring,eval]

theorem eval₂_toPolynomial {R : Type*} [CommSemiring R] (e : NatExpr σ) (v : σ → R) :
    MvPolynomial.eval₂ (Nat.castRingHom R) v e.toPolynomial=e.evalSemiring v := by
  induction e <;> simp_all [evalSemiring,toPolynomial]

end DiophantineConsistency.NatExpr

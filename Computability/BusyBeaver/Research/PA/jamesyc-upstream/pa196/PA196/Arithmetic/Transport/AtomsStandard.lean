module
public import PA196.Arithmetic.Transport.FoundationRelationalCodeAtoms
public import PA196.Logic.Relational.Encoding
@[expose] public section
open M6.PA
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open M6.PA.RelationalSource M6.PA.ActualArithmeticGraph

theorem neighborhood_exact (a d z : Nat) :
    eval neighborhoodExpr a d z 0 = PA196.Logic.neighborhoodEquality a d z := by
  rw [eval_standard]
  rfl

theorem membership_exact (a d z : Nat) :
    eval membershipExpr a d z 0 = PA196.Logic.wel d a := by
  rw [eval_standard]
  rfl

/-- The model graph calibrates to the new standard numeric encoding. -/
theorem atomHead_quote {n k : Nat} (r : Relation k)
    (ts : Fin k → SyntacticSemiterm language n)
    (b : Fin n → Nat) (f : Nat → Nat) (z : Nat) :
    AtomHead (PA196.Logic.Relational.relationalCode z (atomNamed r ts b f)) (Encodable.encode r)
      (termLabel (ts (by cases r <;> exact 0)) b f)
      (termLabel (ts (by cases r <;> exact 1)) b f) z := by
  cases r with
  | eq => exact Or.inl ⟨rfl,(neighborhood_exact _ _ _).symm⟩
  | mem => exact Or.inr ⟨rfl,(membership_exact _ _ _).symm⟩

#print axioms neighborhood_exact
#print axioms membership_exact
#print axioms atomHead_quote
end PA196.Arithmetic.Transport.RelationalSource.Numeric

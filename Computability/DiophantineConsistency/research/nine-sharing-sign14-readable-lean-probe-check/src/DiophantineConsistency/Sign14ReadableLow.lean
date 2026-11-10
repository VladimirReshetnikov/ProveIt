import DiophantineConsistency.Sign14Readable

/-! SOURCE-ONLY: the first named-formula ring identity. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Readable

theorem low_eval {R : Type*} [CommRing R] (v : Fin 15 → R) (p : Fin 4 → ℤ) :
    (SharingSeed14Degree124.shared07 p).evalRing v = (horizontal p).evalRing v - 1 := by
  simp only [SharingSeed14Degree124.shared07, SharingSeed14Degree124.shared02,
    horizontal, width, unit, base, judge, positive, Expr.evalRing_add,
    Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one]
  ring
end DiophantineConsistency.Sign14Readable
#print axioms DiophantineConsistency.Sign14Readable.low_eval

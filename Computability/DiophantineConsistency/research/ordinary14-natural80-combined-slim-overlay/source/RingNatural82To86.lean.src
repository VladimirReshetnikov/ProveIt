import P82NaturalForced
import P86NaturalCancel

/-! Source-only proposal; this file and its dependencies are unelaborated.
The changed valuation is essential: same-valuation equality is not claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.RingNatural82To86Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- Subtract one in the three coordinates whose 82-graph shifts were deleted. -/
def down (v : Fin 14 → R) : Fin 14 → R :=
  fun j => if j = 3 ∨ j = 8 ∨ j = 11 then v j - 1 else v j

theorem undo_one (x : R) : x - 1 + 1 = x := by ring
theorem k_cut (eta zeta : R) : eta + (zeta + 1) = (eta + zeta) + 1 := by ring
theorem r0_cut (kbase rank : R) : (kbase + 1) - rank - 1 = kbase - rank := by ring

/-- The factors agree after the three ring-coordinate translations. -/
theorem restricted_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P82NaturalForced.graph p).first.evalRing v = (P86NaturalCancel.graph p).first.evalRing (down v) ∧
    (P82NaturalForced.graph p).main.evalRing v = (P86NaturalCancel.graph p).main.evalRing (down v) ∧
    (P82NaturalForced.graph p).aux.evalRing v = (P86NaturalCancel.graph p).aux.evalRing (down v) ∧
    (P82NaturalForced.graph p).strong.evalRing v = (P86NaturalCancel.graph p).strong.evalRing (down v) := by
  simp only [P82NaturalForced.graph, P86NaturalCancel.graph, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, down, Int.cast_one, Nat.cast_one, undo_one, k_cut, r0_cut]

theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P82NaturalForced.graph p).guardFactor.evalRing v =
      (P86NaturalCancel.graph p).guardFactor.evalRing (down v) := by
  simp only [P82NaturalForced.graph, P86NaturalCancel.graph, Expr.evalRing_add,
    Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var, Expr.evalRing_constant,
    Expr.evalRing_ofNat, down, Int.cast_one, Nat.cast_one, undo_one, k_cut, r0_cut]

/-- Output identity over a ring, not a same-valuation model equivalence. -/
theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P82NaturalForced.graph p).output.evalRing v =
      (P86NaturalCancel.graph p).output.evalRing (down v) := by
  rw [P82NaturalForced.output_shape, P86NaturalCancel.output_shape]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_ofNat, Expr.evalRing_constant, Int.cast_one, Nat.cast_one]
  rcases restricted_eval p v with ⟨h0, h1, h2, h3⟩
  rw [h0, h1, h2, h3, guard_eval]

end DiophantineConsistency.RingNatural82To86Draft

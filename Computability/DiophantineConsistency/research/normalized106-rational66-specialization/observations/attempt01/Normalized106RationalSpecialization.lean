import Normalized106Rational66
import Mathlib.Data.Rat.Cast.Lemmas

/-! External rational specialization against the historical 67/106 syntax. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.Normalized106RationalSpecialization
open Normalized106Rational66

def portsQ (p : Fin 4 → ℤ) : Fin 4 → ℚ := fun j => p j
def inputQ (v : Fin 14 → ℤ) : Fin 14 → ℚ := fun j => v j

/-- Ring evaluation agrees with casting integer evaluation to ℚ. -/
theorem evalRing_rat_cast (e : Expr (Fin 14)) (v : Fin 14 → ℤ) :
    e.evalRing (inputQ v) = ((e.eval v : ℤ) : ℚ) := by
  induction e <;> simp_all [Expr.evalRing, Expr.eval, inputQ, Int.cast_add,
    Int.cast_sub, Int.cast_mul]

theorem rational_value_eq (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : p 0 ≠ 0) :
    value66 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
      ((p 2 : ℚ) - (p 3 : ℚ)) =
    (((ModelCarrierCurrent.expressionAt106 p).eval v : ℤ) : ℚ) := by
  have hbq : (p 0 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  calc
    _ = (ModelCarrierCurrent.expressionAt106 p).evalRing (inputQ v) := by
      apply value66_eq_syntax
      · exact mul_div_cancel₀ (p 3 : ℚ) hbq
      · rfl
    _ = _ := evalRing_rat_cast _ _

theorem positive_zero_iff (p : Fin 4 → ℤ) (hb : p 0 ≠ 0) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value66 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ModelCarrierCurrent.expressionAt106 p).eval v = 0) := by
  have hzero (v : Fin 14 → ℤ) :
      value66 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = 0 ↔
      (ModelCarrierCurrent.expressionAt106 p).eval v = 0 := by
    rw [rational_value_eq p v hb]
    exact (Int.cast_eq_zero :
      (((ModelCarrierCurrent.expressionAt106 p).eval v : ℤ) : ℚ) = 0 ↔
        (ModelCarrierCurrent.expressionAt106 p).eval v = 0)
  simp only [hzero]

#print axioms evalRing_rat_cast
#print axioms rational_value_eq
#print axioms positive_zero_iff

end DiophantineConsistency.Normalized106RationalSpecialization

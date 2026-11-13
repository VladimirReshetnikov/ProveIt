import RationalCarrier64Current
import Mathlib.Data.Rat.Cast.Lemmas

/-! Rational evaluator specialized against current14's integer syntax. -/
namespace DiophantineConsistency.RationalCarrier64CurrentSpecialization

open RationalCarrier64Current

def portsQ (p : Fin 4 → ℤ) : Fin 4 → ℚ := fun j => p j
def inputQ (v : Fin 14 → ℤ) : Fin 14 → ℚ := fun j => v j

/-- Literal 65-row evaluation commutes with a ring homomorphism. -/
theorem value65_map {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (p : Fin 4 → A) (v : Fin 14 → A) :
    φ (value65 p v) = value65 (fun j => φ (p j)) (fun j => φ (v j)) := by
  simp only [value65, head, rank65, suffix, map_add, map_sub, map_mul, map_one, map_ofNat]

/-- Equality with the integer evaluation of current14's expression. -/
theorem rational_value_eq (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : p 0 ≠ 0) :
    value64 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) =
      (((ObjectCurrentEquation2011.expressionAt p).eval v : ℤ) : ℚ) := by
  have hbq : (p 0 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  calc
    _ = value65 (portsQ p) (inputQ v) := by
      apply values_equal
      · exact mul_div_cancel₀ (p 3 : ℚ) hbq
      · rfl
    _ = ((value65 p v : ℤ) : ℚ) := (value65_map (Int.castRingHom ℚ) p v).symm
    _ = _ := by rw [value65_eq_expressionAt]

theorem rational_zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : p 0 ≠ 0) :
    value64 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = 0 ↔
      (ObjectCurrentEquation2011.expressionAt p).eval v = 0 := by
  rw [rational_value_eq p v hb]
  exact (Int.cast_eq_zero :
    (((ObjectCurrentEquation2011.expressionAt p).eval v : ℤ) : ℚ) = 0 ↔
      (ObjectCurrentEquation2011.expressionAt p).eval v = 0)

theorem positive_zero_iff (p : Fin 4 → ℤ) (hb : p 0 ≠ 0) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value64 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      (ObjectCurrentEquation2011.expressionAt p).eval v = 0) := by
  simp only [rational_zero_iff p _ hb]

#print axioms value65_map
#print axioms rational_value_eq
#print axioms rational_zero_iff
#print axioms positive_zero_iff

end DiophantineConsistency.RationalCarrier64CurrentSpecialization

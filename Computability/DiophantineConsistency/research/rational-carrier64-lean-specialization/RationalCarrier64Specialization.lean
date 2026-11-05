import RationalCarrier64
import Mathlib.Data.Rat.Cast.Lemmas

/-! Rational fixed-leaf specialization, for arbitrary integer ports and inputs. -/

namespace DiophantineConsistency.RationalCarrier64Specialization

open RationalCarrier64

def portsQ (p : Fin 4 → ℤ) : Fin 4 → ℚ := fun j => p j
def inputQ (v : Fin 14 → ℤ) : Fin 14 → ℚ := fun j => v j

/-- Pointwise identity after embedding the integer graph in the rationals. -/
theorem rational_value_eq (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : p 0 ≠ 0) :
    value64 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = ((Carrier65.value p v : ℤ) : ℚ) := by
  have hbq : (p 0 : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
  calc
    _ = value65 (portsQ p) (inputQ v) := by
      apply values_equal
      · exact mul_div_cancel₀ (p 3 : ℚ) hbq
      · rfl
    _ = Carrier65.value (portsQ p) (inputQ v) := value65_eq_carrier _ _
    _ = ((Carrier65.value p v : ℤ) : ℚ) := by
      exact (Carrier65.value_map (Int.castRingHom ℚ) p v).symm

/-- Both zero directions use the identical integer valuation. -/
theorem rational_zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (hb : p 0 ≠ 0) :
    value64 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = 0 ↔ Carrier65.value p v = 0 := by
  rw [rational_value_eq p v hb]
  exact (Int.cast_eq_zero : ((Carrier65.value p v : ℤ) : ℚ) = 0 ↔ Carrier65.value p v = 0)

theorem positive_zero_iff (p : Fin 4 → ℤ) (hb : p 0 ≠ 0) :
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      value64 (portsQ p) (inputQ v) ((p 3 : ℚ) / (p 0 : ℚ))
        ((p 2 : ℚ) - (p 3 : ℚ)) = 0) ↔
    (∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧ Carrier65.value p v = 0) := by
  simp only [rational_zero_iff p _ hb]

#print axioms rational_value_eq
#print axioms rational_zero_iff
#print axioms positive_zero_iff

end DiophantineConsistency.RationalCarrier64Specialization

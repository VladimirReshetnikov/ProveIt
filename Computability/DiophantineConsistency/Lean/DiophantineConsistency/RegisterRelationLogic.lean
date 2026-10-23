import DiophantineConsistency.NaturalRegisterRelation

/-! # Natural output equalities for logical combinations of register constraints -/

namespace DiophantineConsistency.RegisterRelationLogic

/-- Equality of these two nonnegative values conjoins two equalities. -/
def andLeft (a b c d : ℕ) : ℕ := a * a + b * b + (c * c + d * d)
def andRight (a b c d : ℕ) : ℕ := 2 * (a * b + c * d)

theorem and_equality_iff (a b c d : ℕ) :
    andLeft a b c d = andRight a b c d ↔ a = b ∧ c = d := by
  constructor
  · intro h
    have hz : (a : ℤ) * a + (b : ℤ) * b + ((c : ℤ) * c + (d : ℤ) * d) =
        2 * ((a : ℤ) * b + (c : ℤ) * d) := by
      exact_mod_cast h
    have hs : ((a : ℤ) - b) * ((a : ℤ) - b) + ((c : ℤ) - d) * ((c : ℤ) - d) = 0 := by
      nlinarith only [hz]
    obtain ⟨hab,hcd⟩ := mul_self_add_mul_self_eq_zero.mp hs
    constructor
    · exact_mod_cast sub_eq_zero.mp hab
    · exact_mod_cast sub_eq_zero.mp hcd
  · rintro ⟨rfl,rfl⟩
    simp only [andLeft,andRight]
    ring

/-- The product-of-differences identity uses only natural additions and products. -/
def orLeft (a b c d : ℕ) : ℕ := a * c + b * d
def orRight (a b c d : ℕ) : ℕ := a * d + b * c

theorem or_equality_iff (a b c d : ℕ) :
    orLeft a b c d = orRight a b c d ↔ a = b ∨ c = d := by
  constructor
  · intro h
    have hz : (a : ℤ) * c + (b : ℤ) * d = (a : ℤ) * d + (b : ℤ) * c := by
      exact_mod_cast h
    have hs : ((a : ℤ) - b) * ((c : ℤ) - d) = 0 := by nlinarith only [hz]
    rcases mul_eq_zero.mp hs with hab | hcd
    · left
      exact_mod_cast sub_eq_zero.mp hab
    · right
      exact_mod_cast sub_eq_zero.mp hcd
  · rintro (rfl | rfl)
    · simp only [orLeft,orRight]
      ring
    · simp only [orLeft,orRight]

end DiophantineConsistency.RegisterRelationLogic

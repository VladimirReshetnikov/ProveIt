import Mathlib.Data.Int.ModEq

namespace DiophantineConsistency

/-- Congruence modulo an arbitrary integer, with the target sign forgotten. -/
abbrev SignedModEq (m a b : ℤ) : Prop :=
  a ≡ b [ZMOD m] ∨ a ≡ -b [ZMOD m]

namespace SignedModEq
variable {m a b c ε : ℤ}

theorem symm (h : SignedModEq m a b) : SignedModEq m b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa using h.symm.neg)

theorem trans (hab : SignedModEq m a b) (hbc : SignedModEq m b c) :
    SignedModEq m a c := by
  rcases hab with hab | hab <;> rcases hbc with hbc | hbc
  · exact Or.inl (hab.trans hbc)
  · exact Or.inr (hab.trans hbc)
  · exact Or.inr (hab.trans hbc.neg)
  · exact Or.inl (by simpa using hab.trans hbc.neg)

theorem of_sign_mul (h : a ≡ ε * b [ZMOD m]) (hε : ε = 1 ∨ ε = -1) :
    SignedModEq m a b := by
  rcases hε with rfl | rfl
  · exact Or.inl (by simpa using h)
  · exact Or.inr (by simpa using h)

theorem iff_dvd_sub_or_add : SignedModEq m a b ↔ m ∣ a - b ∨ m ∣ a + b := by
  unfold SignedModEq
  rw [Int.modEq_comm (a := a) (b := b), Int.modEq_comm (a := a) (b := -b)]
  simp only [Int.modEq_iff_dvd, sub_neg_eq_add]

/-- Forgetting the sign of an integer does not change its signed residue. -/
theorem natAbs (m a : ℤ) : SignedModEq m a a.natAbs := by
  rcases Int.natAbs_eq a with h | h
  · exact Or.inl (congrArg (fun z : ℤ => z % m) h)
  · exact Or.inr (congrArg (fun z : ℤ => z % m) h)

end SignedModEq
end DiophantineConsistency

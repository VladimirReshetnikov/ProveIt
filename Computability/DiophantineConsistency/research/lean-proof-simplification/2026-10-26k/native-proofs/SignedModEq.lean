import Mathlib.Data.Int.ModEq

/-! Congruence up to sign: a small proof interface for Pell index recovery.
    This module changes no residue modulus and requires no positivity. -/

namespace DiophantineConsistency.ProofSimplification

def SignedModEq (m a b : ℤ) : Prop :=
  a ≡ b [ZMOD m] ∨ a ≡ -b [ZMOD m]

namespace SignedModEq

theorem of_modEq {m a b : ℤ} (h : a ≡ b [ZMOD m]) : SignedModEq m a b :=
  Or.inl h

theorem symm {m a b : ℤ} (h : SignedModEq m a b) : SignedModEq m b a := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (by simpa only [neg_neg] using h.neg.symm)

theorem trans {m a b c : ℤ} (h : SignedModEq m a b) (g : SignedModEq m b c) :
    SignedModEq m a c := by
  rcases h with h | h <;> rcases g with g | g
  · exact Or.inl (h.trans g)
  · exact Or.inr (h.trans g)
  · exact Or.inr (h.trans g.neg)
  · exact Or.inl (by simpa only [neg_neg] using h.trans g.neg)

theorem iff_dvd {m a b : ℤ} :
    SignedModEq m a b ↔ m ∣ a - b ∨ m ∣ a + b := by
  unfold SignedModEq
  rw [Int.modEq_comm, Int.modEq_iff_dvd, Int.modEq_comm, Int.modEq_iff_dvd,
    sub_neg_eq_add]

theorem sign_mul (m t b : ℤ) (ht : t = 1 ∨ t = -1) :
    SignedModEq m (t * b) b := by
  rcases ht with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

theorem natAbs (m a : ℤ) : SignedModEq m (a.natAbs : ℤ) a := by
  rw [Int.natCast_natAbs]
  rcases le_total 0 a with ha | ha
  · exact Or.inl (by rw [abs_of_nonneg ha])
  · exact Or.inr (by rw [abs_of_nonpos ha])

end SignedModEq

/-- The entire final sign chase in `index_residues` factors through this lemma. -/
theorem signed_index_chase {m u J t s p : ℤ}
    (huJ : SignedModEq m u J) (hus : u ≡ t * s [ZMOD m])
    (ht : t = 1 ∨ t = -1) (hsp : m ∣ s - p ∨ m ∣ s + p) :
    m ∣ J - p ∨ m ∣ J + p :=
  SignedModEq.iff_dvd.mp
    (huJ.symm.trans ((SignedModEq.of_modEq hus).trans
      ((SignedModEq.sign_mul m t s ht).trans (SignedModEq.iff_dvd.mpr hsp))))

/-- Absolute-value classification transports back to the original signed value. -/
theorem signed_of_natAbs {m y p : ℤ} (h : SignedModEq m (y.natAbs : ℤ) p) :
    SignedModEq m y p :=
  (SignedModEq.natAbs m y).symm.trans h

#print axioms signed_index_chase
#print axioms signed_of_natAbs

end DiophantineConsistency.ProofSimplification

import Std.Tactic

/-! Semantic certificates shared by distinct arithmetic representation backends. -/

namespace DiophantineConsistency.ArithmeticCertificates

theorem divMod_certificate_iff (q r n b : Nat) :
    (∃ s, n = q * b + r ∧ b = r + s + 1) ↔
      0 < b ∧ q = n / b ∧ r = n % b := by
  constructor
  · rintro ⟨s, hn, hb⟩
    have hb0 : 0 < b := by omega
    have h := (Nat.div_mod_unique (a := n) (d := q) (c := r) hb0).mpr
      ⟨by simpa [Nat.add_comm, Nat.mul_comm] using hn.symm, by omega⟩
    exact ⟨hb0, h.1.symm, h.2.symm⟩
  · rintro ⟨hb, rfl, rfl⟩
    exact ⟨b - n % b - 1, (Nat.div_add_mod' n b).symm,
      by have := Nat.mod_lt n hb; omega⟩

end DiophantineConsistency.ArithmeticCertificates

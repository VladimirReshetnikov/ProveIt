import DiophantineConsistency.ArithmeticCertificates

namespace DiophantineConsistency.ArithmeticCertificateChecks

open ArithmeticCertificates

/-- Exact public statement retained by both replacement wrappers. -/
theorem wrapper_statement (q r n b : Nat) :
    (∃ s, n = q * b + r ∧ b = r + s + 1) ↔
      0 < b ∧ q = n / b ∧ r = n % b :=
  divMod_certificate_iff q r n b

/-- The explicit slack enforces positivity; totalized division at zero
does not produce a certificate. -/
theorem no_zero_denominator (q r n : Nat) :
    ¬∃ s, n = q * 0 + r ∧ 0 = r + s + 1 := by
  rw [divMod_certificate_iff]
  simp

/-- The certificate determines the slack as well as quotient and remainder. -/
theorem certificate_unique {q r s q' r' s' n b : Nat}
    (h : n = q * b + r ∧ b = r + s + 1)
    (h' : n = q' * b + r' ∧ b = r' + s' + 1) :
    q = q' ∧ r = r' ∧ s = s' := by
  have hqr := (divMod_certificate_iff q r n b).mp ⟨s, h⟩
  have hqr' := (divMod_certificate_iff q' r' n b).mp ⟨s', h'⟩
  exact ⟨hqr.2.1.trans hqr'.2.1.symm, hqr.2.2.trans hqr'.2.2.symm, by omega⟩

/-- Every positive denominator yields the canonical arithmetic witness. -/
theorem canonical_certificate (n b : Nat) (hb : 0 < b) :
    ∃ s, n = (n / b) * b + n % b ∧ b = n % b + s + 1 :=
  (divMod_certificate_iff (n / b) (n % b) n b).mpr ⟨hb, rfl, rfl⟩

#print axioms ArithmeticCertificates.divMod_certificate_iff
#print axioms wrapper_statement
#print axioms no_zero_denominator
#print axioms certificate_unique
#print axioms canonical_certificate

end DiophantineConsistency.ArithmeticCertificateChecks

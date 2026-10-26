import DiophantineConsistency.CurrentCarrierArithmetic2011

/-! Same-signature proof candidates; no extra positivity hypothesis on K. -/
namespace DiophantineConsistency.RefactorPositiveZero

open CurrentMasks2011 CurrentCarrierArithmetic2011

/-- Lift a pointwise zero-set equivalence under the existing positivity guard. -/
theorem positiveZero_congr {n : ℕ} (P Q : MvPolynomial (Fin n) ℤ)
    (h : ∀ u : Fin n → ℤ, (∀ j, 0 < u j) →
      (MvPolynomial.eval u P = 0 ↔ MvPolynomial.eval u Q = 0)) :
    PositiveZero P ↔ PositiveZero Q := by
  exact exists_congr fun u => and_congr_right (h u)

theorem port_zero_pos (K : ℤ) : 0 < ports K 0 := by
  change 0 < (beta : ℤ)
  exact_mod_cast beta_pos

theorem positive_zero_69_iff_70 (K : ℤ) :
    PositiveZero (polynomial69 K) ↔ PositiveZero (polynomial70 K) := by
  apply positiveZero_congr
  intro u hu
  have h := ThirteenCarrier.positive_polynomial_zero_sets (ports K) u (port_zero_pos K) hu
  exact h.1.trans h.2.symm

theorem positive_zero_70_iff_71 (K : ℤ) :
    PositiveZero (polynomial70 K) ↔ PositiveZero (polynomial71 K) := by
  exact positiveZero_congr _ _ fun u hu =>
    (ThirteenCarrier.positive_polynomial_zero_sets (ports K) u (port_zero_pos K) hu).2

#print axioms positiveZero_congr
#print axioms positive_zero_69_iff_70
#print axioms positive_zero_70_iff_71

end DiophantineConsistency.RefactorPositiveZero

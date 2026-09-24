import Surreal.Algebra.NumberFieldTailoredGuard

/-!
# Choosing a numeral for existential number-field definitions

The radicand-selection clauses of `odg:def:rem:numberfieldideal`. A prime
nonsquare always exists; a root of the tailored sextic supplies a square
root of one of its three nonsquare natural radicands, possibly composite.
-/

namespace Surreal.NumberFieldTailoredGuard

/-- Every number field misses a square root of some prime. -/
theorem exists_prime_nonsquare (K : Type*) [Field K] [NumberField K] :
    ∃ δ : ℕ, δ.Prime ∧ ¬IsSquare (δ : K) :=
  ⟨(pair K).p, (pair K).admissible.1, (pair K).p_nonsquare⟩

/-- Any root of the tailored sextic supplies a suitable fixed natural radicand. -/
theorem exists_nonsquare_radicand_of_root (K : Type*) [Field K] [NumberField K]
    {L : Type*} [Field L] (r : L)
    (hr : TailoredIntersectivePolynomial.value (pair K).p (pair K).q r = 0) :
    ∃ δ : ℕ, (δ = (pair K).p ∨ δ = (pair K).q ∨ δ = (pair K).p * (pair K).q) ∧
      ¬IsSquare (δ : K) ∧ r ^ 2 = (δ : L) := by
  rcases mul_eq_zero.mp hr with hab | hc
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact ⟨(pair K).p, Or.inl rfl, (pair K).p_nonsquare, sub_eq_zero.mp ha⟩
    · exact ⟨(pair K).q, Or.inr (Or.inl rfl), (pair K).q_nonsquare, sub_eq_zero.mp hb⟩
  · exact ⟨(pair K).p * (pair K).q, Or.inr (Or.inr rfl),
      (pair K).pq_nonsquare, sub_eq_zero.mp hc⟩

end Surreal.NumberFieldTailoredGuard

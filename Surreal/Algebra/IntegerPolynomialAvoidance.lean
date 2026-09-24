import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Bounded avoidance of integer polynomial roots

The finite-satisfiability step of `odg:def:thm:saturation`: a finite family
of nonzero integer polynomials has a common nonroot among `0, …, D`,
where `D` is the sum of the degrees. The witness works in every
characteristic-zero commutative ring.
-/

namespace Surreal.IntegerPolynomialAvoidance

/-- A nonzero integer polynomial cannot vanish at every integer from zero to its degree. -/
theorem exists_nat_le_degree (p : Polynomial ℤ) (hp : p ≠ 0) :
    ∃ n : ℕ, n ≤ p.natDegree ∧ p.eval (n : ℤ) ≠ 0 := by
  by_contra! h
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p
    (f := fun i : Fin (p.natDegree + 1) => (i.val : ℤ))
  · intro a b hab
    exact Fin.ext (Int.ofNat_inj.mp hab)
  · intro i
    exact h i.val (Nat.le_of_lt_succ i.isLt)
  · simp

/-- Finitely many polynomials have a common nonroot bounded by their total degree. -/
theorem exists_nat_le_sum_degrees (s : Finset (Polynomial ℤ)) (hs : ∀ p ∈ s, p ≠ 0) :
    ∃ n : ℕ, n ≤ ∑ p ∈ s, p.natDegree ∧ ∀ p ∈ s, p.eval (n : ℤ) ≠ 0 := by
  obtain ⟨n, hn, hp⟩ := exists_nat_le_degree (∏ p ∈ s, p) (Finset.prod_ne_zero_iff.mpr hs)
  refine ⟨n, hn.trans (Polynomial.natDegree_prod_le s id), ?_⟩
  simpa only [Polynomial.eval_prod, Finset.prod_ne_zero_iff] using hp

/-- The same bounded ordinary integer avoids the roots in any characteristic-zero ring. -/
theorem exists_nat_le_sum_degrees_cast (R : Type*) [CommRing R] [CharZero R]
    (s : Finset (Polynomial ℤ)) (hs : ∀ p ∈ s, p ≠ 0) :
    ∃ n : ℕ, n ≤ ∑ p ∈ s, p.natDegree ∧
      ∀ p ∈ s, p.eval₂ (Int.castRingHom R) (n : R) ≠ 0 := by
  obtain ⟨n, hn, hp⟩ := exists_nat_le_sum_degrees s hs
  refine ⟨n, hn, fun p hps => ?_⟩
  have he := Polynomial.eval₂_at_apply (p := p) (Int.castRingHom R) (n : ℤ)
  change p.eval₂ (Int.castRingHom R) ((n : ℤ) : R) = ((p.eval (n : ℤ) : ℤ) : R) at he
  rw [Int.cast_natCast] at he
  rw [he]
  exact_mod_cast hp p hps

end Surreal.IntegerPolynomialAvoidance

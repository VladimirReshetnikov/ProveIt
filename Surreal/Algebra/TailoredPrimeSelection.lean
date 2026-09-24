import Surreal.Algebra.TailoredIntersectivePolynomial
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.Squarefree

/-!
# Selecting the tailored congruence primes outside a finite obstruction

The Dirichlet-theorem step of `odg:def:lem:tailored`. The three radicands
can simultaneously avoid any prescribed finite set. To finish the source's
number-field existence assertion, one must still prove finiteness of the
squarefree rational radicands that become squares in that number field.
-/

namespace Surreal.TailoredIntersectivePolynomial

/-- Dirichlet supplies admissible prime pairs with all radicands above any given bound. -/
theorem exists_admissible_gt (N : ℕ) :
    ∃ p q : ℕ, Admissible p q ∧ N < p ∧ N < q ∧ N < p * q := by
  obtain ⟨p, hpN, hp, hp8⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := 8) (a := 1) (by decide) (by simp)
  obtain ⟨q, hqN, hq, hq8p⟩ := Nat.forall_exists_prime_gt_and_modEq N
    (q := 8 * p) (a := 1) (mul_ne_zero (by decide) hp.ne_zero) (by simp)
  have hmod : 1 % (8 * p) = 1 := Nat.mod_eq_of_lt (by have := hp.two_le; omega)
  refine ⟨p, q, ⟨hp, hq, hp8, ?_⟩, hpN, hqN, ?_⟩
  · exact Eq.trans hq8p hmod
  · exact hqN.trans_le (Nat.le_mul_of_pos_left q hp.pos)

/-- A single finite forbidden set can be avoided by p, q and pq simultaneously. -/
theorem exists_admissible_avoiding (S : Finset ℕ) :
    ∃ p q : ℕ, Admissible p q ∧ p ∉ S ∧ q ∉ S ∧ p * q ∉ S := by
  obtain ⟨p, q, h, hp, hq, hpq⟩ := exists_admissible_gt (S.sup id)
  have hn (n : ℕ) (hn : S.sup id < n) : n ∉ S := by
    intro hm
    exact (not_lt_of_ge (Finset.le_sup (f := id) hm)) hn
  exact ⟨p, q, h, hn p hp, hn q hq, hn (p * q) hpq⟩

/-- A finite set of squarefree square radicands is the only remaining obstruction
needed by the prime-selection argument. -/
theorem exists_admissible_nonsquares_of_finite {K : Type*} [Field K]
    (hfinite : Set.Finite {d : ℕ | Squarefree d ∧ IsSquare (d : K)}) :
    ∃ p q : ℕ, Admissible p q ∧ ¬IsSquare (p : K) ∧ ¬IsSquare (q : K) ∧
      ¬IsSquare ((p * q : ℕ) : K) := by
  classical
  obtain ⟨p, q, h, hp, hq, hpq⟩ := exists_admissible_avoiding hfinite.toFinset
  have hn (d : ℕ) (hd : d ∉ hfinite.toFinset) (hs : Squarefree d) : ¬IsSquare (d : K) := by
    intro hsq
    exact hd (hfinite.mem_toFinset.mpr ⟨hs, hsq⟩)
  refine ⟨p, q, h, hn p hp h.1.squarefree, hn q hq h.2.1.squarefree, hn (p * q) hpq ?_⟩
  apply (Nat.squarefree_mul ?_).mpr ⟨h.1.squarefree, h.2.1.squarefree⟩
  exact (Nat.coprime_primes h.1 h.2.1).mpr (admissible_distinct_odd h).1

end Surreal.TailoredIntersectivePolynomial

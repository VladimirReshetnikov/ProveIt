import Mathlib.Algebra.Order.Antidiag.Pi
import Mathlib.Algebra.BigOperators.Group.List.Basic
open scoped BigOperators
example {M : Type*} [AddCommMonoid M] (n d : ℕ)
    (f : (Fin n → ℕ) → M) :
    ((List.Nat.antidiagonalTuple n d).map f).sum =
      ∑ k ∈ (Finset.univ : Finset (Fin n)).piAntidiag d, f k := by
  rw [Finset.piAntidiag_univ_fin_eq_antidiagonalTuple]
  rfl

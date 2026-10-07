import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

noncomputable def forecastShortGridEquiv (A : Type*) :
    (A → ℤ) ≃ (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) where
  toFun k a _ := k a
  invFun k a := k a ⟨∅, Finset.mem_univ _⟩
  left_inv _ := rfl
  right_inv k := by
    funext a row
    exact congrArg (k a) (Subsingleton.elim _ _)

theorem forecastShortGrid_tsum {A : Type*}
    (f : (A → ((Finset.univ : Finset (Finset Empty)) : Type) → ℤ) → ℂ) :
    (∑' k : A → ℤ, f (fun a _ => k a)) = ∑' grid, f grid :=
  (forecastShortGridEquiv A).tsum_eq f

end Erdos3.VectorPolynomial

end

end OAI

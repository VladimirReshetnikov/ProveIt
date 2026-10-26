import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Basic

/-!
One weighted finite-sum identity for the mass, word and convolution
interpretations of foldStencil. Collisions are retained: p is arbitrary.
-/
namespace DiophantineConsistency.FinitePushforward
open scoped BigOperators

theorem sum_fiber_mul {I K R : Type*} [Fintype I] [Fintype K] [DecidableEq K] [Semiring R]
    (p : I → K) (a : I → R) (w : K → R) :
    (∑ k, (∑ i, if p i = k then a i else 0) * w k) =
      ∑ i, a i * w (p i) := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

#print axioms sum_fiber_mul

end DiophantineConsistency.FinitePushforward

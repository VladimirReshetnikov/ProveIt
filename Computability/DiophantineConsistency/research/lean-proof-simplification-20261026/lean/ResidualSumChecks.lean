import DiophantineConsistency.ShortSystem
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! Proof-only candidate: the original residualSum definition is retained. -/
namespace DiophantineConsistency.ProofSimplification

theorem residualSum_zero_iff_short (n0 n1 na ns nk nt : ℤ) :
    ShortSystem.residualSum n0 n1 na ns nk nt = 0 ↔
      n0 = 1 ∧ n1 = 1 ∧ na = 1 ∧ ns = 1 ∧ nk * nt = 1 := by
  simpa [ShortSystem.residualSum, Fin.sum_univ_succ, Fin.forall_fin_succ, pow_two, sub_eq_zero,
    add_assoc] using
    (Finset.sum_mul_self_eq_zero_iff (Finset.univ : Finset (Fin 5))
      ![n0 - 1, n1 - 1, na - 1, ns - 1, nk * nt - 1])

#print axioms residualSum_zero_iff_short

end DiophantineConsistency.ProofSimplification

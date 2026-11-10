import DiophantineConsistency.Current14Carrier65QFields
import DiophantineConsistency.Current14Carrier65QDegree
import DiophantineConsistency.Current14Carrier65QCancel
import Mathlib.Tactic.FinCases

/-! Candidate actual Q-factor upper bound; not a whole-polynomial theorem. -/
namespace DiophantineConsistency.Current14Carrier65QActual

abbrev Poly := MvPolynomial (Fin 14) ℤ

noncomputable def core (p : Fin 4 → ℤ) : Carrier65.Core Poly :=
  Carrier65.core (fun j => (p j : Poly)) MvPolynomial.X

noncomputable def values (p : Fin 4 → ℤ) : Fin 5 → Poly :=
  ![(core p).X, (core p).a, (core p).c, (core p).H, MvPolynomial.X 13]

theorem values_degree (p : Fin 4 → ℤ) :
    ∀ j, (values p j).totalDegree ≤ Current14Carrier65QDegree.qWeights j := by
  intro j
  fin_cases j
  · change (core p).X.totalDegree ≤ 2
    exact Current14Carrier65QInputs.core_X_degree p
  · change (core p).a.totalDegree ≤ 6
    exact Current14Carrier65QInputs.core_a_degree p
  · change (core p).c.totalDegree ≤ 5
    exact Current14Carrier65QInputs.core_c_degree p
  · change (core p).H.totalDegree ≤ 6
    exact Current14Carrier65QInputs.core_H_degree p
  · change (MvPolynomial.X (13 : Fin 14) : Poly).totalDegree ≤ 1
    rw [MvPolynomial.totalDegree_X]

theorem Q_degree_le (p : Fin 4 → ℤ) : (core p).Q.totalDegree ≤ 18 := by
  have h := Current14Carrier65QDegree.q_degree_le (values p) (values_degree p)
  change (((core p).X + MvPolynomial.X 13 * (core p).H) ^ 2 +
    2 * (core p).a * (core p).c * ((core p).X + MvPolynomial.X 13 * (core p).H) -
    (core p).H * (core p).c ^ 2).totalDegree ≤ 18 at h
  have hc := Current14Carrier65QCancel.current_core
    (fun j => (p j : Poly)) (MvPolynomial.X : Fin 14 → Poly)
  change (core p).Q = ((core p).X + MvPolynomial.X 13 * (core p).H) ^ 2 +
    2 * (core p).a * (core p).c * ((core p).X + MvPolynomial.X 13 * (core p).H) -
    (core p).H * (core p).c ^ 2 at hc
  rw [hc]
  exact h

end DiophantineConsistency.Current14Carrier65QActual

#print axioms DiophantineConsistency.Current14Carrier65QActual.values_degree
#print axioms DiophantineConsistency.Current14Carrier65QActual.Q_degree_le

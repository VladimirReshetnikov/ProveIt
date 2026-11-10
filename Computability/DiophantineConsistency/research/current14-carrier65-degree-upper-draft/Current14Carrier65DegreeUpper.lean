import DiophantineConsistency.Current14Carrier65OtherFields
import DiophantineConsistency.Current14Carrier65QActual

/-! Candidate total-degree upper bound for the actual Carrier65 polynomial. -/
namespace DiophantineConsistency.Current14Carrier65DegreeUpper

theorem polynomial_degree_le (p : Fin 4 → ℤ) :
    (Carrier65.polynomial p).totalDegree ≤ 150 := by
  let d := Current14Carrier65QActual.core p
  have hP : d.P.totalDegree ≤ 22 := Current14Carrier65OtherFields.core_P_degree p
  have hQ : d.Q.totalDegree ≤ 18 := Current14Carrier65QActual.Q_degree_le p
  have hU : d.U.totalDegree ≤ 62 := Current14Carrier65OtherFields.core_U_degree p
  have hW : d.W.totalDegree ≤ 2 := Current14Carrier65OtherFields.core_W_degree p
  have hZ : d.Z.totalDegree ≤ 46 := Current14Carrier65OtherFields.core_Z_degree p
  have hdelta : d.delta.totalDegree ≤ 12 := Current14Carrier65OtherFields.core_delta_degree p
  have hPQ : (d.P * d.Q).totalDegree ≤ 40 :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hP hQ)
  have hPQU : (d.P * d.Q * d.U).totalDegree ≤ 102 :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hPQ hU)
  have hPQUW : (d.P * d.Q * d.U * d.W).totalDegree ≤ 104 :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hPQU hW)
  have hPQUWZ : (d.P * d.Q * d.U * d.W * d.Z).totalDegree ≤ 150 :=
    (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hPQUW hZ)
  change (d.P * d.Q * d.U * d.W * d.Z - d.delta).totalDegree ≤ 150
  exact (MvPolynomial.totalDegree_sub _ _).trans (max_le hPQUWZ (hdelta.trans (by decide)))

end DiophantineConsistency.Current14Carrier65DegreeUpper

#print axioms DiophantineConsistency.Current14Carrier65DegreeUpper.polynomial_degree_le

import DiophantineConsistency.Current14Carrier65DiagonalUZ
import DiophantineConsistency.Current14Carrier65DiagonalQ
import DiophantineConsistency.Current14Carrier65DiagonalW

/-! Candidate whole all-equal-axis degree; multivariate transport is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalWhole
open Sign17UnivariateDegree Sign17AxisDegreeRoot Current14Carrier65DiagonalBinding
  Current14Carrier65DiagonalCoreBinding

def axisValue (p : Fin 4 → ℤ) : P :=
  Carrier65.value (fun j => Polynomial.C (p j)) axisVars

theorem axis_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisValue p).natDegree = 150 := by
  let d := axisCore p
  have hP : d.P.natDegree = 22 := Current14Carrier65DiagonalP.P_degree p hp
  have hQ : d.Q.natDegree = 18 := Current14Carrier65DiagonalQ.Q_degree p hp
  have hU : d.U.natDegree = 62 := Current14Carrier65DiagonalUZ.U_degree p hp
  have hW : d.W.natDegree = 2 := Current14Carrier65DiagonalW.actual_W_degree p
  have hZ : d.Z.natDegree = 46 := Current14Carrier65DiagonalUZ.Z_degree p hp
  have hd : d.delta.natDegree = 12 := delta_degree p hp
  have hPQ : (d.P * d.Q).natDegree = 40 := by
    simpa using degree_product d.P d.Q 22 18 hP hQ (by decide) (by decide)
  have hPQU : (d.P * d.Q * d.U).natDegree = 102 := by
    simpa using degree_product (d.P * d.Q) d.U 40 62 hPQ hU (by decide) (by decide)
  have hPQUW : (d.P * d.Q * d.U * d.W).natDegree = 104 := by
    simpa using degree_product (d.P * d.Q * d.U) d.W 102 2 hPQU hW (by decide) (by decide)
  have hprod : (d.P * d.Q * d.U * d.W * d.Z).natDegree = 150 := by
    simpa using degree_product (d.P * d.Q * d.U * d.W) d.Z 104 46 hPQUW hZ
      (by decide) (by decide)
  have hlt : d.delta.natDegree < (d.P * d.Q * d.U * d.W * d.Z).natDegree := by omega
  change (d.P * d.Q * d.U * d.W * d.Z - d.delta).natDegree = 150
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hprod]

end DiophantineConsistency.Current14Carrier65DiagonalWhole

#print axioms DiophantineConsistency.Current14Carrier65DiagonalWhole.axis_degree

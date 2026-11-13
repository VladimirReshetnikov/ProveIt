import DiophantineConsistency.Current14Carrier65DiagonalP
import DiophantineConsistency.Current14Carrier65QCancel

/-! Candidate strict-dominance proof of actual diagonal Q degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalQ
open Sign17UnivariateDegree Sign17AxisDegreeRoot Current14Carrier65DiagonalBinding
  Current14Carrier65DiagonalCoreBinding

theorem Q_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).Q.natDegree = 18 := by
  let d := axisCore p
  have hx : d.X.natDegree = 2 := X_degree p hp
  have ha : d.a.natDegree = 6 := a_degree p hp
  have hc : d.c.natDegree = 5 := c_degree p hp
  have hH : d.H.natDegree = 6 := H_degree p hp
  have hgH : ((Polynomial.X : P) * d.H).natDegree = 7 := by
    simpa using degree_product (Polynomial.X : P) d.H 1 6 Polynomial.natDegree_X hH
      (by decide) (by decide)
  have hroot : (d.X + (Polynomial.X : P) * d.H).natDegree = 7 := by
    rw [add_comm]
    exact degree_sum _ _ 7 2 hgH hx (by decide)
  have hroot2 : ((d.X + (Polynomial.X : P) * d.H) ^ 2).natDegree = 14 := by
    simpa [pow_two] using degree_product (d.X + (Polynomial.X : P) * d.H)
      (d.X + (Polynomial.X : P) * d.H) 7 7 hroot hroot (by decide) (by decide)
  have hac : (d.a * d.c).natDegree = 11 := by
    simpa using degree_product d.a d.c 6 5 ha hc (by decide) (by decide)
  have hacroot : (d.a * d.c * (d.X + (Polynomial.X : P) * d.H)).natDegree = 18 := by
    simpa using degree_product (d.a * d.c) (d.X + (Polynomial.X : P) * d.H) 11 7
      hac hroot (by decide) (by decide)
  have hscaled : ((2 : P) * d.a * d.c * (d.X + (Polynomial.X : P) * d.H)).natDegree = 18 := by
    have hn := ne_zero_of_positive_degree _ _ hacroot (by decide)
    have htwo : (Polynomial.C (2 : ℤ) : P) ≠ 0 := Polynomial.C_ne_zero.mpr (by decide)
    have h := product_degree (Polynomial.C (2 : ℤ))
      (d.a * d.c * (d.X + (Polynomial.X : P) * d.H)) htwo hn
    simpa [mul_assoc, hacroot] using h
  have hc2 : (d.c ^ 2).natDegree = 10 := by
    simpa [pow_two] using degree_product d.c d.c 5 5 hc hc (by decide) (by decide)
  have hthird : (d.H * d.c ^ 2).natDegree = 16 := by
    simpa using degree_product d.H (d.c ^ 2) 6 10 hH hc2 (by decide) (by decide)
  have hsum : ((d.X + (Polynomial.X : P) * d.H) ^ 2 +
      (2 : P) * d.a * d.c * (d.X + Polynomial.X * d.H)).natDegree = 18 := by
    rw [add_comm]
    exact degree_sum _ _ 18 14 hscaled hroot2 (by decide)
  have hlt : (d.H * d.c ^ 2).natDegree <
      ((d.X + (Polynomial.X : P) * d.H) ^ 2 +
        (2 : P) * d.a * d.c * (d.X + Polynomial.X * d.H)).natDegree := by omega
  have hid := Current14Carrier65QCancel.current_core
    (fun j => Polynomial.C (p j)) axisVars
  change d.Q = (d.X + (Polynomial.X : P) * d.H) ^ 2 +
    (2 : P) * d.a * d.c * (d.X + Polynomial.X * d.H) - d.H * d.c ^ 2 at hid
  rw [hid, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hsum]

end DiophantineConsistency.Current14Carrier65DiagonalQ

#print axioms DiophantineConsistency.Current14Carrier65DiagonalQ.Q_degree

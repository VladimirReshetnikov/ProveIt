import DiophantineConsistency.Current14Carrier65DiagonalP

/-! Candidate strict-dominance proof of actual diagonal U and Z degrees. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalUZ
open Sign17UnivariateDegree Sign17AxisDegreeRoot Current14Carrier65DiagonalBinding
  Current14Carrier65DiagonalCoreBinding

theorem V_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).V.natDegree = 8 := by
  let d := axisCore p
  have hc : d.c.natDegree = 5 := c_degree p hp
  have hr : d.rank.natDegree ≤ 4 := Current14Carrier65DiagonalRank.rank_degree_le p
  have hcx : (d.c * (Polynomial.X : P)).natDegree = 6 := by
    simpa using degree_product d.c (Polynomial.X : P) 5 1 hc Polynomial.natDegree_X
      (by decide) (by decide)
  have hlt : d.rank.natDegree < (d.c * (Polynomial.X : P)).natDegree := by omega
  have hinner : (d.c * (Polynomial.X : P) - d.rank).natDegree = 6 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hcx]
  have hm : ((Polynomial.X : P) ^ 2 * (d.c * Polynomial.X - d.rank)).natDegree = 8 := by
    simpa using degree_product ((Polynomial.X : P) ^ 2) (d.c * Polynomial.X - d.rank) 2 6
      (by simp) hinner (by decide) (by decide)
  have hlast : d.c.natDegree < ((Polynomial.X : P) ^ 2 * (d.c * Polynomial.X - d.rank)).natDegree := by omega
  change (((Polynomial.X : P) ^ 2 * (d.c * Polynomial.X - d.rank)) - d.c).natDegree = 8
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlast, hm]

theorem S_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).S.natDegree = 23 := by
  let d := axisCore p
  have hd : d.delta.natDegree = 12 := delta_degree p hp
  have hc : d.c.natDegree = 5 := c_degree p hp
  have hxdelta : ((Polynomial.X : P) * d.delta).natDegree = 13 := by
    simpa using degree_product (Polynomial.X : P) d.delta 1 12 Polynomial.natDegree_X hd
      (by decide) (by decide)
  have hc2 : (d.c ^ 2).natDegree = 10 := by
    simpa [pow_two] using degree_product d.c d.c 5 5 hc hc (by decide) (by decide)
  change (((Polynomial.X : P) * d.delta) * d.c ^ 2).natDegree = 23
  simpa using degree_product ((Polynomial.X : P) * d.delta) (d.c ^ 2) 13 10 hxdelta hc2
    (by decide) (by decide)

theorem U_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).U.natDegree = 62 := by
  let d := axisCore p
  have hv : d.V.natDegree = 8 := V_degree p hp
  have hs : d.S.natDegree = 23 := S_degree p hp
  have hv2 : (d.V ^ 2).natDegree = 16 := by
    simpa [pow_two] using degree_product d.V d.V 8 8 hv hv (by decide) (by decide)
  have hx2 : ((Polynomial.X : P) ^ 2).natDegree = 2 := by simp
  have hlt : ((Polynomial.X : P) ^ 2).natDegree < (d.V ^ 2).natDegree := by omega
  have hinner : (d.V ^ 2 - (Polynomial.X : P) ^ 2).natDegree = 16 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hv2]
  have hs2 : (d.S ^ 2).natDegree = 46 := by
    simpa [pow_two] using degree_product d.S d.S 23 23 hs hs (by decide) (by decide)
  have hm : (d.S ^ 2 * (d.V ^ 2 - (Polynomial.X : P) ^ 2)).natDegree = 62 := by
    simpa using degree_product (d.S ^ 2) (d.V ^ 2 - (Polynomial.X : P) ^ 2) 46 16 hs2 hinner
      (by decide) (by decide)
  change (d.S ^ 2 * (d.V ^ 2 - (Polynomial.X : P) ^ 2) + (Polynomial.X : P) ^ 2).natDegree = 62
  exact degree_sum _ _ 62 2 hm hx2 (by decide)

theorem Z_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).Z.natDegree = 46 := by
  let d := axisCore p
  have hd : d.delta.natDegree = 12 := delta_degree p hp
  have hs : d.S.natDegree = 23 := S_degree p hp
  have hleft : (d.delta * (Polynomial.X : P) ^ 2).natDegree = 14 := by
    simpa using degree_product d.delta ((Polynomial.X : P) ^ 2) 12 2 hd (by simp)
      (by decide) (by decide)
  have hright : (d.S ^ 2).natDegree = 46 := by
    simpa [pow_two] using degree_product d.S d.S 23 23 hs hs (by decide) (by decide)
  have hlt : (d.delta * (Polynomial.X : P) ^ 2).natDegree < (d.S ^ 2).natDegree := by omega
  change (d.delta * (Polynomial.X : P) ^ 2 - d.S ^ 2).natDegree = 46
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt, hright]

end DiophantineConsistency.Current14Carrier65DiagonalUZ

#print axioms DiophantineConsistency.Current14Carrier65DiagonalUZ.V_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalUZ.S_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalUZ.U_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalUZ.Z_degree

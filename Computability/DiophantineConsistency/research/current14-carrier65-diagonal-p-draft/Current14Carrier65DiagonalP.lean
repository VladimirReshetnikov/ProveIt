import DiophantineConsistency.Current14Carrier65DiagonalRank
import DiophantineConsistency.Current14Carrier65DiagonalCoreBinding

/-! Candidate strict-dominance proof of the actual diagonal P factor's degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Current14Carrier65DiagonalP
open Sign17UnivariateDegree Sign17AxisDegreeRoot Current14Carrier65DiagonalBinding
  Current14Carrier65DiagonalCoreBinding

theorem k_degree (p : Fin 4 → ℤ) : (axisCore p).k.natDegree = 1 := by
  change ((Polynomial.X : P) + Polynomial.X).natDegree = 1
  have h : (Polynomial.X : P) + Polynomial.X = Polynomial.C (2 : ℤ) * Polynomial.X := by
    simp [two_mul]
  rw [h]
  exact Polynomial.natDegree_C_mul_X 2 (by decide)

theorem ell_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).ell.natDegree = 11 := by
  let d := axisCore p
  have hE : d.E.natDegree = 6 := E_degree p hp
  have hk : d.k.natDegree = 1 := k_degree p
  have hY : d.Y.natDegree = 4 := Y_degree p hp
  have hEK : (d.E * d.k).natDegree = 7 := by
    simpa using degree_product d.E d.k 6 1 hE hk (by decide) (by decide)
  change ((d.E * d.k) * d.Y).natDegree = 11
  simpa using degree_product (d.E * d.k) d.Y 7 4 hEK hY (by decide) (by decide)

theorem tau_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).tau.natDegree = 7 := by
  let d := axisCore p
  have hE : d.E.natDegree = 6 := E_degree p hp
  have hk : d.k.natDegree = 1 := k_degree p
  have hr : d.rank.natDegree ≤ 4 := Current14Carrier65DiagonalRank.rank_degree_le p
  have hm : (d.E * (Polynomial.X : P)).natDegree = 7 := by
    simpa using degree_product d.E (Polynomial.X : P) 6 1 hE Polynomial.natDegree_X
      (by decide) (by decide)
  have hs : (d.E * (Polynomial.X : P) + d.k).natDegree = 7 :=
    degree_sum _ _ 7 1 hm hk (by decide)
  have hlt : d.rank.natDegree < (d.E * (Polynomial.X : P) + d.k).natDegree := by omega
  change (d.E * (Polynomial.X : P) + d.k - d.rank).natDegree = 7
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hs]

theorem P_degree (p : Fin 4 → ℤ) (hp : p 0 ≠ 0) : (axisCore p).P.natDegree = 22 := by
  let d := axisCore p
  have ht : d.tau.natDegree = 7 := tau_degree p hp
  have hl : d.ell.natDegree = 11 := ell_degree p hp
  have hk : d.k.natDegree = 1 := k_degree p
  have hplus : (d.ell + d.k).natDegree = 11 := degree_sum _ _ 11 1 hl hk (by decide)
  have hright : (d.ell * (d.ell + d.k)).natDegree = 22 := by
    simpa using degree_product d.ell (d.ell + d.k) 11 11 hl hplus (by decide) (by decide)
  have hleft : (d.tau ^ 2).natDegree = 14 := by
    simpa [pow_two] using degree_product d.tau d.tau 7 7 ht ht (by decide) (by decide)
  have hlt : (d.tau ^ 2).natDegree < (d.ell * (d.ell + d.k)).natDegree := by omega
  change (d.tau ^ 2 - d.ell * (d.ell + d.k)).natDegree = 22
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt hlt, hright]

end DiophantineConsistency.Current14Carrier65DiagonalP

#print axioms DiophantineConsistency.Current14Carrier65DiagonalP.k_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalP.ell_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalP.tau_degree
#print axioms DiophantineConsistency.Current14Carrier65DiagonalP.P_degree

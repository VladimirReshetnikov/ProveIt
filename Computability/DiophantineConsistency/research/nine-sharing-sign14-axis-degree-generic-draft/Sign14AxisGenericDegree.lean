import DiophantineConsistency.Sign17AxisDegreeScale

/-! SOURCE-ONLY: a conditional generic degree ingredient. The rank and
correction bounds are hypotheses; binding to actual staged nodes is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisGenericDegree
open Sign17UnivariateDegree Sign17AxisDegreeBase Sign17AxisDegreeRoot
  Sign17AxisDegreeScale

abbrev inner (z : ℤ) (correction rank : P) : P :=
  (shift * shift) * ((shift * u z + correction) - rank) - u z

/-- Degree of the substituted inner expression, assuming only upper bounds
    on the lower-order correction and rank. -/
theorem inner_degree (z : ℤ) (hz : z ≠ 0) (correction rank : P)
    (hc : correction.natDegree ≤ 2) (hr : rank.natDegree ≤ 4) :
    (inner z correction rank).natDegree = 8 := by
  have hm : (shift * u z).natDegree = 6 := by
    simpa using degree_product shift (u z) 1 5 shift_degree
      (u_degree z hz) (by decide) (by decide)
  have ha : (shift * u z + correction).natDegree = 6 :=
    degree_sum _ _ 6 correction.natDegree hm rfl (by omega)
  have hb : ((shift * u z + correction) - rank).natDegree = 6 := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by omega :
      rank.natDegree < (shift * u z + correction).natDegree)]
    exact ha
  have hs : (shift * shift).natDegree = 2 := by
    simpa using degree_product shift shift 1 1 shift_degree shift_degree
      (by decide) (by decide)
  have hd : ((shift * shift) * ((shift * u z + correction) - rank)).natDegree = 8 := by
    simpa using degree_product (shift * shift) _ 2 6 hs hb (by decide) (by decide)
  change ((shift * shift) * ((shift * u z + correction) - rank) - u z).natDegree = 8
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by
    have hu := u_degree z hz
    omega : (u z).natDegree < ((shift * shift) * ((shift * u z + correction) - rank)).natDegree)]
  exact hd

end DiophantineConsistency.Sign14AxisGenericDegree
#print axioms DiophantineConsistency.Sign14AxisGenericDegree.inner_degree

import DiophantineConsistency.Sign14AxisGenericDegree

/-! SOURCE-ONLY: generic Na-degree ingredient; staged binding is separate. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisGenericNaDegree
open Sign17UnivariateDegree Sign17AxisDegreeBase Sign17AxisDegreeRoot
  Sign17AxisDegreeScale Sign14AxisGenericDegree

abbrev row (z : ℤ) (correction rank : P) : P :=
  (shift * shift - (scale z * scale z) *
    (shift * shift - inner z correction rank * inner z correction rank)) - 1

theorem row_degree (z : ℤ) (hz : z ≠ 0) (correction rank : P)
    (hc : correction.natDegree ≤ 2) (hr : rank.natDegree ≤ 4) :
    (row z correction rank).natDegree = 62 := by
  have hf : (shift * shift).natDegree = 2 := by
    simpa using degree_product shift shift 1 1 shift_degree shift_degree (by decide) (by decide)
  have hi : (inner z correction rank).natDegree = 8 := inner_degree z hz correction rank hc hr
  have hi2 : (inner z correction rank * inner z correction rank).natDegree = 16 := by
    simpa using degree_product _ _ 8 8 hi hi (by decide) (by decide)
  have hd : (shift * shift - inner z correction rank * inner z correction rank).natDegree = 16 := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by omega :
      (shift * shift).natDegree < (inner z correction rank * inner z correction rank).natDegree)]
    exact hi2
  have hs : (scale z * scale z).natDegree = 46 := by
    simpa using degree_product (scale z) (scale z) 23 23
      (scale_degree z hz) (scale_degree z hz) (by decide) (by decide)
  have hp : ((scale z * scale z) *
      (shift * shift - inner z correction rank * inner z correction rank)).natDegree = 62 := by
    simpa using degree_product _ _ 46 16 hs hd (by decide) (by decide)
  have hq : (shift * shift - (scale z * scale z) *
      (shift * shift - inner z correction rank * inner z correction rank)).natDegree = 62 := by
    rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt (by omega :
      (shift * shift).natDegree < ((scale z * scale z) *
        (shift * shift - inner z correction rank * inner z correction rank)).natDegree)]
    exact hp
  change (shift * shift - (scale z * scale z) *
    (shift * shift - inner z correction rank * inner z correction rank) - 1).natDegree = 62
  rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt (by simp [hq])]
  exact hq
end DiophantineConsistency.Sign14AxisGenericNaDegree
#print axioms DiophantineConsistency.Sign14AxisGenericNaDegree.row_degree

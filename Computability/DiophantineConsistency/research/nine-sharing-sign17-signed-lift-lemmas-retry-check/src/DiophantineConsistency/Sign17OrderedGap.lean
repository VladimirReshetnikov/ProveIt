import DiophantineConsistency.Sign20CurrentExpressionDef

/-! SOURCE-ONLY: generic ordered-ring facts for the sign17 signed lift. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17OrderedGap

theorem root_positive {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (beta x rest : R)
    (hb : 0 < beta) (hx : 0 ≤ x) (hr : 0 ≤ rest) :
    0 < beta * (x + 1) + rest := by
  have ht : 0 < x + 1 := by linarith
  have hp := mul_pos hb ht
  linarith

theorem scale_positive {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (k root : R)
    (hk : 0 ≤ k) (hr : 0 < root) :
    0 < (k + 1) * root * (root + 2) := by
  have hk' : 0 < k + 1 := by linarith
  have hr' : 0 < root + 2 := by linarith
  exact mul_pos (mul_pos hk' hr) hr'

theorem difference_nonnegative {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (F S V : R) (hF : 1 ≤ F) (hS : 0 < S)
    (hNa : F*F - (S*S)*(F*F - V*V) - 1 = 0) :
    0 ≤ F*F - V*V := by
  by_contra h
  have hd : F*F - V*V < 0 := lt_of_not_ge h
  have hp : (S*S)*(F*F - V*V) < 0 := mul_neg_of_pos_of_neg (mul_pos hS hS) hd
  nlinarith [sq_nonneg (F-1)]
end DiophantineConsistency.Sign17OrderedGap
#print axioms DiophantineConsistency.Sign17OrderedGap.root_positive
#print axioms DiophantineConsistency.Sign17OrderedGap.scale_positive
#print axioms DiophantineConsistency.Sign17OrderedGap.difference_nonnegative

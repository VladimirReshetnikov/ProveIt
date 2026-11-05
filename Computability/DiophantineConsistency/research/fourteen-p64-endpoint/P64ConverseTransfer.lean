import P64ConverseResidue

/-! Simple canonical-witness transfers for the P64 converse. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace P64ConverseTransfer

section Domain
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Remove the common nonzero `q` from the canonical transport identity. -/
theorem transport_unscale (q X K C F b z w : R) (hq : q≠0)
    (hX : X=q*w)
    (htransport : C*(X+K*q)-F*q=b*(q*z)) :
    (K+w)*C=F+z*b := by
  apply mul_left_cancel₀ hq
  linear_combination htransport-C*hX
end Domain

section Order
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The canonical first root lies strictly above the offset that is
subtracted to form P64's positive rho coordinate. -/
theorem first_offset_pos (tau ell k s : R)
    (htau : tau*tau=1+ell*(ell+k)) (htau0 : 0≤tau)
    (hs0 : 0≤s) (hsk : 3*s≤k) (hse : s≤ell) :
    ell+s<tau := by
  by_contra hn
  have hle : tau≤ell+s := le_of_not_gt hn
  have hell : 0≤ell := le_trans hs0 hse
  have hsquare := mul_le_mul hle hle htau0 (show 0≤ell+s by linarith)
  nlinarith

/-- The canonical auxiliary ordinate strictly exceeds its root, so their
difference is a positive witness. -/
theorem auxiliary_offset_pos (I w y : R)
    (hnorm : I*I*w*w+y*y=1+I*I*y*y) (hy : 2≤y) (hw : 0≤w) :
    w<y := by
  by_contra hn
  have hle : y≤w := le_of_not_gt hn
  have hsquare := mul_le_mul hle hle (by linarith) hw
  nlinarith [sq_nonneg I]
end Order

#print axioms P64ConverseTransfer.transport_unscale
#print axioms P64ConverseTransfer.first_offset_pos
#print axioms P64ConverseTransfer.auxiliary_offset_pos
end P64ConverseTransfer

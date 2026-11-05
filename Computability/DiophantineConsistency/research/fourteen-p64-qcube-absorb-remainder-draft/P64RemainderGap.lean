import DiophantineConsistency.ModelDifferenceRing

/-! Draft: a first-root remainder bound for a possible further absorption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace P64RemainderGap
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem remainder_gt (ell k s r : R)
    (hs : 0≤s) (hr : 0≤r) (hell : s*s≤ell) (hk : 2*s+1≤k)
    (hnorm : (ell+r)*(ell+r)=1+ell*(ell+k)) : s<r := by
  have hell0 : 0≤ell := by nlinarith [sq_nonneg s]
  by_contra hn
  have hrs : r≤s := le_of_not_gt hn
  have hr2 : r*r≤s*s := mul_le_mul hrs hrs hr hs
  have hgap : 0≤ell*(k-2*s-1) := mul_nonneg hell0 (by linarith)
  have hrem : 0≤2*ell*(s-r) := mul_nonneg (by positivity) (by linarith)
  nlinarith only [hnorm,hr2,hgap,hrem,hell]

#print axioms P64RemainderGap.remainder_gt
end P64RemainderGap

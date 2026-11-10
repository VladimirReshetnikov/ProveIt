import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A positive ordered-ring change from the squared to the linear trace. -/
set_option autoImplicit false
noncomputable section
namespace Trace75PositiveTraceShift
variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

theorem positive_shift (c f d T r : R)
    (hc : 0<c) (hf : 0<f) (hr : 0≤r)
    (hshape : f=1+c*d) (hv : 0<f*f*(c*T-r)-c) :
    0<f*T-d*r ∧
      f*(c*(f*T-d*r)-r)-c = f*f*(c*T-r)-c := by
  have hf2 : 0<f*f := mul_pos hf hf
  have hct : 0<c*T-r := by
    apply (mul_pos_iff_of_pos_left hf2).mp
    linarith
  have hpos : 0<f*(c*T-r)+r := add_pos_of_pos_of_nonneg (mul_pos hf hct) hr
  have hid : c*(f*T-d*r)=f*(c*T-r)+r := by rw [hshape]; ring
  have hshift : 0<f*T-d*r := pos_of_mul_pos_right (by rw [hid]; exact hpos) (le_of_lt hc)
  refine ⟨hshift,?_⟩
  rw [hshape]
  ring

#print axioms Trace75PositiveTraceShift.positive_shift
end Trace75PositiveTraceShift

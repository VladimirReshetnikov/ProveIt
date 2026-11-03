import Mathlib.Tactic.Ring

/-! Algebraic components of the proposed 79-row coordinate normalization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Mask79Gauge
variable {R : Type*} [CommRing R]

theorem preserve_rank_and_carrier (q k w F C n v d : R) :
    q*(q-(F+d))-(C-q*d) = q*(q-F)-C ∧
    (n-v*(q*(k+w)+1)*d)-v*((k+w)*(C-q*d)-(F+d)) =
      n-v*((k+w)*C-F) := by
  constructor <;> ring

#print axioms Mask79Gauge.preserve_rank_and_carrier
end Mask79Gauge

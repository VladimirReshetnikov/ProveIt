import DiophantineConsistency.AdaptiveDirectOrdinate86Transport

/-! Conditional gap-coordinate arithmetic in every IΣ₁ model. This module does
not yet bind the 85-gate literal or prove its required reverse bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85Arithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive original gap is a positive new coordinate. -/
theorem forward_gap (q F alpha : V) (h : F+alpha<q) :
    let C := q-(F+alpha)
    0<C ∧ F+alpha+C=q := by
  dsimp
  constructor
  · exact tsub_pos_iff_lt.mpr h
  · simpa only [add_comm] using tsub_add_cancel_of_le (le_of_lt h)

/-- The reverse bound is the extra condition needed to recover positive alpha. -/
theorem reverse_gap (q F C : V) (h : F+C<q) :
    let alpha := q-(F+C)
    0<alpha ∧ F+alpha+C=q := by
  dsimp
  constructor
  · exact tsub_pos_iff_lt.mpr h
  · have he := tsub_add_cancel_of_le (le_of_lt h)
    calc
      F+(q-(F+C))+C=(F+C)+(q-(F+C)) := by ring
      _=q := by simpa only [add_comm] using he

/-- The rank seed agrees under either direction of that coordinate change. -/
theorem rank_seed_identity (q qm F alpha C : V) (hq : q=1+qm)
    (h : F+alpha+C=q) : alpha+(q-F)*qm+C=(q-F)*q := by
  have hF : F≤q := by rw [←h]; simp
  have hqF : F+(q-F)=q := by simpa only [add_comm] using tsub_add_cancel_of_le hF
  have he : alpha+C=q-F := by
    apply add_left_cancel (a:=F)
    calc
      F+(alpha+C)=q := by simpa only [add_assoc] using h
      _=F+(q-F) := hqF.symm
  calc
    alpha+(q-F)*qm+C=(alpha+C)+(q-F)*qm := by ring
    _=(q-F)+(q-F)*qm := by rw [he]
    _=(q-F)*q := by rw [hq]; ring
end DiophantineConsistency.AdaptiveGap85Arithmetic

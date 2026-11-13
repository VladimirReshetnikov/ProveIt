import DiophantineConsistency.ArithmeticPellCongruences

/-! The first-Pell seed supplies the quotient required by the adaptive main
correction. The index and ordinate assumptions here are exactly the relations
exposed by the seed; this theorem does not assert their construction. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionCorrection2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual scaled seed ordinate yields an additive, hence non-truncated,
quotient for the adaptive main correction. -/
theorem correction_quotient (q X Y sY R k time : V)
    (hX : 0<X) (hY : 0<Y) (hYq : Y=sY*q^3)
    (hR : R+1=2*time)
    (hk : k=2*ycoord time (2*(X*Y*Y-1)+1)) :
    ∃ t : V, k=R+1+(Y*q^2)*t := by
  have hQ : (1:V) ≤ X*Y*Y := pos_iff_one_le.mp (mul_pos (mul_pos hX hY) hY)
  have hsub : X*Y*Y-1+1=X*Y*Y := tsub_add_cancel_of_le hQ
  have hb : (2*(X*Y*Y-1)+1)+1=2*(X*Y*Y) := by
    calc
      _=2*(X*Y*Y-1+1) := by ring
      _=2*(X*Y*Y) := by rw [hsub]
  obtain ⟨s,hs⟩ := first_transport time (2*(X*Y*Y-1)+1) (X*Y*Y) R k hb hk hR
  refine ⟨4*X*(sY*q)*s, ?_⟩
  rw [hs]
  congr 1
  rw [hYq]
  ring
end DiophantineConsistency.ArithmeticAdaptiveConstructionCorrection2011

import DiophantineConsistency.ArithmeticPellCongruences

/-! Exact natural μ² quotient for a scaled first Pell ordinate. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositiveScaledOffsetGeneric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem scaled_offset (X Y mu r : V) (hX : 0<X) (hY : 0<Y) (hmu : 0<mu) :
    let P:=X*(mu*Y)*(mu*Y)
    let K:=2*ycoord (r+1) (2*(P-1)+1)
    ∃ rho : V, K=(2*r+1)+1+(mu*mu)*rho := by
  let P:=X*(mu*Y)*(mu*Y)
  let B:=2*(P-1)+1
  have hP : 0<P := mul_pos (mul_pos hX (mul_pos hmu hY)) (mul_pos hmu hY)
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hdiv : (2*P)∣B+1 := by
    refine ⟨1,?_⟩
    calc
      B+1=2*(P-1+1) := by dsimp [B]; ring
      _=2*P := by rw [hP1]
      _=2*P*1 := by ring
  obtain ⟨_z,s,_hx,hys⟩ := residue_quotients (r+1) B (2*P) hdiv
  refine ⟨4*X*Y*Y*s,?_⟩
  change 2*ycoord (r+1) B=(2*r+1)+1+(mu*mu)*(4*X*Y*Y*s)
  rw [hys]
  dsimp [P]
  ring

#print axioms TenPositiveScaledOffsetGeneric.scaled_offset
end TenPositiveScaledOffsetGeneric

import DiophantineConsistency.ArithmeticPellCongruences

/-! The first seed's excess index is divisible by the XY carrier factor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace75SeedOffset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem offset_divisible (X Y r : V) (hX : 0<X) (hY : 0<Y) :
    ∃ rho : V,
      2*ycoord (r+1) (2*(X*Y*Y-1)+1)=(2*r+1)+1+(X*Y)*rho := by
  let P := X*Y*Y
  let B := 2*(P-1)+1
  have hP : 0<P := by dsimp [P]; exact mul_pos (mul_pos hX hY) hY
  have hP1 : P-1+1=P := tsub_add_cancel_of_le (pos_iff_one_le.mp hP)
  have hB : B+1=2*P := calc
    B+1=2*(P-1+1) := by dsimp [B]; ring
    _=2*P := by rw [hP1]
  have hdiv : 2*P∣B+1 := ⟨1,by rw [hB,mul_one]⟩
  obtain ⟨_x,s,_hx,hy⟩ := residue_quotients (r+1) B (2*P) hdiv
  refine ⟨4*Y*s,?_⟩
  change 2*ycoord (r+1) B=(2*r+1)+1+(X*Y)*(4*Y*s)
  rw [hy]
  dsimp [P]
  ring

#print axioms Trace75SeedOffset.offset_divisible
end Trace75SeedOffset

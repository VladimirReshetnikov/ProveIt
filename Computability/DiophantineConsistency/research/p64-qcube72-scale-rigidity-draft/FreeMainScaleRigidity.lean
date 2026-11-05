import DiophantineConsistency.ArithmeticPellCongruences

/-! Unchecked draft: two roots at the same scale have the same index and carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainScaleRigidity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem same_rank_root_carrier (a X Y c R R' g g' h h' : V)
    (hy : ycoord R a=c) (hy' : ycoord R' a=c)
    (hx : xcoord R a=g) (hx' : xcoord R' a=g')
    (hcar : (Y*Y)*g=(Y*Y)*(X+a*c)+(4*a+3)*h)
    (hcar' : (Y*Y)*g'=(Y*Y)*(X+a*c)+(4*a+3)*h') :
    R=R' ∧ g=g' ∧ h=h' := by
  have hR : R=R' := (y_strictMono a).injective (hy.trans hy'.symm)
  have hg : g=g' := by rw [←hx,←hx',hR]
  have hH : 0<4*a+3 := by simp
  have hm : (4*a+3)*h=(4*a+3)*h' := by
    apply add_left_cancel (a := (Y*Y)*(X+a*c))
    rw [←hcar,←hcar',hg]
  have hh : h=h' := mul_left_cancel₀ (ne_of_gt hH) hm
  exact ⟨hR,hg,hh⟩

#print axioms same_rank_root_carrier
end FreeMainScaleRigidity

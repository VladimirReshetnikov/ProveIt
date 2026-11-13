import Direct80ProjectionPell
import DiophantineConsistency.ArithmeticPow

/-! A variable-base paired Pell comparison in every IΣ₁ model. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace TenPositivePellVariableGrowth
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery ArithmeticPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem paired_step (X a b r : V)
    (hsep : X*(2*(b+2))<(2*a+3)*(2*a+3))
    (ih : power X r*ycoord (r+1) b≤ycoord (2*r+1) a) :
    power X (r+1)*ycoord (r+1+1) b<ycoord (2*(r+1)+1) a := by
  have hpos : 0<ycoord (2*r+1) a :=
    lt_of_lt_of_le (by simp : (0:V)<2*r+1) (time_le_y _ _)
  have htwo : (2*a+3)*(2*a+3)*ycoord (2*r+1) a<ycoord (2*(r+1)+1) a := calc
    (2*a+3)*(2*a+3)*ycoord (2*r+1) a=
        (2*a+3)*((2*a+3)*ycoord (2*r+1) a) := by ring
    _<(2*a+3)*ycoord (2*r+1+1) a := mul_lt_mul_of_pos_left (y_lower a (2*r+1)) (by simp)
    _<ycoord (2*r+1+1+1) a := y_lower a (2*r+1+1)
    _=ycoord (2*(r+1)+1) a := by congr 1; ring
  calc
    power X (r+1)*ycoord (r+1+1) b=(X*power X r)*ycoord (r+1+1) b := by rw [power_succ]
    _≤(X*power X r)*(2*(b+2)*ycoord (r+1) b) :=
      mul_le_mul_of_nonneg_left (y_upper b (r+1) (by simp)) (by simp)
    _=(X*(2*(b+2)))*(power X r*ycoord (r+1) b) := by ring
    _≤(X*(2*(b+2)))*ycoord (2*r+1) a := mul_le_mul_of_nonneg_left ih (by simp)
    _<(2*a+3)*(2*a+3)*ycoord (2*r+1) a := mul_lt_mul_of_pos_right hsep hpos
    _<ycoord (2*(r+1)+1) a := htwo

private def comparisonDef : 𝚺₁.Semisentence 4 := .mkSigma
  “r X a b. ∃ e u v, !ArithmeticPow.powerDef e X r ∧ !yDef u (r+1) b ∧
    !yDef v (2*r+1) a ∧ e*u≤v”

private instance comparison_defined : 𝚺₁-Relation₄[V]
    (fun r X a b : V => power X r*ycoord (r+1) b≤ycoord (2*r+1) a)
    via comparisonDef := .mk fun e => by
  simp [comparisonDef,Semiformula.eval_substs]

private instance comparison_definable : 𝚺₁-Relation₄[V]
    (fun r X a b : V => power X r*ycoord (r+1) b≤ycoord (2*r+1) a) :=
  comparison_defined.to_definable

theorem paired_comparison (X a b : V)
    (hsep : X*(2*(b+2))<(2*a+3)*(2*a+3)) (r : V) :
    power X r*ycoord (r+1) b≤ycoord (2*r+1) a := by
  induction r using ISigma1.sigma1_succ_induction
  · exact HierarchySymbol.Definable.comp₄
      (P := fun r X a b : V => power X r*ycoord (r+1) b≤ycoord (2*r+1) a)
      (f₁ := fun v => v 0) (f₂ := fun _ => X) (f₃ := fun _ => a) (f₄ := fun _ => b)
      (by simp) (by simp) (by simp) (by simp)
  case zero =>
    have hy (b : V) : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    simp [hy]
  case succ r ih => exact le_of_lt (paired_step X a b r hsep ih)

theorem paired_comparison_strict (X a b : V)
    (hsep : X*(2*(b+2))<(2*a+3)*(2*a+3)) (r : V) (hr : 0<r) :
    power X r*ycoord (r+1) b<ycoord (2*r+1) a := by
  rcases zero_or_succ r with rfl|⟨r,rfl⟩
  · simp at hr
  · exact paired_step X a b r hsep (paired_comparison X a b hsep r)

#print axioms TenPositivePellVariableGrowth.paired_comparison
#print axioms TenPositivePellVariableGrowth.paired_comparison_strict
end TenPositivePellVariableGrowth

import DiophantineConsistency.ArithmeticPellRecurrence

/-! A small Pell-index configuration that does not satisfy the m≥6 bound. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85SmallIndexExample
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The first/main Pell-index equations and Y=q³*s alone allow m=3.
This does not assert any of the actual four factor-unit equations. -/
theorem small_main_index :
    let q : V := 2
    let Y : V := 8
    let X : V := 14
    let eta : V := 2159
    let zeta : V := 5013
    let k : V := eta+zeta
    let Q : V := X*Y*Y
    let B : V := 2*(Q-1)+1
    let a : V := X*Y+Y
    Y=q^3*1 ∧ 0<eta ∧ 0<zeta ∧ 2*ycoord 2 B=k ∧
      ycoord 3 a=eta+Y*k ∧ (2:V)<3 ∧ 3<6 := by
  have hx1 (b : V) : xcoord 1 b=b+2 := by simpa using x_succ (V:=V) 0 b
  have hy1 (b : V) : ycoord 1 b=1 := by simpa using y_succ (V:=V) 0 b
  have hx2 (b : V) : xcoord 2 b=(b+2)*(b+2)+delta b := by
    have h := x_succ (V:=V) 1 b
    simpa only [one_add_one_eq_two,hx1,hy1,mul_one] using h
  have hy2 (b : V) : ycoord 2 b=2*(b+2) := by
    have h := y_succ (V:=V) 1 b
    simpa only [one_add_one_eq_two,hx1,hy1,mul_one,two_mul] using h
  have hy3 (b : V) : ycoord 3 b=(b+2)*(b+2)+delta b+(b+2)*(2*(b+2)) := by
    have h := y_succ (V:=V) 2 b
    simpa only [show (2:V)+1=3 by norm_num,hx2,hy2] using h
  dsimp only
  rw [hy2,hy3]
  have hsub : (896:V)-1=895 := by
    rw [show (896:V)=895+1 by norm_num]
    simp
  norm_num [delta,hsub]
end DiophantineConsistency.AdaptiveGap85SmallIndexExample

import DiophantineConsistency.ArithmeticAdaptiveIndexComparison2011
import DiophantineConsistency.ArithmeticPellCommonUnit

/-! Unchecked draft: the first index is strictly above half the main index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainHalfIndexLower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence ArithmeticPellCongruences
open ArithmeticAdaptiveIndexComparison2011 ArithmeticPellCommonUnit
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem main_lt_twice_first (X Y eta zeta n m : V)
    (hZeta : 0<zeta)
    (hfirst : 2*ycoord n (2*((X*Y)*Y-1)+1)=eta+zeta)
    (hmain : ycoord m (X*Y+Y)=(eta+zeta)*Y+eta) : m<2*n := by
  let a : V := X*Y+Y
  let P : V := (X*Y)*Y
  let B : V := 2*(P-1)+1
  let A2 : V := 2*a*a+8*a+5
  let k : V := eta+zeta
  have ha0 : 0≤a := Arithmetic.zero_le _
  have hXY : X*Y≤a := by dsimp [a]; simp
  have hYle : Y≤a := by dsimp [a]; simp
  have hP : P≤a*a := by
    dsimp [P]
    exact mul_le_mul hXY hYle (Arithmetic.zero_le _) ha0
  have hBbound : B≤2*P+1 := by
    dsimp [B]
    exact _root_.add_le_add (mul_le_mul_of_nonneg_left tsub_le_self (by norm_num)) (le_refl 1)
  have hAB : B≤A2 := by
    have hh : 2*P+1≤A2 := by dsimp [A2]; nlinarith
    exact le_trans hBbound hh
  have hx1 : xcoord 1 a=a+2 := by simpa using x_succ (0:V) a
  have hy1 : ycoord 1 a=1 := by simpa using y_succ (0:V) a
  have hx2 : A2+2=xcoord 2 a := by
    have hh := x_succ (1:V) a
    rw [hx1,hy1] at hh
    unfold delta at hh
    dsimp [A2]
    nlinarith [hh]
  have hy2 : ycoord 2 a=2*(a+2) := by
    have hh := y_succ (1:V) a
    rw [hx1,hy1] at hh
    nlinarith [hh]
  have hcomp : ycoord n A2*(2*(a+2))=ycoord (2*n) a := by
    have hh := (composition A2 a 2 hx2 n).2
    rwa [hy2] at hh
  have hbase := (base_mono B A2 hAB n).2
  have hcoef : 2*(Y+1)≤2*(a+2) := by dsimp [a]; nlinarith
  have hlarge : (Y+1)*k≤ycoord (2*n) a := by
    change 2*ycoord n B=k at hfirst
    rw [←hcomp,←hfirst]
    have hm1 := mul_le_mul_of_nonneg_left hbase (show 0≤2*(Y+1) by simp)
    have hm2 := mul_le_mul_of_nonneg_right hcoef (Arithmetic.zero_le (ycoord n A2))
    nlinarith [hm1,hm2]
  have hupper : k*Y+eta<(Y+1)*k := by
    dsimp [k]
    nlinarith
  change ycoord m a=k*Y+eta at hmain
  by_contra hn
  have hm : 2*n≤m := le_of_not_gt hn
  have hy := (y_strictMono a).monotone hm
  rw [hmain] at hy
  exact (not_le_of_gt hupper) (le_trans hlarge hy)

#print axioms main_lt_twice_first
end FreeMainHalfIndexLower

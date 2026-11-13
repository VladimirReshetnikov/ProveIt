import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! A main ordinate cannot fit the interval forced by first index one. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Direct80IndexOne
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticPellRecurrence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem impossible (Y S X eta zeta m : V)
    (hY : 1≤Y) (hYS : Y≤S) (heta : 0<eta) (hzeta : 0<zeta)
    (hk : eta+zeta=2)
    (hc : (eta+zeta)*Y+eta=ycoord m (S*(X+1)-1)) : False := by
  let A : V := S*(X+1)
  let base : V := A-1
  have hA : Y≤A := calc
    Y≤S := hYS
    _≤S*(X+1) := le_mul_of_one_le_right (by simp) (by simp)
  have hA1 : A-1+1=A := tsub_add_cancel_of_le (le_trans hY hA)
  have heta2 : eta<2 := by rw [←hk]; exact lt_add_of_pos_right eta hzeta
  have hy1 : ycoord 1 base=1 := by simpa using y_succ (0:V) base
  have hx1 : xcoord 1 base=base+2 := by simpa using x_succ (0:V) base
  have hy2 : ycoord 2 base=2*(A+1) := by
    calc
      ycoord 2 base=xcoord 1 base+(base+2)*ycoord 1 base := by simpa only [show (1:V)+1=2 by ring] using y_succ (1:V) base
      _=2*(base+1)+2 := by rw [hx1,hy1]; ring
      _=2*(A+1) := by dsimp [base]; rw [hA1]; ring
  have hc1 : 1<(eta+zeta)*Y+eta := by
    rw [hk]
    have h2 : (1:V)≤2*Y := le_trans hY (le_mul_of_one_le_left (by simp) (by norm_num : (1:V)≤2))
    exact lt_of_le_of_lt h2 (lt_add_of_pos_right _ heta)
  have hm : 1<m := by
    by_contra hn
    have hle : m≤1 := le_of_not_gt hn
    have hh := (ordinate_strictMono base).monotone hle
    rw [hy1,←hc] at hh
    exact (not_le_of_gt hc1) hh
  have hm2 : 2≤m := by simpa only [show (1:V)+1=2 by ring] using lt_iff_succ_le.mp hm
  have hlow : 2*(A+1)≤(eta+zeta)*Y+eta := by
    have hh := (ordinate_strictMono base).monotone hm2
    rw [hy2,←hc] at hh
    exact hh
  have hupp : (eta+zeta)*Y+eta<2*(A+1) := by
    rw [hk]
    calc
      2*Y+eta<2*Y+2 := by simpa only [add_comm] using add_lt_add_left heta2 (2*Y)
      _=2*(Y+1) := by ring
      _≤2*(A+1) := mul_le_mul_of_nonneg_left (by simpa only [add_comm] using add_le_add_right hA 1) (by simp)
  exact (not_le_of_gt hupp) hlow

#print axioms Direct80IndexOne.impossible
end Direct80IndexOne

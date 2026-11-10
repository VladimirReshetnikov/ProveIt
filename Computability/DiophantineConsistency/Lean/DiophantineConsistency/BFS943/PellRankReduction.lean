import DiophantineConsistency.BFS943.SignedRankIndex

/-! Noncircular reduction of the signed rank congruence to the main index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositivePellRankReduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellStrongDivisibility ArithmeticPellIndexDivisibility
open ArithmeticPellPeriodicity ArithmeticPellResidueClasses ArithmeticPellHalfIndex ArithmeticPellResidueAux
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem rank_to_main_index (n s b c r R : V) (hn : 0<n) (hr3 : 3≤r)
    (hc : c=ycoord r b) (hd : c*c∣ycoord n b)
    (hmain : SignMod (xcoord n b) c (ycoord s b))
    (hrank : SignMod c R s) : SignMod c R r := by
  have hr : 0<r := lt_of_lt_of_le (by simp : (0:V)<3) hr3
  have hcpos : 0<c := by rw [hc]; exact lt_of_lt_of_le hr (time_le_y r b)
  have hcdiv : c∣ycoord n b := dvd_trans (dvd_mul_right c c) hd
  have hrdiv : r∣n := (y_dvd_iff b r n).mp (by rw [←hc]; exact hcdiv)
  have hcdivn : c∣n := by
    have hdsq : ycoord r b*ycoord r b∣delta b*ycoord n b := by
      rw [←hc]
      exact dvd_mul_of_dvd_right hd (delta b)
    have h := ordinate_divides_index b r n hrdiv hdsq
    rwa [←hc] at h
  have hcle : c≤n := Arithmetic.le_of_dvd hn hcdivn
  have htwice : 2*r<c := by rw [hc]; exact twice_index_lt_y b r hr3
  have hbound : 2*r≤n := le_trans (le_of_lt htwice) hcle
  have hF : 0<xcoord n b := lt_of_lt_of_le (by simp : (0:V)<1) (one_le_x n b)
  have hsq : (ycoord s b*ycoord s b)%xcoord n b=(c*c)%xcoord n b :=
    sign_square hF (sign_symm hmain)
  have hdouble : xcoord (2*s) b%xcoord n b=xcoord (2*r) b%xcoord n b := by
    rw [double_x,double_x,←hc]
    have hprod := same_mul hF (x:=2*delta b) rfl hsq
    rw [show 2*delta b*ycoord s b*ycoord s b=(2*delta b)*(ycoord s b*ycoord s b) by ring,
      show 2*delta b*c*c=(2*delta b)*(c*c) by ring]
    calc
      (1+(2*delta b)*(ycoord s b*ycoord s b))%xcoord n b =
          (1%xcoord n b+((2*delta b)*(ycoord s b*ycoord s b))%xcoord n b)%xcoord n b := mod_add hF
      _=(1%xcoord n b+((2*delta b)*(c*c))%xcoord n b)%xcoord n b := by rw [hprod]
      _=(1+(2*delta b)*(c*c))%xcoord n b := (mod_add hF).symm
  have hstep : SignMod n s r := doubled_step_down b n r s hr hbound (Or.inl hdouble)
  exact sign_trans hcpos hrank (sign_reduce hcpos hcdivn hstep)

#print axioms TenPositivePellRankReduction.rank_to_main_index
end TenPositivePellRankReduction

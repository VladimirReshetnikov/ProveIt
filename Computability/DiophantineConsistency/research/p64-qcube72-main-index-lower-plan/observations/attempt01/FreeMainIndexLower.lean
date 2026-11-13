import DiophantineConsistency.Compact44.P64Early
import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticStandardCasts

/-! Unchecked draft: the free carrier forces the main index beyond five. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainIndexLower
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
open ArithmeticAdaptiveFirstDivisibility2011 P72Mu
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem six_le_index (q X Y U a H g c h m : V)
    (hq : 33≤q) (hX : q≤X) (hY : 3≤Y)
    (hU : U=Y*Y) (ha : a=X*Y+Y) (hH : H=4*a+3)
    (hmx : xcoord m a=g) (hmy : ycoord m a=c)
    (hcar : U*g=U*(X+a*c)+H*h) : 6≤m := by
  by_contra hn
  have hm5 : m≤5 := by
    apply lt_succ_iff_le.mp
    simpa only [show (5:V)+1=6 by norm_num] using (lt_of_not_ge hn)
  have hX0 : 0≤X := Arithmetic.zero_le X
  have hH0 : 0<H := by rw [hH]; simp
  obtain ⟨z,hz⟩ := projection_quotient a m
  have hproj : g=Exp.exp m+a*c+H*z := by rw [←hmx,hz,hmy,hH]
  have heq : (U*Exp.exp m+U*(a*c))+H*(U*z) =
      (U*X+U*(a*c))+H*h := by
    calc
      _ = U*g := by rw [hproj]; ring
      _ = _ := by rw [hcar]; ring
  have hres := congrArg (fun t : V => t % H) heq
  rw [mod_add_mul' _ _ hH0,mod_add_mul' _ _ hH0] at hres
  have hmod : (U*Exp.exp m)%H = (U*X)%H := mod_cancel hH0 hres
  obtain ⟨e,mu,_,hHmu,heU,_,hmodmu⟩ := gcd_cancel H U (Exp.exp m) X hH0 hmod
  have heY : e ∣ Y*Y := by rw [←hU]; exact heU
  have hHeq : H=3+4*(X*Y+Y) := by rw [hH,ha]; ring
  have heH : e ∣ 3+4*(X*Y+Y) := by rw [←hHeq]; exact ⟨mu,hHmu⟩
  have he9 : e ∣ (9:V) := P64Early.gcd_dvd_nine X Y e heY heH
  have hele : e≤9 := Arithmetic.le_of_dvd (by norm_num) he9
  have hHle : H≤9*mu := by rw [hHmu]; exact mul_le_mul_of_nonneg_right hele (Arithmetic.zero_le mu)
  have hXY : 3*X≤X*Y := by
    have hh := mul_le_mul_of_nonneg_left hY hX0
    nlinarith
  have hHX : 9*X<H := by rw [hH,ha]; nlinarith [hXY,Arithmetic.zero_le Y]
  have hXmu : X<mu := lt_of_mul_lt_mul_left (lt_of_lt_of_le hHX hHle) (by norm_num : (0:V)≤9)
  have hExp : Exp.exp m≤(32:V) := by
    have hh := exp_monotone_le.mpr hm5
    have h5 : Exp.exp (5:V)=(32:V) := by
      simpa using (ArithmeticStandardCasts.cast_exp (V:=V) 5)
    rwa [h5] at hh
  have hExpX : Exp.exp m<X := lt_of_le_of_lt hExp (lt_of_lt_of_le (by norm_num : (32:V)<33) (le_trans hq hX))
  have hExpmu : Exp.exp m<mu := lt_trans hExpX hXmu
  rw [mod_eq_self_of_lt hExpmu,mod_eq_self_of_lt hXmu] at hmodmu
  exact (ne_of_lt hExpX) hmodmu

#print axioms FreeMainIndexLower.six_le_index
end FreeMainIndexLower

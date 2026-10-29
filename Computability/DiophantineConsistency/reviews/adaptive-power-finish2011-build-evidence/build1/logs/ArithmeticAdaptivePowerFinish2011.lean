import DiophantineConsistency.ArithmeticAdaptivePowerGrowth2011

/-! Exact adaptive X = 2^R from the actual current zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptivePowerFinish2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveScaledNorms2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveMainOrientation2011
open ArithmeticAdaptiveExactIndices2011 ArithmeticAdaptivePowerGrowth2011
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort xcoord ycoord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem mod_cancel {a b c m : V} (hm : 0<m) (h : (a+c)%m=(b+c)%m) : a%m=b%m := by
  have hr := le_of_lt (mod_lt c hm)
  have hc : c+(m-c%m)=m*(c/m+1) := by
    calc
      c+(m-c%m)=(m*(c/m)+c%m)+(m-c%m) := by rw [div_add_mod]
      _=m*(c/m)+(c%m+(m-c%m)) := by ring
      _=m*(c/m)+m := by rw [add_tsub_cancel_of_le hr]
      _=m*(c/m+1) := by ring
  have hh : ((a+c)+(m-c%m))%m=((b+c)+(m-c%m))%m := by
    rw [mod_add (a:=a+c) hm,mod_add (a:=b+c) hm,h]
  simpa only [add_assoc,hc,mod_add_mul' _ _ hm] using hh

def PowerFinish (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  v 6=Exp.exp R

theorem finish_of_facts (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hq : 1<1+v 0*(p 0:V)) (hv : ∀j,0<v j)
    (hgap : v 1+v 2<1+v 0*(p 0:V))
    (hY : ∃ s:V, v 7=(1+v 0*(p 0:V))^3*s)
    (he : ExactIndices p v) (hg : PowerGrowth p v) : PowerFinish p v := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := v 6
  let Y : V := v 7
  let U : V := Y*(q*q)
  let E : V := X*Y
  let Q : V := E*Y
  let k : V := v 9+v 10
  let c : V := v 9+Y*k
  let a : V := E+Y
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq0 : 0<q := lt_trans (by simp : (0:V)<1) hq
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs⟩ := hY
  obtain ⟨first,main,n,m,t,_,_,_,_,hmR,_,hk,_,horient,_,_,hmx,hmy⟩ := he
  change m=R at hmR
  change k=R+1+4*Q*t at hk
  let W : V := 4*X*q*s*t
  have hscale : 4*Q*t=U*W := by dsimp [Q,E,U,W,Y]; rw [hs]; ring
  have hrep := main_root_rep p v (le_of_lt hq) hF
  have hroot := equivalent_trans (equivalent_symm hrep) horient
  change (U*(X+a*c)+H*(U*v 12+E*q+R'+1))+0=H*k+U*main at hroot
  simp only [add_zero] at hroot
  rw [←hRank,hk,hscale] at hroot
  have hcancel : U*(main+H*W)=U*(X+a*c+H*v 12)+H*(E*q) := by
    apply add_right_cancel (b:=H*(R+1))
    calc
      U*(main+H*W)+H*(R+1)=H*(R+1+U*W)+U*main := by ring
      _=U*(X+a*c)+H*(U*v 12+E*q+R+1) := hroot.symm
      _=(U*(X+a*c+H*v 12)+H*(E*q))+H*(R+1) := by ring
  have hqY : 0<q*Y := mul_pos hq0 (hv 7)
  have hqeq : q*(main+H*W)=q*(X+a*c+H*v 12)+H*X := by
    apply mul_left_cancel₀ (ne_of_gt hqY)
    calc
      (q*Y)*(q*(main+H*W))=U*(main+H*W) := by dsimp [U]; ring
      _=U*(X+a*c+H*v 12)+H*(E*q) := hcancel
      _=(q*Y)*(q*(X+a*c+H*v 12)+H*X) := by dsimp [U,E]; ring
  let d : V := 4*(q*q)*s*(X+1)
  have hH : H=3+q*d := by dsimp [H,a,E,d,Y]; rw [hs]; ring
  have hm : (q*d)*(main+H*W)=(q*d)*(X+a*c+H*v 12)+H*d*X := calc
    _=d*(q*(main+H*W)) := by ring
    _=d*(q*(X+a*c+H*v 12)+H*X) := by rw [hqeq]
    _=_ := by ring
  have hbal : H*(main+H*W)+3*(X+a*c+H*v 12) =
      3*(main+H*W)+H*(X+a*c+H*v 12)+H*d*X := calc
    _=3*(main+H*W)+(q*d)*(main+H*W)+3*(X+a*c+H*v 12) := by rw [hH]; ring
    _=3*(main+H*W)+((q*d)*(X+a*c+H*v 12)+H*d*X)+3*(X+a*c+H*v 12) := by rw [hm]
    _=_ := by rw [hH]; ring
  have hbal' : 3*(X+a*c)+H*(main+H*W+3*v 12) =
      3*main+H*(3*W+X+a*c+H*v 12+d*X) := by
    calc
      _=H*(main+H*W)+3*(X+a*c+H*v 12) := by ring
      _=3*(main+H*W)+H*(X+a*c+H*v 12)+H*d*X := hbal
      _=_ := by ring
  have hHp : 0<H := by dsimp [H]; simp
  have hmod : (3*(X+a*c))%H=(3*main)%H := by
    have h := congrArg (fun z : V => z%H) hbal'
    rw [mod_add_mul' _ _ hHp,mod_add_mul' _ _ hHp] at h
    exact h
  change xcoord m a=main at hmx
  change ycoord m a=c at hmy
  have hxR : xcoord R a=main := by rw [←hmR]; exact hmx
  have hyR : ycoord R a=c := by rw [←hmR]; exact hmy
  obtain ⟨w,hw⟩ := projection_quotient a R
  have hproj : main=Exp.exp R+a*c+(4*a+3)*w := by rw [←hxR,←hyR]; exact hw
  have hHform : H=4*a+3 := by dsimp [H]; ring
  have hproj' : main=Exp.exp R+a*c+H*w := by rw [hHform]; exact hproj
  have hres : (3*X+3*a*c)%H=(3*Exp.exp R+3*a*c)%H := calc
    _=(3*(X+a*c))%H := by congr 1; ring
    _=(3*main)%H := hmod
    _=(3*Exp.exp R+3*a*c+H*(3*w))%H := by rw [hproj']; congr 1; ring
    _=(3*Exp.exp R+3*a*c)%H := mod_add_mul' _ _ hHp
  have h3mod : (3*X)%H=(3*Exp.exp R)%H := mod_cancel hHp hres
  have hY1 : 1≤Y := pos_iff_one_le.mp (hv 7)
  have hXa : X<a := by
    have ha : X+1≤a := calc
      X+1≤Y*(X+1) := le_mul_of_one_le_left (by simp) hY1
      _=a := by dsimp [a,E]; ring
    exact lt_of_lt_of_le (lt_add_one X) ha
  have hYa : Y≤a := calc
    Y≤Y*(X+1) := le_mul_of_one_le_right (by simp) (by simp)
    _=a := by dsimp [a,E]; ring
  have h3a : 3*a<H := calc
    3*a<3*a+(a+3) := lt_add_of_pos_right _ (by simp)
    _=H := by dsimp [H]; ring
  have h3X : 3*X<H := lt_trans (mul_lt_mul_of_pos_left hXa (by simp)) h3a
  change Exp.exp R<Y at hg
  have h3exp : 3*Exp.exp R<H :=
    lt_trans (mul_lt_mul_of_pos_left (lt_of_lt_of_le hg hYa) (by simp)) h3a
  rw [mod_eq_self_of_lt h3X,mod_eq_self_of_lt h3exp] at h3mod
  change X=Exp.exp R
  exact mul_left_cancel₀ (by simp : (3:V)≠0) h3mod

theorem current_power_finish (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : PowerFinish currentPorts v := by
  have hp := current_parameters_positive v hv
  have hgap := tsub_pos_iff_lt.mp (current_transport_positive v hv hz).2
  obtain ⟨s,_,hs⟩ := current_Y_quotient v hv hz
  have hs' : v 7=(1+v 0*(CurrentMasks2011.beta:V))^3*s := by
    simpa only [pow_succ,pow_zero,one_mul,mul_assoc] using hs
  have hy : ∃s:V, v 7=(1+v 0*(currentPorts 0:V))^3*s := by
    refine ⟨s,?_⟩
    simpa only [currentPorts,Matrix.cons_val_zero] using hs'
  apply finish_of_facts currentPorts v
  · simpa only [currentPorts,Matrix.cons_val_zero] using hp.1
  · exact hv
  · simpa only [currentPorts,Matrix.cons_val_zero] using hgap
  · exact hy
  · exact current_exact_indices v hv hz
  · exact current_power_growth v hv hz

theorem current_natural_power_finish (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    PowerFinish currentPorts (fun j => v j+1) :=
  current_power_finish _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptivePowerFinish2011

import DiophantineConsistency.Compact44.FreeJPowerGrowth
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJPowerFinish
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticPellPowerRecovery
open DiophantineConsistency.ArithmeticPellCongruences
open DiophantineConsistency.ArithmeticAdaptiveFirstDivisibility2011
open FreeJRootBinding FreeJFirstTransport FreeJMainOrientation FreeJIndexComparison
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_power (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v)
    (hbeta : (46:V)≤(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    v 5=Exp.exp R := by
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let X : V := v 5
  let Y : V := v 6
  let U : V := Y*(q*q)
  let E : V := X*Y
  let Q : V := E*Y
  let k : V := v 8+v 9
  let c : V := v 8+Y*k
  let a : V := E+Y
  let H : V := 3+4*a
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hq0 : 0<q := by dsimp [q,b]; simp
  have hq : 1<q := by dsimp [q,b]; exact lt_add_of_pos_right 1 (mul_pos (hv 0) hb)
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp (freej_first_factor_transport p v hb hv hz).2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs⟩ := first_factor_forces_Y_divisible p v hz (hv 0) hb
  change Y=q^3*s at hs
  obtain ⟨t,hk⟩ := FreeJExactTransport.first_quotient p v hb hl hh hv hz
  obtain ⟨first,main,n,m,_,_,_,_,_,_,_,horient,_,_,hmx,hmy,_⟩ :=
    comparison p v hb hl hh hv hz
  obtain ⟨_,_,_,pi,_,_,_,_,hpiR,_,_,_,_,hpiy⟩ :=
    FreeJExactOrdinary.exact_ordinary_indices p v hb hl hh hv hz
  change pi=R at hpiR
  change ycoord pi a=c at hpiy
  change ycoord m a=c at hmy
  have hcR : ycoord R a=c := by rw [←hpiR]; exact hpiy
  have hmR : m=R := (y_strictMono a).injective (hmy.trans hcR.symm)
  change k=R+1+4*Q*t at hk
  let W : V := 4*X*q*s*t
  have hscale : 4*Q*t=U*W := by dsimp [Q,E,U,W]; rw [hs]; ring
  have hrep := freej_main_root_rep p v (le_of_lt hq) hF
  have hroot := equivalent_trans (equivalent_symm hrep) horient
  change (U*(X+a*c)+H*(U*v 11+E*q+R'+1))+0=H*k+U*main at hroot
  simp only [add_zero] at hroot
  rw [←hRank,hk,hscale] at hroot
  have hcancel : U*(main+H*W)=U*(X+a*c+H*v 11)+H*(E*q) := by
    apply add_right_cancel (b:=H*(R+1))
    calc
      U*(main+H*W)+H*(R+1)=H*(R+1+U*W)+U*main := by ring
      _=U*(X+a*c)+H*(U*v 11+E*q+R+1) := hroot.symm
      _=(U*(X+a*c+H*v 11)+H*(E*q))+H*(R+1) := by ring
  have hqY : 0<q*Y := mul_pos hq0 (hv 6)
  have hqeq : q*(main+H*W)=q*(X+a*c+H*v 11)+H*X := by
    apply mul_left_cancel₀ (ne_of_gt hqY)
    calc
      (q*Y)*(q*(main+H*W))=U*(main+H*W) := by dsimp [U]; ring
      _=U*(X+a*c+H*v 11)+H*(E*q) := hcancel
      _=(q*Y)*(q*(X+a*c+H*v 11)+H*X) := by dsimp [U,E]; ring
  let d : V := 4*(q*q)*s*(X+1)
  have hH : H=3+q*d := by dsimp [H,a,E,d]; rw [hs]; ring
  have hm : (q*d)*(main+H*W)=(q*d)*(X+a*c+H*v 11)+H*d*X := calc
    _=d*(q*(main+H*W)) := by ring
    _=d*(q*(X+a*c+H*v 11)+H*X) := by rw [hqeq]
    _=_ := by ring
  have hbal : H*(main+H*W)+3*(X+a*c+H*v 11) =
      3*(main+H*W)+H*(X+a*c+H*v 11)+H*d*X := calc
    _=3*(main+H*W)+(q*d)*(main+H*W)+3*(X+a*c+H*v 11) := by rw [hH]; ring
    _=3*(main+H*W)+((q*d)*(X+a*c+H*v 11)+H*d*X)+3*(X+a*c+H*v 11) := by rw [hm]
    _=_ := by rw [hH]; ring
  have hbal' : 3*(X+a*c)+H*(main+H*W+3*v 11) =
      3*main+H*(3*W+X+a*c+H*v 11+d*X) := by
    calc
      _=H*(main+H*W)+3*(X+a*c+H*v 11) := by ring
      _=3*(main+H*W)+H*(X+a*c+H*v 11)+H*d*X := hbal
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
  have hY1 : 1≤Y := pos_iff_one_le.mp (hv 6)
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
  have hg : Exp.exp R<Y := FreeJPowerGrowth.growth p v hb hl hh hv hz hbeta
  have h3exp : 3*Exp.exp R<H :=
    lt_trans (mul_lt_mul_of_pos_left (lt_of_lt_of_le hg hYa) (by simp)) h3a
  rw [mod_eq_self_of_lt h3X,mod_eq_self_of_lt h3exp] at h3mod
  change X=Exp.exp R
  exact mul_left_cancel₀ (by simp : (3:V)≠0) h3mod

end FreeJPowerFinish
#print axioms FreeJPowerFinish.graph_power

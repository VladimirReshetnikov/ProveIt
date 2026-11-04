import DiophantineConsistency.Compact44.FreeJExactTransport
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJPowerProjection
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.Ordinary12FreeJ
open FreeJRootBinding FreeJFirstTransport FreeJMainOrientation
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_projection (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    q ∣ 3*v 5 ∧ q≤3*v 5 := by
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
  have hq : 0<q := by dsimp [q,b]; simp
  have hq1 : 1≤q := by dsimp [q,b]; simp
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp (freej_first_factor_transport p v hb hv hz).2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R=R' := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  obtain ⟨s,hs⟩ := first_factor_forces_Y_divisible p v hz (hv 0) hb
  change Y=q^3*s at hs
  obtain ⟨t,hk⟩ := FreeJExactTransport.first_quotient p v hb hl hh hv hz
  change k=R+1+4*Q*t at hk
  obtain ⟨main,_,horient,_⟩ := main_oriented p v hb hv hz
  let W : V := 4*X*q*s*t
  have hscale : 4*Q*t=U*W := by dsimp [Q,E,U,W]; rw [hs]; ring
  have hrep := freej_main_root_rep p v hq1 hF
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
  have hqY : 0<q*Y := mul_pos hq (hv 6)
  have hqeq : q*(main+H*W)=q*(X+a*c+H*v 11)+H*X := by
    apply mul_left_cancel₀ (ne_of_gt hqY)
    calc
      (q*Y)*(q*(main+H*W))=U*(main+H*W) := by dsimp [U]; ring
      _=U*(X+a*c+H*v 11)+H*(E*q) := hcancel
      _=(q*Y)*(q*(X+a*c+H*v 11)+H*X) := by dsimp [U,E]; ring
  let d : V := 4*(q*q)*s*(X+1)
  have hH : H=3+q*d := by dsimp [H,a,E,d]; rw [hs]; ring
  have hqeq' : q*(main+H*W)=3*X+q*(X+a*c+H*v 11+d*X) := calc
    _=q*(X+a*c+H*v 11)+H*X := hqeq
    _=3*X+q*(X+a*c+H*v 11+d*X) := by rw [hH]; ring
  have hdiv : q∣3*X := by
    apply mod_eq_zero_iff_dvd.mp
    have hm := congrArg (fun z : V => z%q) hqeq'
    rw [show q*(main+H*W)=0+q*(main+H*W) by ring,
      mod_add_mul' _ _ hq,mod_add_mul' _ _ hq,zero_mod] at hm
    exact hm.symm
  exact ⟨hdiv,Arithmetic.le_of_dvd (mul_pos (by simp) (hv 5)) hdiv⟩
end FreeJPowerProjection
#print axioms FreeJPowerProjection.graph_projection

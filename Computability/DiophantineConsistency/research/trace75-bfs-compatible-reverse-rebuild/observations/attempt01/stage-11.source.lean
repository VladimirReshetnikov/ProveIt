import Trace75UnscaledReverseData
import Trace75NaturalPartsBinding

/-! Conditional unscaled source-to-trace75 positive graph construction. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75UnscaledReverseGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 ArithmeticPellRecurrence
open Trace75Factors Trace75Rank Trace75OldTraceMap Trace75NaturalPartsBinding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def valuation (v : Fin 10 → V) (i T n eta zeta : V) : Fin 10 → V :=
  ![v 0,v 1,v 2,i,T,v 5,v 6,n,eta,zeta]

theorem graph_zero_of_source (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (r eta zeta t : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hr : 0<r)
    (hmask : v 1+v 2<q p v)
    (htransport : ((p 1:V)+v 5)*(q p v-v 1-v 2)=v 1+b p v*t)
    (hR : rankNat p v=2*r+1) (hphase : (2*r+1)%4=3)
    (hXeq : X p v=Exp.exp (2*r+1)) (h72 : 72*r<X p v+1)
    (heta : 0<eta) (hzeta : 0<zeta)
    (hck : ycoord (2*r+1) (Y p v*(X p v+1))=
      2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)*Y p v+eta)
    (hk : 2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)=eta+zeta) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧ value75 (ports p) (fun j => ι (w j))=0 := by
  have hbpos : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hbpos (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  let P:=X p v*Y p v*Y p v
  let a:=Y p v*(X p v+1)-1
  let R:=2*r+1
  let K:=2*ycoord (r+1) (2*(P-1)+1)
  let C:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  let H:=4*a+3
  let Kpos:=X p v*(3*C-2*X p v)+2
  obtain ⟨eta',zeta',i,T,n,tau,f0,u,y,I,rho,heta',hzeta',hi,hT,hn,htau,hf0,hu,hy,
    hC,hK,hoff,hsize,hE,hfn,hQ,hV,hZ,haux⟩ :=
    Trace75UnscaledReverseData.reverse_data (X p v) (Y p v) r eta zeta (b p v) t
      (pos_iff_one_le.mp hX) (pos_iff_one_le.mp hY) hr hXeq h72 hphase heta hzeta hck hk
  change C=K*Y p v+eta' at hC
  change K=eta'+zeta' at hK
  change K=R+1+(X p v*Y p v)*rho at hoff
  change X p v<C at hsize
  let W:=valuation v i T n eta' zeta'
  have hWpos : ∀j,0<W j := by
    intro j
    fin_cases j <;> simp [W,valuation,hv,hi,hT,hn,heta',hzeta']
  have hbW : b p W=b p v := by simp [W,valuation,b]
  have hqW : q p W=q p v := by simp [q,hbW]
  have hYW : Y p W=Y p v := by
    change (q p W*q p W*q p W)*W 6=(q p v*q p v*q p v)*v 6
    rw [hqW]
    simp [W,valuation]
  have hXW : X p W=X p v := by
    change W 5*q p W=v 5*q p v
    rw [hqW]
    simp [W,valuation]
  have hkW : k W=K := by
    change W 8+W 9=K
    simpa [W,valuation] using hK.symm
  have hcW : c p W=C := by
    change k W*Y p W+W 8=C
    rw [hkW,hYW]
    simpa [W,valuation] using hC.symm
  have hUW : U p W=i*C*C := by dsimp [U]; rw [hcW]; simp [W,valuation,mul_assoc]
  have hAW : A p W=Y p v*(X p v+1) := by
    simp only [A,hXW,hYW]
    ring
  have hApos : 0<A p W := by rw [hAW]; exact mul_pos hY (add_pos hX (by simp))
  have ha1 : a+1=A p W := by
    rw [hAW]
    exact tsub_add_cancel_of_le (pos_iff_one_le.mp (by simpa only [hAW] using hApos))
  have hDW : delta p W=D := by
    change A p W*(A p W+2)=ArithmeticPellRecurrence.delta a
    unfold ArithmeticPellRecurrence.delta
    have h3 : a+3=(a+1)+2 := by ring
    rw [h3,ha1]
  have hEW : E p W=tau*tau := by
    dsimp [E]
    rw [hYW,hXW,hkW]
    calc
      (X p v*Y p v*(K*Y p v))*(X p v*Y p v*(K*Y p v)+K)+1 =
        1+(P*K)*(P*K+K) := by dsimp [P]; ring
      _=tau*tau := hE
  have hmaskW : W 1+W 2<q p W := by
    change v 1+v 2<q p W
    rw [hqW]
    exact hmask
  have hRankW : rankNat p W=R := by
    have hh : rankNat p W=rankNat p v := by
      simp only [rankNat,hbW,hqW]
      simp [W,valuation]
    rw [hh,hR]
  let z : Fin 10 → DiffRing V := fun j => ι (W j)
  let rr := regs (ports p) z
  let A0 := D*(i*C*C)*(i*C*C)*(tau*tau)
  have hcR : rr.c=ι C := by
    dsimp [rr,z]
    simp only [c_def,k_def,Y_def,q_def,h_def,ports]
    have hh := congrArg (ι : V →+* DiffRing V) hcW
    simp only [c,k,Y,q,b,map_add,map_mul,map_one,map_natCast] at hh
    exact hh
  have hRankR : rr.rank=ι R := by
    dsimp [rr,z]
    rw [rank_eval_of_mask p W (by rw [hqW]; exact hq) hmaskW,hRankW]
  have hdelta : rr.Delta=ι D := by dsimp [rr,z]; rw [delta_eval,hDW]
  have hU : rr.U=ι (i*C*C) := by dsimp [rr,z]; rw [U_eval,hUW]
  have hE' : rr.E=ι tau*ι tau := by dsimp [rr,z]; rw [E_eval,hEW,map_mul]
  have haR : rr.a=ι A0 := by
    dsimp [rr]
    rw [a_def,hdelta,hU,hE']
    dsimp [A0]
    simp only [map_mul]
    ring
  have hVR : oldV (ports p) z=ι u := by
    dsimp [oldV]
    rw [f_def,F0_def,haR,b_def,hcR,hRankR]
    have hW4 : W 4=T := by simp [W,valuation]
    dsimp [z]
    rw [hW4]
    have hVS : ((ι (1+4*A0*(1+A0)):DiffRing V)*(ι C*ι T-ι R)-ι C)=ι u := by
      simpa only [A0,mul_assoc] using hV
    simp only [map_add,map_mul,map_one,map_ofNat] at hVS
    convert hVS using 1; ring
  have hhR : rr.h=ι (b p v) := by
    dsimp [rr,z]
    simp only [h_def,ports,b,map_mul,map_natCast]
    simp [W,valuation]
  have hDR : rr.D=ι (X p v*Y p v) := by
    dsimp [rr,z]
    simp only [D_def,X_def,Y_def,q_def,h_def,ports,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
    simp [W,valuation]
  have hHR : rr.H=ι H := by
    dsimp [rr]
    rw [H_def,Am1_def]
    have hAcast : (regs (ports p) z).X*(regs (ports p) z).Y+(regs (ports p) z).Y=ι (A p W) := by
      dsimp [z]
      simp only [A,X,Y,q,b,ports,regs,map_add,map_mul,map_one,map_natCast]
    rw [hAcast]
    have he := congrArg (ι : V →+* DiffRing V) ha1
    simp only [map_add,map_one] at he
    dsimp [H]
    simp only [map_add,map_mul,map_ofNat]
    rw [←he]
    ring
  have hsub {x y : V} (hy : y≤x) : (ι (x-y):DiffRing V)=ι x-ι y := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hy]
  have hFle : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hAle : v 2≤q p v-v 1 := by
    apply (le_tsub_iff_right hFle).mpr
    change v 2+v 1≤q p v
    rw [add_comm]
    exact le_of_lt hmask
  have hmaskCast : (ι (q p v-v 1-v 2):DiffRing V)=ι (q p v)-ι (v 1)-ι (v 2) := by
    rw [hsub hAle,hsub hFle]
  have hBR : rr.B=ι (b p v)*ι t := by
    dsimp [rr,z]
    simp only [B_def,C_def,q_def,h_def,ports]
    simp [W,valuation]
    have hqCast : (ι (q p v):DiffRing V)=(p 0:DiffRing V)*ι (v 0)+1 := by
      simp only [q,b,map_add,map_mul,map_one,map_natCast]
    rw [hqCast] at hmaskCast
    rw [←hmaskCast]
    have hh := congrArg (ι : V →+* DiffRing V) htransport
    simp only [map_add,map_mul,map_natCast] at hh
    linear_combination hh
  have heR : rr.e=ι (K-R-1) := by
    dsimp [rr]
    rw [e_def,k_def,hRankR]
    dsimp [z]
    simp [W,valuation]
    have heNat : K-R-1=(X p v*Y p v)*rho := by
      rw [hoff,show R+1+(X p v*Y p v)*rho=((X p v*Y p v)*rho+1)+R by ring]
      simp
    rw [heNat,map_mul]
    have hh := congrArg (ι : V →+* DiffRing V) (hK.symm.trans hoff)
    simp only [map_add,map_mul,map_one] at hh
    dsimp [R] at hh ⊢
    simp only [map_add,map_mul,map_one,map_ofNat] at hh ⊢
    linear_combination hh
  have hgap : 2*X p v≤3*C := by
    have h2 : 2*X p v<2*C := mul_lt_mul_of_pos_left hsize (by simp)
    have h23 : 2*C≤3*C := by
      have hh : 2*C≤2*C+C := by simp
      simpa only [show 2*C+C=3*C by ring] using hh
    exact le_of_lt (lt_of_lt_of_le h2 h23)
  have hKR : rr.K=ι Kpos := by
    have hKcast : (ι Kpos:DiffRing V)=ι (X p v)*(3*ι C-2*ι (X p v))+2 := by
      dsimp [Kpos]
      rw [map_add,map_mul,map_ofNat,hsub hgap]
      simp only [map_mul,map_ofNat]
    dsimp [rr,z]
    rw [K_def,hcR]
    have hXR : (regs (ports p) (fun j => ι (W j))).X=ι (X p v) := by
      simp only [X_def,q_def,h_def,ports,X,q,b,map_add,map_mul,map_one,map_natCast]
      simp [W,valuation]
    rw [hXR,←hKcast]
  have hMR : rr.M=ι (b p v)*ι (X p v*Y p v)*ι H := by
    change rr.h*rr.D*rr.H=ι (b p v)*ι (X p v*Y p v)*ι H
    rw [hhR,hDR,hHR]
  have hZR : oldZ (ports p) z=rr.M*(ι tau*ι f0*ι y) := by
    dsimp [oldZ]
    change rr.h*rr.D*(rr.H*(ι (W 7)-oldV (ports p) z*oldV (ports p) z*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e)=rr.M*(ι tau*ι f0*ι y)
    rw [hVR,hhR,hDR,hHR,hBR,heR,hKR,hMR]
    have hW7 : W 7=n := by simp [W,valuation]
    rw [hW7]
    change ((ι (b p v)*ι (X p v*Y p v))*(ι H*(ι n-ι u*ι u*(ι (b p v)*ι t))+ι Kpos)-
      ι H*(ι (X p v*Y p v)*(ι (b p v)*ι t)+ι (b p v)*ι (K-R-1)) =
      (ι (b p v)*ι (X p v*Y p v)*ι H)*(ι tau*ι f0*ι y)) at hZ
    simpa only [mul_assoc] using hZ
  have hfnW : f0*f0=1+delta p W*U p W*U p W*(tau*tau) := by rw [hDW,hUW]; simpa only [mul_assoc] using hfn
  have hQW : delta p W*(4*(delta p W*U p W*U p W*(tau*tau))*
      (1+delta p W*U p W*U p W*(tau*tau)))=I*I := by rw [hDW,hUW]; simpa only [mul_assoc] using hQ
  exact positive_zero_of_natural_parts p W tau f0 y u I hb hWpos hmaskW hu hEW hfnW hQW hVR hZR haux

#print axioms Trace75UnscaledReverseGraph.graph_zero_of_source
end Trace75UnscaledReverseGraph

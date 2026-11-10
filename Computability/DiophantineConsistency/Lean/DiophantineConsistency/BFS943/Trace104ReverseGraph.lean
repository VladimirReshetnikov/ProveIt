import DiophantineConsistency.BFS943.Trace104ReverseData
import DiophantineConsistency.BFS943.Trace104ParentMap
import DiophantineConsistency.BFS943.Trace104Integral

/-! # Source data to a positive core zero of the 104/174 circuit

`Trace87ReverseGraph.graph_zero_of_source` for the constant-dilation chart: from
the canonical source data (mask, natural transport at base `w`, `R = 2r + 1`,
`R ≡ 3 (mod 4)`, `X = q w = 2^R`, `q⁷ ∣ X`, `s = q³ s_Y`) and an unscaled
strip at `(X, s)`, `Trace104ReverseData` builds the data at the constant scale
`μ = 210`, and the parent map `Trace104ParentMap` gives a positive zero of
`valueC` at `(J, F, α, i, T, w, s, n, η', ζ')`, together with the positive
projection quotient `κ` (`K = H κ`), the eleventh coordinate of the literal.
The carrier offset is `ec = q⁷ ρ` with the signed quotient `ρ` of
`Trace104ReverseData`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace104ReverseGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace104 ArithmeticPellRecurrence
open Trace104Factors Trace104NormRank Trace104ParentMap
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem Am1_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (fun j => ι (v j))).Am1=ι (A p v) := by
  simp only [Am1_def,X_def,q_def,h_def,ports,A,X,Y,q,b,map_add,map_mul,map_one,map_natCast,
    map_ofNat]
  ring

def valuation (v : Fin 10 → V) (i T n eta zeta : V) : Fin 10 → V :=
  ![v 0,v 1,v 2,i,T,v 5,v 6,n,eta,zeta]

theorem graph_zero_of_source (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (r eta zeta t sY : V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) (hr : 2≤r)
    (hmask : v 1+v 2<q p v)
    (htransport : ((p 1:V)+v 5)*(q p v-v 1-v 2)=v 1+b p v*t)
    (hR : rankNat p v=2*r+1) (hphase : (2*r+1)%4=3)
    (hXeq : X p v=Exp.exp (2*r+1)) (h72 : 72*r<X p v+1)
    (heta : 0<eta) (hzeta : 0<zeta)
    (hck : ycoord (2*r+1) (v 6*(X p v+1))=
      2*ycoord (r+1) (2*(X p v*v 6*v 6-1)+1)*v 6+eta)
    (hk : 2*ycoord (r+1) (2*(X p v*v 6*v 6-1)+1)=eta+zeta)
    (hYs : v 6=q p v*q p v*q p v*sY) (hq8 : (8:V)≤q p v) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧ valueC (ports p) (fun j => ι (w j))=0 ∧
      ∃ kappa : V, 0<kappa ∧
        (regs (ports p) (fun j => ι (w j))).K=(regs (ports p) (fun j => ι (w j))).H*ι kappa := by
  have hbpos : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hbpos (by simp)
  have hY : 0<Y p v := mul_pos (by norm_num) (hv 6)
  have hX : 0<X p v := mul_pos hq (hv 5)
  let S:=210*v 6
  let P:=X p v*S*S
  let a:=S*(X p v+1)-1
  let R:=2*r+1
  let K:=2*ycoord (r+1) (2*(P-1)+1)
  let C:=ycoord R a
  let D:=ArithmeticPellRecurrence.delta a
  let H:=4*a+3
  let Kpos:=X p v*(3*C-2*X p v)+2
  -- `R ≥ q² - 1 ≥ 7 q`, so `q⁷ ∣ X`
  have hG : 1≤b p v*(q p v-v 1)+v 2 := pos_iff_one_le.mp
    (add_pos_of_nonneg_of_pos (by simp) (hv 2))
  have hRlower : q p v*q p v-1≤rankNat p v := calc
    q p v*q p v-1≤(b p v*(q p v-v 1)+v 2)*(q p v*q p v-1) :=
      le_mul_of_one_le_left (by simp) hG
    _≤rankNat p v := by dsimp [rankNat]; simp
  have h7 : 7*q p v≤rankNat p v := by
    have h8 : 8*q p v≤q p v*q p v := mul_le_mul_of_nonneg_right hq8 (by simp)
    have hsq1 : 1≤q p v*q p v := one_le_mul (pos_iff_one_le.mp hq) (pos_iff_one_le.mp hq)
    have h7' : 7*q p v≤q p v*q p v-1 := (le_tsub_iff_right hsq1).mpr (by
      calc 7*q p v+1≤7*q p v+q p v := add_le_add (le_refl _) (pos_iff_one_le.mp hq)
        _=8*q p v := by ring
        _≤q p v*q p v := h8)
    exact le_trans h7' hRlower
  have hq7 : q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v)∣X p v :=
    Trace104Integral.q7_dvd (q p v) (X p v) (rankNat p v) (by rw [hR]; exact hXeq) ⟨v 5,rfl⟩ h7
  obtain ⟨eta',zeta',i,T,n,tau,f0,u,y,I,kappa,rho,heta',hzeta',hi,hT,hn,htau,hf0,hu,hy,
    hkappa,hkap,hC,hK,hKR1,hsize,hE,hfn,hQ,hV,hecl,hZ,haux⟩ :=
    Trace104ReverseData.reverse_data (X p v) (v 6) (q p v) r eta zeta (b p v) t sY
      (pos_iff_one_le.mp hX) (pos_iff_one_le.mp (hv 6)) hr hXeq h72
      hphase heta hzeta hck hk hYs hq7
  change C=K*v 6+eta' at hC
  change K=eta'+zeta' at hK
  change R+1≤K at hKR1
  change X p v<C at hsize
  let W:=valuation v i T n eta' zeta'
  have hWpos : ∀j,0<W j := by
    intro j
    fin_cases j <;> simp [W,valuation,hv,hi,hT,hn,heta',hzeta']
  have hbW : b p W=b p v := by simp [W,valuation,b]
  have hqW : q p W=q p v := by simp [q,hbW]
  have hYW : Y p W=S := by
    change 210*W 6=210*v 6
    simp [W,valuation]
  have hXW : X p W=X p v := by
    change q p W*W 5=q p v*v 5
    rw [hqW]
    simp [W,valuation]
  have hkW : k W=K := by
    change W 8+W 9=K
    simpa [W,valuation] using hK.symm
  have hcW : c p W=C := by
    change k W*W 6+W 8=C
    rw [hkW]
    simpa [W,valuation] using hC.symm
  have hUW : U p W=i*C*C := by dsimp [U]; rw [hcW]; simp [W,valuation,mul_assoc]
  have hAW : A p W=S*(X p v+1) := by
    simp only [A,hXW,hYW]
    ring
  have hSpos : 0<S := mul_pos (by norm_num) (hv 6)
  have hApos : 0<A p W := by rw [hAW]; exact mul_pos hSpos (add_pos hX (by simp))
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
      (X p v*S*(K*S))*(X p v*S*(K*S)+K)+1 =
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
  have hA0eq : A0=D*(i*C*C)*(i*C*C)*tau*tau := by dsimp [A0]; ring
  have hcR : rr.c=ι C := by
    dsimp [rr,z]
    rw [Trace104Residue.c_eval p W,hcW]
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
      rw [hA0eq]; exact hV
    simp only [map_add,map_mul,map_one,map_ofNat] at hVS
    convert hVS using 1; ring
  have hhR : rr.h=ι (b p v) := by
    dsimp [rr,z]
    simp only [h_def,ports,b,map_mul,map_natCast]
    simp [W,valuation]
  have hqR : rr.q=ι (q p v) := by
    dsimp [rr,z]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
    simp [W,valuation]
  have hDR : rr.D=ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v)) := by
    change rr.D=_
    rw [D_def,hqR]; simp only [map_mul]
  have hHR : rr.H=ι H := by
    dsimp [rr]
    rw [H_def,Am1_eval p W]
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
    have hBdef : rr.B=((ports p) 1+ι (W 5))*rr.C-ι (W 1) := B_def _ _
    have hCdef : rr.C=rr.q-ι (W 1)-ι (W 2) := C_def _ _
    rw [hBdef,hCdef,hqR]
    have h5 : W 5=v 5 := by simp [W,valuation]
    have h1 : W 1=v 1 := by simp [W,valuation]
    have h2 : W 2=v 2 := by simp [W,valuation]
    rw [h5,h1,h2,←hmaskCast]
    have hh := congrArg (ι : V →+* DiffRing V) htransport
    simp only [map_add,map_mul,map_natCast] at hh
    simp only [ports]
    linear_combination hh
  have heR : rr.e=ι (K-R-1) := by
    dsimp [rr]
    rw [e_def,k_def,hRankR]
    dsimp [z]
    have h89 : (ι (W 8):DiffRing V)+ι (W 9)=ι K := by
      rw [←map_add]; exact congrArg (ι : V →+* DiffRing V) hkW
    rw [h89]
    have hKsub : K-R-1+(R+1)=K := by
      rw [show K-R-1=K-(R+1) by rw [tsub_tsub]]
      exact tsub_add_cancel_of_le hKR1
    have hh := congrArg (ι : V →+* DiffRing V) hKsub
    simp only [map_add,map_one] at hh
    linear_combination -hh
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
  have hMR : rr.M=ι (b p v)*ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*ι H := by
    change rr.h*rr.D*rr.H=_
    rw [hhR,hDR,hHR]
  have hfR : rr.f=ι (1+2*A0) := by
    rw [f_def,F0_def,haR]
    simp only [map_add,map_mul,map_one,map_ofNat]
    ring
  have hbR : rr.b=ι C*ι T-ι R := by
    rw [b_def,hcR,hRankR]
    have hW4 : W 4=T := by simp [W,valuation]
    dsimp [z]
    rw [hW4]
  have hW6 : (ι (W 6):DiffRing V)=ι (v 6) := by simp [W,valuation]
  have hkR : rr.k=ι K := by
    dsimp [rr,z]
    rw [k_def]
    have h89 : (ι (W 8):DiffRing V)+ι (W 9)=ι K := by
      rw [←map_add]; exact congrArg (ι : V →+* DiffRing V) hkW
    exact h89
  have hXR0 : rr.X=ι (X p v) := by
    dsimp [rr,z]
    simp only [X_def,q_def,h_def,ports,X,q,b,map_add,map_mul,map_one,map_natCast]
    simp [W,valuation]
  have heclR : ecl (ports p) z=ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*rho := by
    change (ι (K-R-1):DiffRing V)-InverseLucasThird.corr (ι K) (ι (X p v*v 6*v 6))-
      ι (q p v)^4*ι (v 6)=ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*rho at hecl
    rw [ecl_def]
    change rr.e-InverseLucasThird.corr rr.k (rr.X*ι (W 6)*ι (W 6))-
      rr.q*rr.q*(rr.q*rr.q)*ι (W 6)=_
    rw [heR,hqR,hXR0,hkR,hW6]
    simp only [map_mul] at hecl ⊢
    linear_combination hecl
  have hZR : oldZ (ports p) z=rr.M*(ι tau*ι f0*ι y) := by
    dsimp [oldZ]
    change rr.h*rr.D*(rr.H*(ι (W 7)-(rr.f*rr.b)*oldV (ports p) z*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) z)=rr.M*(ι tau*ι f0*ι y)
    rw [hVR,hfR,hbR,hhR,hDR,hHR,hBR,heclR,hKR,hMR]
    have hW7 : W 7=n := by simp [W,valuation]
    rw [hW7]
    change ((ι (b p v)*ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v)))*(ι H*(ι n-(ι (1+2*(D*(i*C*C)*(i*C*C)*tau*tau))*
      (ι C*ι T-ι R))*ι u*(ι (b p v)*ι t))+ι Kpos)-
      ι H*(ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*(ι (b p v)*ι t)+ι (b p v)*(ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*rho)) =
      (ι (b p v)*ι (q p v*q p v*(q p v*q p v)*(q p v*q p v*q p v))*ι H)*(ι tau*ι f0*ι y)) at hZ
    rw [hA0eq]
    linear_combination hZ
  have hfnW : f0*f0=1+delta p W*U p W*U p W*(tau*tau) := by
    rw [hDW,hUW]
    have h : f0*f0=1+D*(i*C*C)*(i*C*C)*tau*tau := hfn
    rw [h]; ring
  have hQW : delta p W*(4*(delta p W*U p W*U p W*(tau*tau))*
      (1+delta p W*U p W*U p W*(tau*tau)))=I*I := by
    rw [hDW,hUW]
    have h : D*(4*(D*(i*C*C)*(i*C*C)*tau*tau)*(1+D*(i*C*C)*(i*C*C)*tau*tau))=I*I := hQ
    rw [←h]; ring
  obtain ⟨w,hw,hzw,hKw,hHw⟩ :=
    positive_zero_of_natural_parts p W tau f0 y u I hb hWpos hmaskW hu hEW hfnW hQW hVR hZR haux
  refine ⟨w,hw,hzw,kappa,hkappa,?_⟩
  rw [hKw,hHw]
  change rr.K=rr.H*ι kappa
  rw [hKR,hHR,←map_mul]
  exact congrArg (ι : V →+* DiffRing V) hkap

#print axioms Trace104ReverseGraph.graph_zero_of_source
end Trace104ReverseGraph

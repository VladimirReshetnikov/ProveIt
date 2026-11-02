import DiophantineConsistency.FreeJEarlySize
set_option autoImplicit false
set_option Elab.async false
namespace FreeJGraphVBound
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12FreeJ
open FreeJEarlySize
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem simple (c R T t : V) (hT : 0<T) (ht : 0<t) (hR : 2*R<c) :
  2*c < ((1+t)*(1+t))*(T*c-R) := by
  have hT1 : 1 ≤ T := pos_iff_one_le.mp hT
  have ht1 : 1 ≤ t := pos_iff_one_le.mp ht
  have hTc : c ≤ T*c := by
    calc c = 1*c := by simp
      _ ≤ T*c := mul_le_mul_of_nonneg_right hT1 (by simp)
  have hR2 : R ≤ 2*R := by calc
    R ≤ R+R := by simp
    _ = 2*R := by ring
  have hRc : R ≤ T*c := le_trans hR2 (le_trans (le_of_lt hR) hTc)
  have hsub : T*c-R+R=T*c := tsub_add_cancel_of_le hRc
  let u := T*c-R
  have hRu : R<u := by
    have hx : R+R < u+R := calc
      R+R = 2*R := by ring
      _ < c := hR
      _ ≤ T*c := hTc
      _ = u+R := hsub.symm
    exact (add_lt_add_iff_right R).mp hx
  have h2 : (2:V) ≤ 1+t := by
    calc 2 = 1+1 := by ring
      _ ≤ 1+t := by simpa only [add_comm] using add_le_add_left ht1 (1:V)
  have h4 : (4:V) ≤ (1+t)*(1+t) := by
    calc 4 = 2*2 := by ring
      _ ≤ (1+t)*(1+t) := mul_le_mul h2 h2 (by simp) (by simp)
  have hprod : 4*u ≤ ((1+t)*(1+t))*u :=
    mul_le_mul_of_nonneg_right h4 (by simp)
  have h2R : 2*R < 2*u := mul_lt_mul_of_pos_left hRu (by simp)
  calc
    2*c ≤ 2*(u+R) := mul_le_mul_of_nonneg_left (by rw [hsub]; exact hTc) (by simp)
    _ = 2*u+2*R := by ring
    _ < 2*u+2*u := by simpa only [add_comm] using add_lt_add_left h2R (2*u)
    _ = 4*u := by ring
    _ ≤ ((1+t)*(1+t))*u := hprod
def graphR (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let J : Expr (Fin 12) := .var 0
  let F : Expr (Fin 12) := .var 1
  let alpha : Expr (Fin 12) := .var 2
  let q := 1+J*(.constant (p 0))
  let qm := J*(.constant (p 0))
  let G := alpha+(q-F)*qm
  let tail := J*((.constant (p 2))+(.constant (p 3))*q)
  G*(q*q-1)+tail

def graphV (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let t : Expr (Fin 12) := .var 3
  let T : Expr (Fin 12) := .var 4
  let Y : Expr (Fin 12) := .var 6
  let eta : Expr (Fin 12) := .var 8
  let zeta : Expr (Fin 12) := .var 9
  let c := eta+Y*(eta+zeta)
  ((1+t)*(1+t))*(T*c-graphR p)-c

def graphQ : Expr (Fin 12) :=
  let t : Expr (Fin 12) := .var 3
  let X : Expr (Fin 12) := .var 5
  let Y : Expr (Fin 12) := .var 6
  let a := X*Y+Y
  let delta := (3+4*a)+a*a
  delta*((1+t)*(1+t)-1)

theorem shape (p : Fin 4 → ℤ) :
  (core p).pc = graphQ*((graphV p)*(graphV p))-1 := by rfl

theorem ring_bridge (q u F s e a M : V) (hF : u+F=q) (hs : s+1=q*q) :
    (a+q*e)*(q*q)+F*e+M = a+q*e+F*e*(q*q)+((e*u+a)*s+M) := by
  calc
    _ = (a+(u+F)*e)*(s+1)+F*e+M := by rw [hF,hs]
    _ = a+(u+F)*e+F*e*(s+1)+((e*u+a)*s+M) := by ring
    _ = _ := by rw [hF,hs]

theorem R_eval (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hgap : v 1 < 1+v 0*(p 0:V)) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    Equivalent (pairEval (graphR (fun j => (p j:ℤ))) v) (natural R) := by
  let q : V := 1+v 0*(p 0:V)
  have hq1 : q-1+1=q := tsub_add_cancel_of_le (by dsimp [q]; simp)
  have hqf : q-v 1+v 1=q := tsub_add_cancel_of_le (le_of_lt hgap)
  have hq2 : q*q-1+1=q*q := tsub_add_cancel_of_le (by
    have hq : 1≤q := by dsimp [q]; simp
    calc 1 = 1*1 := by ring
      _ ≤ q*q := mul_le_mul hq hq (by simp) (by simp))
  simp [graphR,pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,natural,HSub.hSub,Sub.sub]
  have hqm : (1+v 0*(p 0:V))-1 = v 0*(p 0:V) := by simp
  simp only [HSub.hSub,Sub.sub] at hqm
  rw [hqm]
  have hid := ring_bridge q (q-v 1) (v 1) (q*q-1) (v 0*(p 0:V)) (v 2)
    (((p 2:V)+q*(p 3:V))*v 0) hqf hq2
  dsimp only [q] at hid
  simpa only [pow_two, HSub.hSub, Sub.sub, add_tsub_cancel_left, mul_comm, mul_left_comm, mul_assoc] using hid

theorem V_eval (p : Fin 4 → ℤ) (v : Fin 12 → V) (R : V)
    (hR : Equivalent (pairEval (graphR p) v) (natural R)) :
    let f := 1+v 3
    let c := v 8+v 6*(v 8+v 9)
    Equivalent (pairEval (graphV p) v) (f*f*v 4*c,f*f*R+c) := by
  have h := hR
  simp only [pairEval, Equivalent, natural, add_zero] at h
  simp [graphV,pairEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,
    HSub.hSub,Sub.sub]
  rw [h]
  ring

theorem graph_bound (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j,0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let c : V := v 8+v 6*(v 8+v 9)
    let z := pairEval (graphV (fun j => (p j:ℤ))) v
    1<c ∧ z.2+c<z.1 := by
  let q : V := 1+v 0*(p 0:V)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let c : V := v 8+v 6*(v 8+v 9)
  let z := pairEval (graphV (fun j => (p j:ℤ))) v
  let f : V := 1+v 3
  have hR : 2*R<c := (early_size p v hb hl hh hv hz).2
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp (FreeJFirstTransport.freej_first_factor_transport p v hb hv hz).2
  have hF : v 1<q := lt_of_le_of_lt (by simp) hgap
  have hRe : Equivalent (pairEval (graphR (fun j => (p j:ℤ))) v) (natural R) := R_eval p v hF
  have hVe := V_eval (fun j => (p j:ℤ)) v R hRe
  change z.1+(f*f*R+c)=z.2+f*f*v 4*c at hVe
  have hc1 : 1<c := calc
    1≤v 8 := pos_iff_one_le.mp (hv 8)
    _<v 8+v 6*(v 8+v 9) := lt_add_of_pos_right _ (mul_pos (hv 6) (add_pos (hv 8) (hv 9)))
  have hR2 : R≤2*R := by calc
    R≤R+R := by simp
    _=2*R := by ring
  have hTc : c≤v 4*c := by
    calc c=1*c := by simp
      _≤v 4*c := mul_le_mul_of_nonneg_right (pos_iff_one_le.mp (hv 4)) (by simp)
  have hsub : v 4*c-R+R=v 4*c := tsub_add_cancel_of_le (le_trans hR2 (le_trans (le_of_lt hR) hTc))
  have hs : 2*c<f*f*(v 4*c-R) := simple c R (v 4) (v 3) (hv 4) (hv 3) hR
  have hbase : f*f*R+2*c<f*f*v 4*c := calc
    f*f*R+2*c < f*f*R+f*f*(v 4*c-R) := by simpa only [add_comm] using add_lt_add_left hs (f*f*R)
    _ = f*f*v 4*c := by
      calc
        f*f*R+f*f*(v 4*c-R)=f*f*(v 4*c-R+R) := by ring
        _=f*f*v 4*c := by rw [hsub]; ring
  refine ⟨hc1,?_⟩
  have hh : z.2+c+(f*f*R+c)<z.1+(f*f*R+c) := calc
    z.2+c+(f*f*R+c)=z.2+(f*f*R+2*c) := by ring
    _<z.2+f*f*v 4*c := by simpa only [add_comm] using add_lt_add_left hbase z.2
    _=z.1+(f*f*R+c) := hVe.symm
  exact (add_lt_add_iff_right (f*f*R+c)).mp hh

end FreeJGraphVBound
#print axioms FreeJGraphVBound.simple
#print axioms FreeJGraphVBound.shape

#print axioms FreeJGraphVBound.R_eval
#print axioms FreeJGraphVBound.V_eval
#print axioms FreeJGraphVBound.graph_bound

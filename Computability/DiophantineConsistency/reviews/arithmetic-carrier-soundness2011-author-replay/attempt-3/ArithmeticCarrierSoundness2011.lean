import DiophantineConsistency.ArithmeticNegativeNorms
import DiophantineConsistency.ArithmeticSignedPairs
import DiophantineConsistency.ArithmeticPellFirstIndex
import DiophantineConsistency.CurrentEquationSyntax2011

/-! The actual maintained split-natural zero implies its five additive equations.
Rank and tau are formal differences until the transport factor is extracted.
The concrete ports and the single positive-domain shift are retained. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrierSoundness2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ObjectCurrentEquation2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.highPrefix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private def plus (p q : Pair V) : Pair V := (p.1+q.1,p.2+q.2)
private def minus (p q : Pair V) : Pair V := (p.1+q.2,p.2+q.1)
private def pairEval {σ : Type*} (e : Expr σ) (v : σ → V) : Pair V :=
  (e.splitNatural.1.evalSemiring v,e.splitNatural.2.evalSemiring v)
private def Rep {σ : Type*} (e : Expr σ) (v : σ → V) (p : Pair V) : Prop :=
  Equivalent (pairEval e v) p

private theorem equivalent_plus {p q r s : Pair V} (h : Equivalent p q)
    (k : Equivalent r s) : Equivalent (plus p r) (plus q s) := by
  change p.1+q.2=p.2+q.1 at h
  change r.1+s.2=r.2+s.1 at k
  change (p.1+r.1)+(q.2+s.2)=(p.2+r.2)+(q.1+s.1)
  calc
    _=(p.1+q.2)+(r.1+s.2) := by ring
    _=(p.2+q.1)+(r.2+s.1) := by rw [h,k]
    _=_ := by ring

private theorem equivalent_minus {p q r s : Pair V} (h : Equivalent p q)
    (k : Equivalent r s) : Equivalent (minus p r) (minus q s) := by
  exact equivalent_plus h (show Equivalent (swap r) (swap s) from k.symm)

private theorem square_magnitude (p : Pair V) :
    Equivalent (multiply p p) (natural (magnitude p*magnitude p)) := by
  rcases le_total p.2 p.1 with h|h
  · let u:=p.1-p.2
    have hu : p.1=p.2+u := by rw [add_comm,tsub_add_cancel_of_le h]
    rw [magnitude_of_add hu]
    change p.1*p.1+p.2*p.2+0=(p.1*p.2+p.2*p.1)+u*u
    rw [hu]; ring
  · let u:=p.2-p.1
    have hu : p.2=p.1+u := by rw [add_comm,tsub_add_cancel_of_le h]
    have hm := magnitude_of_add hu
    change magnitude (swap p)=u at hm
    rw [magnitude_swap] at hm
    rw [hm]
    change p.1*p.1+p.2*p.2+0=(p.1*p.2+p.2*p.1)+u*u
    rw [hu]; ring

#check Nat.zero_le -- checkpoint pair algebra
private theorem rep_nat {σ : Type*} (v : σ → V) (n : ℕ) :
    Rep (Expr.constant (n:ℤ)) v (natural (n:V)) := by
  simp [Rep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural,Equivalent]
private theorem rep_var {σ : Type*} (v : σ → V) (j : σ) :
    Rep (Expr.var j) v (natural (v j)) := equivalent_refl _
private theorem rep_add {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (e+f) v (plus p q) :=
  equivalent_plus h k
private theorem rep_sub {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (e-f) v (minus p q) :=
  equivalent_minus h k
private theorem rep_mul {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (e*f) v (multiply p q) :=
  equivalent_multiply h k
private theorem rep_add_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) :
    Rep (e+f) v (natural (a+b)) := by
  simpa only [plus,natural,add_zero] using rep_add h k
private theorem rep_mul_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) :
    Rep (e*f) v (natural (a*b)) := by
  simpa only [multiply,natural,mul_zero,zero_mul,add_zero] using rep_mul h k
private theorem rep_pow_nat {σ : Type*} {e : Expr σ} {v : σ → V} {a : V}
    (h : Rep e v (natural a)) (n : ℕ) : Rep (e^n) v (natural (a^n)) := by
  change Rep (Expr.pow e n) v (natural (a^n))
  induction n with
  | zero => simpa only [Expr.pow,pow_zero,Nat.cast_one] using rep_nat v 1
  | succ n ih => simpa only [Expr.pow,pow_succ] using rep_mul_nat ih h
private theorem rep_square {σ : Type*} {e : Expr σ} {v : σ → V} {p : Pair V}
    (h : Rep e v p) : Rep (e^2) v (natural (magnitude p*magnitude p)) := by
  have h1 : Rep (Expr.pow e 1) v p := by
    simpa only [Expr.pow,one_multiply,Nat.cast_one] using rep_mul (rep_nat v 1) h
  change Rep (Expr.pow e 2) v _
  exact equivalent_trans (rep_mul h1 h) (square_magnitude p)
private theorem rep_tsub {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) (hle : b≤a) :
    Rep (e-f) v (natural (a-b)) := by
  apply equivalent_trans (rep_sub h k)
  change (a+0)+0=(0+b)+(a-b)
  simpa only [add_zero,zero_add,add_comm] using (tsub_add_cancel_of_le hle).symm

private theorem zero_of_rep {σ : Type*} {e : Expr σ} {v : σ → V} {p : Pair V}
    (h : Rep e v p) (hz : e.splitNatural.1.evalSemiring v=e.splitNatural.2.evalSemiring v) :
    p.1=p.2 := by
  change e.splitNatural.1.evalSemiring v+p.2=e.splitNatural.2.evalSemiring v+p.1 at h
  rw [hz] at h
  exact (add_left_cancel h).symm

#check Nat.zero_le -- checkpoint expression helper proofs
/-- The five actual inputs of the accepted maintained-index/power clients. -/
def Equations (beta K MC MF : V) (v : Fin 14 → V) : Prop :=
  let J:=v 0; let F:=v 1; let alpha:=v 2; let z:=v 3
  let f:=v 4; let i:=v 5; let T:=v 6; let s:=v 7; let w:=v 8
  let N:=v 9; let eta:=v 10; let zeta:=v 11; let y:=v 12; let gamma:=v 13
  let q:=beta*J+1; let X:=w*q; let Y:=s*q^3; let E:=X*Y
  let k:=eta+zeta; let c:=k*Y+eta; let a:=E+Y
  let delta:=(a+1)*(a+3); let d:=X+a*c+gamma*(4*a+3)
  let R:=((q-1)*(q-F)+alpha)*(q^2-1)+(MC+q*MF)*J
  let tau:=E*N+k-R; let I:=delta*i*c*c
  let u:=(f*f*c*T-(f*f*R+c))+((f*f*R+c)-f*f*c*T)
  (K+w)*q+q=(K+w)*(F+alpha)+F+z*(q-1)+1 ∧
  tau*tau=1+(E*Y)*(E*Y+1)*k*k ∧ d*d=1+delta*c*c ∧
  f*f=1+delta*(i*c*c)*(i*c*c) ∧ I*I*u*u+y*y=1+I*I*y*y

/-- This binds the original syntax while every potentially negative cut is a pair. -/
private theorem literal_product (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hq : 2≤(p 0:V)*v 0+1) :
    let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
    let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
    let H:=4*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
    let M:=((p 2:V)+q*(p 3:V))*v 0
    let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
    let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
    let S:=delta*v 5*c*c
    let P:=(magnitude tp*magnitude tp,(E*Y)*(E*Y+1)*k*k)
    let Q:=(d*d,delta*c*c)
    let U:=(S*S*magnitude vp*magnitude vp+v 12*v 12,S*S*v 12*v 12)
    let W:=(((p 1:V)+v 8)*q+q,((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b)
    let Z:=(v 4*v 4,delta*(v 5*c*c)*(v 5*c*c))
    (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v →
    Equivalent (scale delta (product5 P Q U W Z)) (natural delta) := by
  run_tac Lean.logInfo "checkpoint literal start"
  dsimp only
  intro hz
  let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
  let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
  let H:=(4:V)*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
  let M:=((p 2:V)+q*(p 3:V))*v 0
  let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
  let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
  let S:=delta*v 5*c*c
  let eB : Expr (Fin 14):=Expr.constant (p 0:ℤ)*Expr.var 0
  let eq:=eB+1; let eX:=Expr.var 8*eq; let eY:=Expr.var 7*eq^3
  let eE:=eX*eY; let ek : Expr (Fin 14):=Expr.var 10+Expr.var 11; let ec:=ek*eY+Expr.var 10
  let ea:=eE+eY; let eH:=4*ea+3; let edelta:=ea^2+eH
  let ed:=eX+ea*ec+Expr.var 13*eH
  let eM:=(Expr.constant (p 2:ℤ)+eq*Expr.constant (p 3:ℤ))*Expr.var 0
  let er:=(eB*(eq-Expr.var 1)+Expr.var 2)*(eq^2-1)+eM
  let etau:=eE*Expr.var 9+ek-er
  let eV:=(Expr.var 4)^2*(ec*Expr.var 6-er)-ec
  let eS:=Expr.var 5*edelta*ec^2
  let ell:=eE*ek*eY
  let eP:=etau^2-ell*(ell+ek)
  let eQ:=ed^2-edelta*ec^2
  let eU:=eS^2*(eV^2-(Expr.var 12)^2)+(Expr.var 12)^2
  let eW:=(Expr.constant (p 1:ℤ)+Expr.var 8)*(eq-Expr.var 1-Expr.var 2)+
    (eq-Expr.var 1)-Expr.var 3*eB
  let eZ:=edelta*(Expr.var 4)^2-eS^2
  have hb : Rep eB v (natural b):=rep_mul_nat (rep_nat v (p 0)) (rep_var v 0)
  have hq' : Rep eq v (natural q):=rep_add_nat hb (rep_nat v 1)
  have hX : Rep eX v (natural X):=rep_mul_nat (rep_var v 8) hq'
  have hY : Rep eY v (natural Y):=rep_mul_nat (rep_var v 7) (rep_pow_nat hq' 3)
  have hE : Rep eE v (natural E):=rep_mul_nat hX hY
  have hk : Rep ek v (natural k):=rep_add_nat (rep_var v 10) (rep_var v 11)
  have hc : Rep ec v (natural c):=rep_add_nat (rep_mul_nat hk hY) (rep_var v 10)
  have ha : Rep ea v (natural a):=rep_add_nat hE hY
  have hH : Rep eH v (natural H):=rep_add_nat (rep_mul_nat (rep_nat v 4) ha) (rep_nat v 3)
  have hdelta : Rep edelta v (natural delta):=by
    have h:=rep_add_nat (rep_pow_nat ha 2) hH
    have he : a^2+H=delta:=by dsimp [H,delta]; ring
    exact he ▸ h
  have hd : Rep ed v (natural d):=rep_add_nat (rep_add_nat hX (rep_mul_nat ha hc))
    (rep_mul_nat (rep_var v 13) hH)
  have hM : Rep eM v (natural M):=rep_mul_nat
    (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat hq' (rep_nat v (p 3)))) (rep_var v 0)
  have hq1 : (1:V)≤q:=le_trans (by simp : (1:V)≤2) hq
  have hq21 : (1:V)≤q^2:=by simpa only [pow_two,one_mul] using mul_le_mul hq1 hq1 (by simp) (by simp)
  have hQ2:=rep_tsub (rep_pow_nat hq' 2) (rep_nat v 1) hq21
  have hqF : Rep (eq-Expr.var 1) v (q,v 1):=by
    simpa only [minus,natural,add_zero,zero_add] using rep_sub hq' (rep_var v 1)
  have hr : Rep er v (rp,rn):=by
    simpa only [multiply,plus,natural,mul_zero,zero_mul,add_zero,zero_add,rp,rn]
      using rep_add (rep_mul (rep_add (rep_mul hb hqF) (rep_var v 2)) hQ2) hM
  have htau : Rep etau v tp:=by
    simpa only [minus,natural,zero_add] using rep_sub (rep_add_nat (rep_mul_nat hE (rep_var v 9)) hk) hr
  have hV : Rep eV v vp:=by
    simpa only [minus,multiply,natural,mul_zero,zero_mul,add_zero,zero_add,pow_two,vp]
      using rep_sub (rep_mul (rep_pow_nat (rep_var v 4) 2)
        (rep_sub (rep_mul_nat hc (rep_var v 6)) hr)) hc
  have hS : Rep eS v (natural S):=by
    have h:=rep_mul_nat (rep_mul_nat (rep_var v 5) hdelta) (rep_pow_nat hc 2)
    have he : v 5*delta*c^2=S:=by dsimp [S]; ring
    exact he ▸ h
  have hell : Rep ell v (natural (E*k*Y)):=rep_mul_nat (rep_mul_nat hE hk) hY
  run_tac Lean.logInfo "checkpoint literal factors"
  have hP : Rep eP v (magnitude tp*magnitude tp,(E*Y)*(E*Y+1)*k*k):=by
    have h:=rep_sub (rep_square htau) (rep_mul_nat hell (rep_add_nat hell hk))
    have he : E*k*Y*(E*k*Y+k)=(E*Y)*(E*Y+1)*k*k:=by ring
    simpa only [minus,natural,add_zero,zero_add,he] using h
  have hQ : Rep eQ v (d*d,delta*c*c):=by
    simpa only [minus,natural,add_zero,zero_add,pow_two,mul_assoc] using
      rep_sub (rep_pow_nat hd 2) (rep_mul_nat hdelta (rep_pow_nat hc 2))
  have hU : Rep eU v (S*S*magnitude vp*magnitude vp+v 12*v 12,S*S*v 12*v 12):=by
    simpa only [minus,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul,pow_two,mul_assoc]
      using rep_add (rep_mul (rep_pow_nat hS 2)
        (rep_sub (rep_square hV) (rep_pow_nat (rep_var v 12) 2))) (rep_pow_nat (rep_var v 12) 2)
  have hW : Rep eW v (((p 1:V)+v 8)*q+q,((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b):=by
    simpa only [minus,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul]
      using rep_sub (rep_add (rep_mul (rep_add_nat (rep_nat v (p 1)) (rep_var v 8))
        (rep_sub hqF (rep_var v 2))) hqF) (rep_mul_nat (rep_var v 3) hb)
  have hZ : Rep eZ v (scale delta (v 4*v 4,delta*(v 5*c*c)*(v 5*c*c))):=by
    apply equivalent_trans (rep_sub (rep_mul_nat hdelta (rep_pow_nat (rep_var v 4) 2)) (rep_pow_nat hS 2))
    dsimp [Equivalent,minus,natural,scale,S]
    ring
  run_tac Lean.logInfo "checkpoint literal product"
  have hprod:=rep_mul (rep_mul (rep_mul (rep_mul hP hQ) hU) hW) hZ
  have hfull:=rep_sub hprod hdelta
  run_tac Lean.logInfo "checkpoint literal zero"
  have he:=zero_of_rep hfull hz
  change _=(_+delta) at he
  change _+0=_+delta
  simpa only [multiply,scale,product5,minus,natural,mul_add,add_mul,mul_assoc,
    mul_comm,mul_left_comm,add_zero] using he

#check Nat.zero_le -- checkpoint literal end
/-- Generic natural ports; the zero is the literal existing split evaluator. -/
theorem expressionAt_equations (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hbeta : 0<(p 0:V)) (hMC : (p 2:V)<(p 0:V)) (hMF : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v) :
    Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) v := by
  let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
  let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
  let H:=(4:V)*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
  let M:=((p 2:V)+q*(p 3:V))*v 0
  let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
  let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
  let S:=delta*v 5*c*c
  have onele (j : Fin 14) : (1:V)≤v j:=pos_iff_one_le.mp (hv j)
  have hq2 : (2:V)≤q:=by
    have h:=add_le_add (one_le_mul (pos_iff_one_le.mp hbeta) (onele 0)) (le_refl (1:V))
    simpa only [one_add_one_eq_two] using h
  have hq1 : (1:V)≤q:=le_trans (by simp : (1:V)≤2) hq2
  have hY : (2:V)≤Y:=calc
    2≤q:=hq2
    _≤q*q:=le_mul_of_one_le_right (by simp) hq1
    _≤q*q*q:=le_mul_of_one_le_right (by simp) hq1
    _≤v 7*(q*q*q):=le_mul_of_one_le_left (by simp) (onele 7)
    _=Y:=by dsimp [Y]; ring
  have hX : (1:V)≤X:=one_le_mul (onele 8) hq1
  have hE : (1:V)≤E:=one_le_mul hX (le_trans (by simp : (1:V)≤2) hY)
  have hn : (2:V)≤E*Y:=le_trans hY (le_mul_of_one_le_left (by simp) hE)
  have hdelta : 0<delta:=mul_pos (add_pos_of_nonneg_of_pos (by simp) (by simp))
    (add_pos_of_nonneg_of_pos (by simp) (by simp))
  have huNeg : S*S*magnitude vp*magnitude vp+v 12*v 12+1≠S*S*v 12*v 12:=by
    intro h
    apply ArithmeticNegativeNorms.square_aux_ne_negative S (magnitude vp) (v 12)
    calc
      _=S*S*magnitude vp*magnitude vp+v 12*v 12+1:=by ring
      _=S*S*v 12*v 12:=h
  have hp:=literal_product p v hq2 hz
  obtain ⟨hP,hQ,hU,hW,hZ⟩:=scaled_product5_positive delta hdelta hp
    (ArithmeticNegativeNorms.consecutive_ne_negative (E*Y) (magnitude tp) k hn)
    (ArithmeticNegativeNorms.main_ne_negative a d c)
    huNeg
    (ArithmeticNegativeNorms.strong_ne_negative a (v 4) (v 5) c)
  change magnitude tp*magnitude tp=(E*Y)*(E*Y+1)*k*k+1 at hP
  change d*d=delta*c*c+1 at hQ
  change S*S*magnitude vp*magnitude vp+v 12*v 12=S*S*v 12*v 12+1 at hU
  change ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b+1 at hW
  change v 4*v 4=delta*(v 5*c*c)*(v 5*c*c)+1 at hZ
  have hb : b=q-1:=by dsimp [q]; simp
  have ht : ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*(q-1)+1:=by
    simpa only [hb] using hW
  obtain ⟨hgap,hRlo,hRhi⟩:=ArithmeticPellFirstIndex.scalar_window q (p 0:V) (p 1:V)
    (p 2:V) (p 3:V) (v 0) (v 1) (v 2) (v 3) (v 8) (v 7)
    hbeta (hv 0) (hv 1) (hv 2) (hv 3) (hv 8) (hv 7) hMC hMF rfl ht
  let R:=((q-1)*(q-v 1)+v 2)*(q^2-1)+M
  have hF : v 1≤q:=by
    have hsub : 0<q-v 1:=lt_of_lt_of_le hgap tsub_le_self
    exact le_of_lt (tsub_pos_iff_lt.mp hsub)
  have hFq : q-v 1+v 1=q:=tsub_add_cancel_of_le hF
  have hrr : rp=rn+R:=by
    dsimp [rp,rn,R]
    rw [←hb]
    calc
      _=(b*(q-v 1+v 1)+v 2)*(q^2-1)+M:=by rw [hFq]
      _=_:=by ring
  have hRE : R+2<E:=by
    convert hRhi using 1 <;> dsimp [E,X,Y,R,M] <;> ring
  have hEN : R<E*v 9+k:=calc
    R<R+2:=lt_add_of_pos_right _ (by simp)
    _<E:=hRE
    _≤E*v 9:=le_mul_of_one_le_right (by simp) (onele 9)
    _≤E*v 9+k:=by simp
  have htau : magnitude tp=E*v 9+k-R:=by
    apply magnitude_of_add
    change E*v 9+k+rn=rp+(E*v 9+k-R)
    rw [hrr]
    have he:=tsub_add_cancel_of_le (le_of_lt hEN)
    calc
      _=(E*v 9+k-R+R)+rn:=by rw [he]
      _=_:=by ring
  have hvp : magnitude vp=(v 4*v 4*c*v 6-(v 4*v 4*R+c))+
      ((v 4*v 4*R+c)-v 4*v 4*c*v 6):=by
    dsimp [magnitude,vp]
    rw [hrr]
    have h1 : v 4*v 4*(c*v 6+rn)=v 4*v 4*c*v 6+v 4*v 4*rn:=by ring
    have h2 : v 4*v 4*(rn+R)+c=(v 4*v 4*R+c)+v 4*v 4*rn:=by ring
    rw [h1,h2,add_tsub_add_eq_tsub_right,add_tsub_add_eq_tsub_right]
  rw [htau] at hP
  rw [hvp] at hU
  change _ ∧ (E*v 9+k-R)*(E*v 9+k-R)=1+(E*Y)*(E*Y+1)*k*k ∧
    d*d=1+delta*c*c ∧ v 4*v 4=1+delta*(v 5*c*c)*(v 5*c*c) ∧
    S*S*((v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6))*
      ((v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6))+v 12*v 12=1+S*S*v 12*v 12
  exact ⟨ht,hP.trans (add_comm _ _),hQ.trans (add_comm _ _),
    hZ.trans (add_comm _ _),hU.trans (add_comm _ _)⟩

#check Nat.zero_le -- checkpoint generic equations end
private theorem current_bounds_nat :
    15≤CurrentMasks2011.beta ∧ CurrentMasks2011.lowPort<CurrentMasks2011.beta ∧
      CurrentMasks2011.highPort+CurrentMasks2011.beta<2*CurrentMasks2011.beta := by
  have hr : 16≤CurrentMasks2011.radix:=by change 16≤2^47; decide
  have hr1 : 1<CurrentMasks2011.radix:=by omega
  have hp : CurrentMasks2011.radix≤CurrentMasks2011.radix^2011:=
    Nat.le_self_pow (by decide) _
  have hb : 15≤CurrentMasks2011.beta:=by unfold CurrentMasks2011.beta; omega
  have hz : 0∈CurrentMasks2011.lowSupport:=by
    rw [CurrentMasks2011.lowSupport_def]
    simp
  have hm : 1≤LowMaskCoding.supportValue CurrentMasks2011.radix CurrentMasks2011.lowSupport:=by
    simpa only [LowMaskCoding.supportValue,pow_zero] using Finset.single_le_sum (fun j _ => Nat.zero_le (_^j)) hz
  have hl : CurrentMasks2011.lowPort<CurrentMasks2011.beta:=by
    unfold CurrentMasks2011.lowPort LowMaskCoding.mask
    rw [←CurrentMasks2011.beta]
    simp only [show (2:ℕ)-1=1 by decide,one_mul]
    exact Nat.sub_lt (by omega : 0<CurrentMasks2011.beta) (by omega : 0<LowMaskCoding.supportValue CurrentMasks2011.radix CurrentMasks2011.lowSupport)
  have hlen : CurrentMasks2011.highPrefix.length=1006:=by
    simp only [CurrentMasks2011.highPrefix,List.length_cons,List.length_append,List.length_replicate,List.length_nil]
  have hd : ∀x∈CurrentMasks2011.highPrefix,x<CurrentMasks2011.radix:=by
    intro x hx
    simp only [CurrentMasks2011.highPrefix,List.mem_cons,List.mem_append,List.mem_replicate,
      List.not_mem_nil,or_false] at hx
    norm_num [CurrentMasks2011.radix] at hx ⊢
    omega
  have hhigh : CurrentMasks2011.highPort<CurrentMasks2011.radix^1006:=by
    unfold CurrentMasks2011.highPort CurrentMasks2011.highDigits
    rw [Nat.ofDigits_append_replicate_zero]
    simpa only [hlen] using Nat.ofDigits_lt_base_pow_length hr1 hd
  have hpow : 2*CurrentMasks2011.radix^1006≤CurrentMasks2011.radix^2011:=calc
    _≤CurrentMasks2011.radix*CurrentMasks2011.radix^1006:=Nat.mul_le_mul_right _ (by omega)
    _=CurrentMasks2011.radix^1007:=by rw [pow_succ]; ring
    _≤CurrentMasks2011.radix^2011:=Nat.pow_le_pow_right (by omega) (by decide)
  have hpowpos : 0<CurrentMasks2011.radix^1006:=pow_pos (by omega) _
  have hh : CurrentMasks2011.highPort<CurrentMasks2011.beta:=by
    unfold CurrentMasks2011.beta
    omega
  exact ⟨hb,hl,by omega⟩

#check Nat.zero_le -- checkpoint natural bounds end
/-- The actual fixed port inequalities, cast into every selected internal model. -/
theorem current_bounds :
    (15:V)≤(CurrentMasks2011.beta:V) ∧
    (CurrentMasks2011.lowPort:V)<(CurrentMasks2011.beta:V) ∧
    ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)<2*(CurrentMasks2011.beta:V) := by
  obtain ⟨hb,hl,hh⟩:=current_bounds_nat
  exact ⟨by exact_mod_cast hb,by exact_mod_cast hl,by exact_mod_cast hh⟩

#check Nat.zero_le -- checkpoint cast bounds end
/-- No port, product, norm or transport oracle: only the actual positive zero. -/
theorem current_equations (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : expression.splitNatural.1.evalSemiring v=expression.splitNatural.2.evalSemiring v) :
    Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v := by
  let p : Fin 4 → ℕ:=![CurrentMasks2011.beta,CurrentKernel2011.K,
    CurrentMasks2011.lowPort,CurrentMasks2011.highPort+CurrentMasks2011.beta]
  have he : (fun j => (p j:ℤ))=CurrentWindowCarry2011.ports:=by
    funext j
    fin_cases j <;> simp [p,CurrentWindowCarry2011.ports,CurrentMasks2011.ports]
  obtain ⟨hb,hl,hh⟩:=current_bounds (V:=V)
  have hb0 : (0:V)<(CurrentMasks2011.beta:V):=lt_of_lt_of_le (by simp : (0:V)<15) hb
  apply expressionAt_equations p v hb0 hl hh hv
  simpa only [he,expression] using hz

private theorem split_positiveShift {σ : Type*} (e : Expr σ) (v : σ → V) :
    pairEval (positiveShift e) v=pairEval e (fun j => v j+1) := by
  induction e with
  | constant a => rfl
  | var j => simp [positiveShift,Expr.subst,pairEval,Expr.splitNatural,NatExpr.evalSemiring]
  | add e f he hf => exact congrArg₂ plus he hf
  | sub e f he hf => exact congrArg₂ minus he hf
  | mul e f he hf => exact congrArg₂ multiply he hf

/-- The maintained natural expression performs exactly one positive shift. -/
theorem current_natural_equations (v : Fin 14 → V)
    (hz : naturalExpression.splitNatural.1.evalSemiring v=
      naturalExpression.splitNatural.2.evalSemiring v) :
    Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V)
      (fun j => v j+1) := by
  apply current_equations _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
  have he:=split_positiveShift expression v
  have h1:=congrArg Prod.fst he
  have h2:=congrArg Prod.snd he
  change (pairEval naturalExpression v).1=(pairEval naturalExpression v).2 at hz
  change (pairEval expression (fun j => v j+1)).1=(pairEval expression (fun j => v j+1)).2
  exact h1.symm.trans (hz.trans h2)

end DiophantineConsistency.ArithmeticCarrierSoundness2011

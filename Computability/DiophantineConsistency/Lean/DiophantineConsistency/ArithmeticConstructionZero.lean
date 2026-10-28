import DiophantineConsistency.ArithmeticCarrierSoundness2011

/-! **K7a — the literal polynomial vanishes on a solution of the five equations**
(the converse of `ArithmeticCarrierSoundness2011.current_equations`), in every
model of IΣ1.

The signed-pair representation of the literal current expression is copied from
`ArithmeticCarrierSoundness2011` (`literal_product`, private there): the split
evaluator represents `P·Q·U·W·(δ·Z) − δ` for the five factor pairs. When each
factor pair is equivalent to `1`, the representation is `δ − δ`, so the two
split sides agree.

* `expressionAt_zero` — generic natural ports;
* `current_zero` — the actual ports: `Equations β K lowPort (highPort+β) v`,
  positivity and `F ≤ q` give the zero of the literal `expression` (with positivity
  this is `ArithmeticCurrentSentence2011.PositiveZero v`). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticConstructionZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ObjectCurrentEquation2011 ArithmeticCarrierSoundness2011
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

private theorem rep_nat {σ : Type*} (v : σ → V) (n : ℕ) :
    Rep (Expr.constant (n:ℤ)) v (natural (n:V)) := by
  simp [Rep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural,Equivalent]
private theorem rep_one {σ : Type*} (v : σ → V) :
    Rep (Expr.constant 1) v (natural (1:V)) := by
  simpa only [Nat.cast_one] using rep_nat v 1
private theorem rep_three {σ : Type*} (v : σ → V) :
    Rep (Expr.constant 3) v (natural (3:V)) := by
  simpa only [Nat.cast_ofNat] using rep_nat v 3
private theorem rep_four {σ : Type*} (v : σ → V) :
    Rep (Expr.constant 4) v (natural (4:V)) := by
  simpa only [Nat.cast_ofNat] using rep_nat v 4
private theorem rep_var {σ : Type*} (v : σ → V) (j : σ) :
    Rep (Expr.var j) v (natural (v j)) := equivalent_refl _
private theorem rep_add {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (Expr.add e f) v (plus p q) :=
  equivalent_plus h k
private theorem rep_sub {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (Expr.sub e f) v (minus p q) :=
  equivalent_minus h k
private theorem rep_mul {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (Expr.mul e f) v (multiply p q) :=
  equivalent_multiply h k
private theorem rep_add_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) :
    Rep (Expr.add e f) v (natural (a+b)) := by
  simpa only [plus,natural,add_zero] using rep_add h k
private theorem rep_mul_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) :
    Rep (Expr.mul e f) v (natural (a*b)) := by
  simpa only [multiply,natural,mul_zero,zero_mul,add_zero] using rep_mul h k
private theorem rep_pow_nat {σ : Type*} {e : Expr σ} {v : σ → V} {a : V}
    (h : Rep e v (natural a)) (n : ℕ) : Rep (e^n) v (natural (a^n)) := by
  change Rep (Expr.pow e n) v (natural (a^n))
  induction n with
  | zero =>
    change Rep (Expr.constant 1) v (natural (1:V))
    exact rep_one v
  | succ n ih =>
    change Rep (Expr.mul (Expr.pow e n) e) v (natural (a^n*a))
    exact rep_mul_nat ih h
private theorem rep_square {σ : Type*} {e : Expr σ} {v : σ → V} {p : Pair V}
    (h : Rep e v p) : Rep (e^2) v (natural (magnitude p*magnitude p)) := by
  have h1 : Rep (Expr.pow e 1) v p := by
    change Rep (Expr.mul (Expr.constant 1) e) v p
    simpa only [one_multiply,Nat.cast_one] using rep_mul (rep_one v) h
  change Rep (Expr.pow e 2) v _
  exact equivalent_trans (rep_mul h1 h) (square_magnitude p)
private theorem rep_tsub {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) (hle : b≤a) :
    Rep (Expr.sub e f) v (natural (a-b)) := by
  apply equivalent_trans (rep_sub h k)
  change (a+0)+0=(0+b)+(a-b)
  simpa only [add_zero,zero_add,add_comm] using (tsub_add_cancel_of_le hle).symm

private theorem zero_of_rep {σ : Type*} {e : Expr σ} {v : σ → V} {p : Pair V}
    (h : Rep e v p) (hz : e.splitNatural.1.evalSemiring v=e.splitNatural.2.evalSemiring v) :
    p.1=p.2 := by
  change e.splitNatural.1.evalSemiring v+p.2=e.splitNatural.2.evalSemiring v+p.1 at h
  rw [hz] at h
  exact (add_left_cancel h).symm

private theorem delta_identity (a : V) : a^2+(4*a+3)=(a+1)*(a+3) := by ring
private theorem scale_identity (a i c : V) : i*a*c^2=a*i*c*c := by ring
private theorem strong_pair (a i c f : V) :
    Equivalent (minus (natural (a*f^2)) (natural ((a*i*c*c)^2)))
      (scale a (f*f,a*(i*c*c)*(i*c*c))) := by
  dsimp [Equivalent,minus,natural,scale]
  ring
private theorem auxiliary_negative (S u y : V) :
    S*S*u*u+y*y+1≠S*S*y*y := by
  intro h
  apply ArithmeticNegativeNorms.square_aux_ne_negative S u y
  calc
    _=S*S*u*u+y*y+1:=by ring
    _=S*S*y*y:=h

private theorem multiply_scale (a : V) (p q : Pair V) :
    multiply p (scale a q)=scale a (multiply p q) := by
  apply Prod.ext <;> simp only [multiply,scale] <;> ring

/-- This binds the original syntax while every potentially negative cut is a pair. -/
private theorem literal_rep (p : Fin 4 → ℕ) (v : Fin 14 → V)
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
    Rep (expressionAt (fun j => (p j:ℤ))) v
      (minus (multiply (multiply (multiply (multiply P Q) U) W) (scale delta Z)) (natural delta)) := by
  dsimp only
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
  have hq' : Rep eq v (natural q):=rep_add_nat hb (rep_one v)
  have hX : Rep eX v (natural X):=rep_mul_nat (rep_var v 8) hq'
  have hY : Rep eY v (natural Y):=rep_mul_nat (rep_var v 7) (rep_pow_nat hq' 3)
  have hE : Rep eE v (natural E):=rep_mul_nat hX hY
  have hk : Rep ek v (natural k):=rep_add_nat (rep_var v 10) (rep_var v 11)
  have hc : Rep ec v (natural c):=rep_add_nat (rep_mul_nat hk hY) (rep_var v 10)
  have ha : Rep ea v (natural a):=rep_add_nat hE hY
  have hH : Rep eH v (natural H):=rep_add_nat (rep_mul_nat (rep_four v) ha) (rep_three v)
  have hdelta : Rep edelta v (natural delta):=by
    have h:=rep_add_nat (rep_pow_nat ha 2) hH
    have he : a^2+H=delta:=delta_identity a
    exact he ▸ h
  have hd : Rep ed v (natural d):=rep_add_nat (rep_add_nat hX (rep_mul_nat ha hc))
    (rep_mul_nat (rep_var v 13) hH)
  have hM : Rep eM v (natural M):=rep_mul_nat
    (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat hq' (rep_nat v (p 3)))) (rep_var v 0)
  have hq1 : (1:V)≤q:=le_trans (by simp : (1:V)≤2) hq
  have hq21 : (1:V)≤q^2:=by simpa only [pow_two,one_mul] using mul_le_mul hq1 hq1 (by simp) (by simp)
  have hQ2:=rep_tsub (rep_pow_nat hq' 2) (rep_one v) hq21
  have hqF : Rep (eq-Expr.var 1) v (q,v 1):=by
    have h:=rep_sub hq' (rep_var v 1)
    change Rep (eq-Expr.var 1) v _ at h
    simpa only [minus,natural,add_zero,zero_add] using h
  have hr : Rep er v (rp,rn):=by
    have h:=rep_add (rep_mul (rep_add (rep_mul hb hqF) (rep_var v 2)) hQ2) hM
    change Rep er v _ at h
    simpa only [multiply,plus,natural,mul_zero,zero_mul,add_zero,zero_add,rp,rn] using h
  have htau : Rep etau v tp:=by
    have h:=rep_sub (rep_add_nat (rep_mul_nat hE (rep_var v 9)) hk) hr
    change Rep etau v _ at h
    simpa only [minus,natural,zero_add] using h
  have hV : Rep eV v vp:=by
    have h:=rep_sub (rep_mul (rep_pow_nat (rep_var v 4) 2)
      (rep_sub (rep_mul_nat hc (rep_var v 6)) hr)) hc
    change Rep eV v _ at h
    simpa only [minus,multiply,natural,mul_zero,zero_mul,add_zero,zero_add,pow_two,vp] using h
  have hS : Rep eS v (natural S):=by
    have h:=rep_mul_nat (rep_mul_nat (rep_var v 5) hdelta) (rep_pow_nat hc 2)
    have he : v 5*delta*c^2=S:=scale_identity delta (v 5) c
    exact he ▸ h
  have hell : Rep ell v (natural (E*k*Y)):=rep_mul_nat (rep_mul_nat hE hk) hY
  have hP : Rep eP v (magnitude tp*magnitude tp,(E*Y)*(E*Y+1)*k*k):=by
    have h:=rep_sub (rep_square htau) (rep_mul_nat hell (rep_add_nat hell hk))
    change Rep eP v _ at h
    have he : E*k*Y*(E*k*Y+k)=(E*Y)*(E*Y+1)*k*k:=by ring
    simpa only [minus,natural,add_zero,zero_add,he] using h
  have hQ : Rep eQ v (d*d,delta*c*c):=by
    have h:=rep_sub (rep_pow_nat hd 2) (rep_mul_nat hdelta (rep_pow_nat hc 2))
    change Rep eQ v _ at h
    simpa only [minus,natural,add_zero,zero_add,pow_two,mul_assoc] using h
  have hU : Rep eU v (S*S*magnitude vp*magnitude vp+v 12*v 12,S*S*v 12*v 12):=by
    have h:=rep_add (rep_mul (rep_pow_nat hS 2)
      (rep_sub (rep_square hV) (rep_pow_nat (rep_var v 12) 2))) (rep_pow_nat (rep_var v 12) 2)
    change Rep eU v _ at h
    simpa only [minus,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul,pow_two,mul_assoc] using h
  have hW : Rep eW v (((p 1:V)+v 8)*q+q,((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b):=by
    have h:=rep_sub (rep_add (rep_mul (rep_add_nat (rep_nat v (p 1)) (rep_var v 8))
      (rep_sub hqF (rep_var v 2))) hqF) (rep_mul_nat (rep_var v 3) hb)
    change Rep eW v _ at h
    simpa only [minus,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using h
  have hZ : Rep eZ v (scale delta (v 4*v 4,delta*(v 5*c*c)*(v 5*c*c))):=by
    apply equivalent_trans (rep_sub (rep_mul_nat hdelta (rep_pow_nat (rep_var v 4) 2)) (rep_pow_nat hS 2))
    exact strong_pair delta (v 5) c (v 4)
  have hprod:=rep_mul (rep_mul (rep_mul (rep_mul hP hQ) hU) hW) hZ
  exact rep_sub hprod hdelta


private theorem equivalent_scale (a : V) {p q : Pair V} (h : Equivalent p q) :
    Equivalent (scale a p) (scale a q) := by
  change p.1+q.2=p.2+q.1 at h
  change a*p.1+a*q.2=a*p.2+a*q.1
  rw [← mul_add, ← mul_add, h]

/-- **Converse direction, generic ports.** -/
theorem expressionAt_zero (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hq : 2≤(p 0:V)*v 0+1) :
    let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
    let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
    let H:=4*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
    let M:=((p 2:V)+q*(p 3:V))*v 0
    let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
    let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
    let S:=delta*v 5*c*c
    magnitude tp*magnitude tp=(E*Y)*(E*Y+1)*k*k+1 →
    d*d=delta*c*c+1 →
    S*S*magnitude vp*magnitude vp+v 12*v 12=S*S*v 12*v 12+1 →
    ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b+1 →
    v 4*v 4=delta*(v 5*c*c)*(v 5*c*c)+1 →
    (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v := by
  intro b q X Y E k c a H delta d M rp rn tp vp S hP hQ hU hW hZ
  have hr := literal_rep p v hq
  have e1 : ∀ x y : V, x=y+1 → Equivalent ((x,y) : Pair V) (natural (1:V)) :=
    fun x y h => equivalent_one.mpr h
  have hprod := equivalent_multiply (equivalent_multiply (equivalent_multiply
    (equivalent_multiply (e1 _ _ hP) (e1 _ _ hQ)) (e1 _ _ hU)) (e1 _ _ hW))
    (equivalent_scale delta (e1 _ _ hZ))
  have hm := equivalent_minus hprod (equivalent_refl (natural delta))
  have hall := equivalent_trans hr hm
  change _ + _ = _ + _ at hall
  simp only [minus, multiply, natural, scale, mul_one, mul_zero, zero_mul, add_zero,
    zero_add] at hall
  rw [one_mul] at hall
  exact add_right_cancel hall

/-- **Generic ports: a positive solution of the five equations is a zero.** -/
theorem equations_zero (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hb1 : (1:V) ≤ (p 0:V)) (hF : v 1 ≤ (p 0:V)*v 0+1)
    (heq : Equations (p 0:V) (p 1:V) (p 2:V) (p 3:V) v) :
    (expressionAt (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (expressionAt (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v := by
  have hq : (2:V) ≤ (p 0:V)*v 0+1 := by
    have h := add_le_add (one_le_mul hb1 (pos_iff_one_le.mp (hv 0))) (le_refl (1:V))
    simpa only [one_add_one_eq_two] using h
  obtain ⟨ht, hP, hQ, hZ, hU⟩ := heq
  let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
  let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
  let M:=((p 2:V)+q*(p 3:V))*v 0
  let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
  let R:=((q-1)*(q-v 1)+v 2)*(q^2-1)+M
  have hb : q-1=b := add_tsub_cancel_right b 1
  have hFq : q-v 1+v 1=q := tsub_add_cancel_of_le hF
  have hrr : rp=rn+R := by
    show (b*q+v 2)*(q^2-1)+M=b*v 1*(q^2-1)+(((q-1)*(q-v 1)+v 2)*(q^2-1)+M)
    rw [hb]
    calc (b*q+v 2)*(q^2-1)+M=(b*(q-v 1+v 1)+v 2)*(q^2-1)+M := by rw [hFq]
      _=_ := by ring
  -- the first norm: τ = E·n + k − R ≥ 1
  have htau_pos : R < E*v 9+k := by
    by_contra hc
    have h0 : E*v 9+k-R=0 := tsub_eq_zero_of_le (le_of_not_gt hc)
    change (E*v 9+k-R)*(E*v 9+k-R)=1+(E*Y)*(E*Y+1)*k*k at hP
    rw [h0, zero_mul] at hP
    exact absurd hP.symm (ne_of_gt (lt_of_lt_of_le _root_.zero_lt_one (le_add_of_nonneg_right
      (Arithmetic.zero_le _))))
  have hmagP : magnitude ((E*v 9+k+rn,rp) : Pair V)=E*v 9+k-R := by
    apply magnitude_of_add
    rw [hrr]
    calc E*v 9+k+rn=(E*v 9+k-R+R)+rn := by rw [tsub_add_cancel_of_le htau_pos.le]
      _=_ := by ring
  have hmagU : magnitude ((v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c) : Pair V)=
      (v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6) := by
    dsimp only [magnitude]
    rw [hrr]
    have h1 : v 4*v 4*(c*v 6+rn)=v 4*v 4*c*v 6+v 4*v 4*rn := by ring
    have h2 : v 4*v 4*(rn+R)+c=(v 4*v 4*R+c)+v 4*v 4*rn := by ring
    rw [h1,h2,add_tsub_add_eq_tsub_right,add_tsub_add_eq_tsub_right]
  refine expressionAt_zero p v hq ?_ ?_ ?_ ?_ ?_
  · rw [hmagP]; exact hP.trans (add_comm _ _)
  · exact hQ.trans (add_comm _ _)
  · rw [hmagU]; exact hU.trans (add_comm _ _)
  · change ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*(q-1)+1 at ht
    rw [hb] at ht
    exact ht
  · exact hZ.trans (add_comm _ _)

/-- Ports given as natural parameters (no evaluation of the actual numerals). -/
theorem vector_zero (beta K MC high : ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hb1 : (1:V) ≤ (beta:V)) (hF : v 1 ≤ (beta:V)*v 0+1)
    (heq : Equations (beta:V) (K:V) (MC:V) ((high+beta:ℕ):V) v) :
    (expressionAt ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)]).splitNatural.1.evalSemiring v =
      (expressionAt ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)]).splitNatural.2.evalSemiring v := by
  let p : Fin 4 → ℕ := ![beta, K, MC, high + beta]
  have hpe : (fun j => (p j:ℤ)) = ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)] := by
    funext j
    fin_cases j <;> simp [p, Nat.cast_add]
  have hz := equations_zero p v hv hb1 hF heq
  rw [hpe] at hz
  exact hz

/-- **The actual polynomial vanishes on a positive solution of the five equations.** -/
theorem current_zero (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (hF : v 1 ≤ (CurrentMasks2011.beta:V)*v 0+1)
    (heq : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v) :
    expression.splitNatural.1.evalSemiring v = expression.splitNatural.2.evalSemiring v := by
  obtain ⟨hb15, _, _⟩ := current_bounds (V := V)
  exact vector_zero CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
    CurrentMasks2011.highPort v hv (le_trans (by norm_num) hb15) hF heq

end DiophantineConsistency.ArithmeticConstructionZero

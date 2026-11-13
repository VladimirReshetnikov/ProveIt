import DiophantineConsistency.ArithmeticCarrier94Soundness
import DiophantineConsistency.Carrier94Syntax
import DiophantineConsistency.ArithmeticNegativeNorms

/-! # The five equations of a positive 67/94 zero

`current94_equations`: in every model of `𝗜𝚺₁`, a positive zero of the literal
67/94 syntax (`Carrier94Syntax.expression94`) satisfies
`ArithmeticCarrier94Soundness.OrdinaryEquations`. The proof is the maintained
`ArithmeticCarrierSoundness2011.expressionAt_equations` with its literal pair
representation (`literal_rep`, `literal_product`, copied with their private
helpers) adapted to the 67/94 factors. The sign step follows `native/PROOF.md`
§3: all five factors are units; the strong factor `Ns = 1 + I² − Delta (f² − 1)`
is not `−1` modulo four (`ns_ne_negative`), so `Ns = 1` and `Aaux = I²`; then the
auxiliary factor is a square-coefficient norm, which excludes `−1`, and the
transport factor is `+1` because the other four are. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiophantineConsistency.ArithmeticCarrier94Extraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticSignedPairs ObjectCurrentEquation2011 ArithmeticCarrierSoundness2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.highPrefix
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private def plus (p q : Pair V) : Pair V := (p.1+q.1,p.2+q.2)
def minus (p q : Pair V) : Pair V := (p.1+q.2,p.2+q.1)
def pairEval {σ : Type*} (e : Expr σ) (v : σ → V) : Pair V :=
  (e.splitNatural.1.evalSemiring v,e.splitNatural.2.evalSemiring v)
def Rep {σ : Type*} (e : Expr σ) (v : σ → V) (p : Pair V) : Prop :=
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

private theorem square_magnitude (p : Pair V) :
    Equivalent (multiply p p) (natural (magnitude p*magnitude p)) := by
  wlog h : p.2 ≤ p.1 generalizing p
  · have hh := this (swap p) (le_of_not_ge h)
    rw [multiply_swap_left, multiply_swap_right, magnitude_swap] at hh
    simpa only [swap, Prod.eta] using hh
  let u := p.1-p.2
  have hu : p.1=p.2+u := by rw [add_comm,tsub_add_cancel_of_le h]
  rw [magnitude_of_add hu]
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
private theorem auxiliary_negative (S u y : V) :
    S*S*u*u+y*y+1≠S*S*y*y := by
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    ArithmeticNegativeNorms.square_aux_ne_negative S u y

/-- The ordinary strong factor is never `−1`: modulo four, `x² + t² + A² + 1 ≢ A² t²`. -/
theorem ns_ne_negative (A x t : V) : x*x+t*t+A*A+1 ≠ A*A*t*t := by
  intro he
  have h4 : (0:V)<4 := by simp
  have h1m : (1:V)%4=1 := by norm_num
  have h2m : (2:V)%4=2 := by norm_num
  have h3m : (3:V)%4=3 := by norm_num
  have h4m : (4:V)%4=0 := by norm_num
  have hm := congrArg (fun z : V => z%4) he
  rw [show A*A*t*t=(A*A)*(t*t) by ring,
    mod_add (a:=x*x+t*t+A*A) (b:=1) h4,mod_add (a:=x*x+t*t) (b:=A*A) h4,
    mod_add (a:=x*x) (b:=t*t) h4,mod_mul (a:=A*A) (b:=t*t) h4] at hm
  rcases ArithmeticNegativeNorms.square_mod_four x with hx|hx <;>
    rcases ArithmeticNegativeNorms.square_mod_four t with ht|ht <;>
    rcases ArithmeticNegativeNorms.square_mod_four A with hA|hA <;>
    simp only [hx,ht,hA,zero_add,add_zero,mul_zero,mul_one,
      one_add_one_eq_two,show (2:V)+1=3 by ring,show (3:V)+1=4 by ring,
      zero_mod,h1m,h2m,h3m,h4m] at hm
  all_goals (revert hm; norm_num)

/-- This binds the original syntax while every potentially negative cut is a pair. -/
theorem literal_rep94 (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hq : 2≤(p 0:V)*v 0+1) (hf : 1≤v 4) :
    let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
    let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
    let H:=4*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
    let M:=((p 2:V)+q*(p 3:V))*v 0
    let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
    let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
    let I:=v 5*c^2; let Aa:=delta*(v 4^2-1)
    let P:=(magnitude tp*magnitude tp,(E*Y)*(E*Y+1)*k*k)
    let Q:=(d*d,delta*c*c)
    let U:=(Aa*magnitude vp*magnitude vp+v 12*v 12,Aa*v 12*v 12)
    let W:=(((p 1:V)+v 8)*q+q,((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b)
    let Z:=(1+I^2,Aa)
    Rep (Carrier94Syntax.expressionAt94 (fun j => (p j:ℤ))) v
      (minus (multiply (multiply (multiply (multiply P Q) U) W) Z) (natural 1)) := by
  dsimp only
  let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
  let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
  let H:=(4:V)*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
  let M:=((p 2:V)+q*(p 3:V))*v 0
  let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
  let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
  let I:=v 5*c^2; let Aa:=delta*(v 4^2-1)
  let eB : Expr (Fin 14):=Expr.constant (p 0:ℤ)*Expr.var 0
  let eq:=eB+1; let eX:=Expr.var 8*eq; let eY:=Expr.var 7*eq^3
  let eE:=eX*eY; let ek : Expr (Fin 14):=Expr.var 10+Expr.var 11; let ec:=ek*eY+Expr.var 10
  let ea:=eE+eY; let eH:=4*ea+3; let edelta:=ea^2+eH
  let ed:=eX+ea*ec+Expr.var 13*eH
  let eM:=(Expr.constant (p 2:ℤ)+eq*Expr.constant (p 3:ℤ))*Expr.var 0
  let er:=(eB*(eq-Expr.var 1)+Expr.var 2)*(eq^2-1)+eM
  let etau:=eE*Expr.var 9+ek-er
  let eV:=(Expr.var 4)^2*(ec*Expr.var 6-er)-ec
  let eI:=Expr.var 5*ec^2
  let eA:=edelta*((Expr.var 4)^2-1)
  let ell:=eE*ek*eY
  let eP:=etau^2-ell*(ell+ek)
  let eQ:=ed^2-edelta*ec^2
  let eU:=eA*(eV^2-(Expr.var 12)^2)+(Expr.var 12)^2
  let eW:=(Expr.constant (p 1:ℤ)+Expr.var 8)*(eq-Expr.var 1-Expr.var 2)+
    (eq-Expr.var 1)-Expr.var 3*eB
  let eZ:=1+eI^2-eA
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
  have hI : Rep eI v (natural I):=rep_mul_nat (rep_var v 5) (rep_pow_nat hc 2)
  have hf2 : (1:V)≤v 4^2:=by simpa only [pow_two,one_mul] using mul_le_mul hf hf (by simp) (by simp)
  have hA : Rep eA v (natural Aa):=rep_mul_nat hdelta (rep_tsub (rep_pow_nat (rep_var v 4) 2) (rep_one v) hf2)
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
  have hU : Rep eU v (Aa*magnitude vp*magnitude vp+v 12*v 12,Aa*v 12*v 12):=by
    have h:=rep_add (rep_mul hA
      (rep_sub (rep_square hV) (rep_pow_nat (rep_var v 12) 2))) (rep_pow_nat (rep_var v 12) 2)
    change Rep eU v _ at h
    simpa only [minus,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul,pow_two,mul_assoc] using h
  have hW : Rep eW v (((p 1:V)+v 8)*q+q,((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b):=by
    have h:=rep_sub (rep_add (rep_mul (rep_add_nat (rep_nat v (p 1)) (rep_var v 8))
      (rep_sub hqF (rep_var v 2))) hqF) (rep_mul_nat (rep_var v 3) hb)
    change Rep eW v _ at h
    simpa only [minus,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using h
  have hZ : Rep eZ v (1+I^2,Aa):=by
    have h:=rep_sub (rep_add_nat (rep_one v) (rep_pow_nat hI 2)) hA
    change Rep eZ v _ at h
    simpa only [minus,natural,add_zero,zero_add] using h
  have hprod:=rep_mul (rep_mul (rep_mul (rep_mul hP hQ) hU) hW) hZ
  exact rep_sub hprod (rep_one v)

/-- This binds the original syntax while every potentially negative cut is a pair. -/
theorem literal_product94 (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hq : 2≤(p 0:V)*v 0+1) (hf : 1≤v 4) :
    let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
    let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
    let H:=4*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
    let M:=((p 2:V)+q*(p 3:V))*v 0
    let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
    let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
    let I:=v 5*c^2; let Aa:=delta*(v 4^2-1)
    let P:=(magnitude tp*magnitude tp,(E*Y)*(E*Y+1)*k*k)
    let Q:=(d*d,delta*c*c)
    let U:=(Aa*magnitude vp*magnitude vp+v 12*v 12,Aa*v 12*v 12)
    let W:=(((p 1:V)+v 8)*q+q,((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b)
    let Z:=(1+I^2,Aa)
    (Carrier94Syntax.expressionAt94 (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (Carrier94Syntax.expressionAt94 (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v →
    Equivalent (product5 P Q U W Z) (natural (1:V)) := by
  dsimp only
  intro hz
  have hfull := literal_rep94 p v hq hf
  have he := zero_of_rep hfull hz
  change _=(_+_) at he
  change _+0=_+_
  simpa only [product5, minus, natural, add_zero] using he


/-- A positive zero of the literal 67/94 syntax satisfies the five ordinary equations. -/
theorem expressionAt94_equations (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hbeta : 0<(p 0:V)) (hMC : (p 2:V)<(p 0:V)) (hMF : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j)
    (hz : (Carrier94Syntax.expressionAt94 (fun j => (p j:ℤ))).splitNatural.1.evalSemiring v=
      (Carrier94Syntax.expressionAt94 (fun j => (p j:ℤ))).splitNatural.2.evalSemiring v) :
    ArithmeticCarrier94Soundness.OrdinaryEquations (p 0:V) (p 1:V) (p 2:V) (p 3:V) v := by
  let b:=(p 0:V)*v 0; let q:=b+1; let X:=v 8*q; let Y:=v 7*q^3
  let E:=X*Y; let k:=v 10+v 11; let c:=k*Y+v 10; let a:=E+Y
  let H:=(4:V)*a+3; let delta:=(a+1)*(a+3); let d:=X+a*c+v 13*H
  let M:=((p 2:V)+q*(p 3:V))*v 0
  let rp:=(b*q+v 2)*(q^2-1)+M; let rn:=b*v 1*(q^2-1)
  let tp:=(E*v 9+k+rn,rp); let vp:=(v 4*v 4*(c*v 6+rn),v 4*v 4*rp+c)
  let I:=v 5*c^2; let Aa:=delta*(v 4^2-1)
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
  have hp:=literal_product94 p v hq2 (onele 4) hz
  obtain ⟨-,-,-,-,mZ⟩:=product5_magnitudes hp
  have hf2 : 1≤v 4*v 4:=one_le_mul (onele 4) (onele 4)
  have hAd : Aa+delta=delta*(v 4*v 4):=by
    dsimp only [Aa]
    rw [pow_two,← mul_add_one,tsub_add_cancel_of_le hf2]
  have hd : delta+1=(a+2)*(a+2):=by dsimp only [delta]; ring
  have hZneg : (1+I^2)+1≠Aa:=by
    intro h
    apply ns_ne_negative (a+2) I (v 4)
    calc
      I*I+v 4*v 4+(a+2)*(a+2)+1=((1+I^2)+1)+delta+v 4*v 4:=by rw [← hd]; ring
      _=Aa+delta+v 4*v 4:=by rw [h]
      _=delta*(v 4*v 4)+v 4*v 4:=by rw [hAd]
      _=(a+2)*(a+2)*v 4*v 4:=by rw [← hd]; ring
  have hZ1:=equivalent_one.mp (positive_of_magnitude_one mZ hZneg)
  change 1+I^2=Aa+1 at hZ1
  have hAa : Aa=I*I:=by
    have h1 : I*I+1=Aa+1:=by rw [← hZ1]; ring
    exact (add_right_cancel h1).symm
  have huNeg : Aa*magnitude vp*magnitude vp+v 12*v 12+1≠Aa*v 12*v 12:=by
    rw [hAa]; exact auxiliary_negative I (magnitude vp) (v 12)
  obtain ⟨hP,hQ,hU,hW,-⟩:=product5_positive hp
    (ArithmeticNegativeNorms.consecutive_ne_negative (E*Y) (magnitude tp) k hn)
    (ArithmeticNegativeNorms.main_ne_negative a d c)
    huNeg hZneg
  change magnitude tp*magnitude tp=(E*Y)*(E*Y+1)*k*k+1 at hP
  change d*d=delta*c*c+1 at hQ
  change Aa*magnitude vp*magnitude vp+v 12*v 12=Aa*v 12*v 12+1 at hU
  change ((p 1:V)+v 8)*q+q=((p 1:V)+v 8)*(v 1+v 2)+v 1+v 3*b+1 at hW
  have hIc : I=v 5*c*c:=by dsimp only [I]; ring
  have hstrong : (v 5*c*c)*(v 5*c*c)+delta=delta*v 4*v 4:=by
    rw [← hIc,← hAa,hAd]; ring
  rw [hAa,hIc] at hU
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
    convert hRhi using 1
    dsimp [E,X,Y,R,M]
    ring
  have hEN : R<E*v 9+k:=calc
    R<R+2:=lt_add_of_pos_right _ (by simp)
    _<E:=hRE
    _≤E*v 9:=le_mul_of_one_le_right (by simp) (onele 9)
    _≤E*v 9+k:=by simp
  have htau : magnitude tp=E*v 9+k-R:=by
    apply magnitude_of_add
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
    d*d=1+delta*c*c ∧ (v 5*c*c)*(v 5*c*c)+delta=delta*v 4*v 4 ∧
    (v 5*c*c)*(v 5*c*c)*((v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6))*
      ((v 4*v 4*c*v 6-(v 4*v 4*R+c))+((v 4*v 4*R+c)-v 4*v 4*c*v 6))+v 12*v 12=
        1+(v 5*c*c)*(v 5*c*c)*v 12*v 12
  exact ⟨ht,hP.trans (add_comm _ _),hQ.trans (add_comm _ _),
    hstrong,hU.trans (add_comm _ _)⟩

private theorem vector94_equations (beta K MC high : ℕ) (v : Fin 14 → V)
    (hb : 0<(beta:V)) (hl : (MC:V)<(beta:V))
    (hh : ((high+beta:ℕ):V)<2*(beta:V)) (hv : ∀j,0<v j)
    (hz : (Carrier94Syntax.expressionAt94 ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)]).splitNatural.1.evalSemiring v=
      (Carrier94Syntax.expressionAt94 ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)]).splitNatural.2.evalSemiring v) :
    ArithmeticCarrier94Soundness.OrdinaryEquations (beta:V) (K:V) (MC:V) ((high+beta:ℕ):V) v := by
  let p : Fin 4 → ℕ:=![beta,K,MC,high+beta]
  have he : (fun j => (p j:ℤ)) = ![(beta:ℤ),(K:ℤ),(MC:ℤ),(high:ℤ)+(beta:ℤ)] := by
    funext j
    fin_cases j <;> simp [p,Nat.cast_add]
  apply expressionAt94_equations p v hb hl hh hv
  rw [he]
  exact hz

/-- No port, product, norm or transport oracle: only the actual positive zero. -/
theorem current94_equations (v : Fin 14 → V) (hv : ∀j,0<v j)
    (hz : Carrier94Syntax.expression94.splitNatural.1.evalSemiring v=
      Carrier94Syntax.expression94.splitNatural.2.evalSemiring v) :
    ArithmeticCarrier94Soundness.OrdinaryEquations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v := by
  obtain ⟨hb,hl,hh⟩:=current_bounds (V:=V)
  have hb0 : (0:V)<(CurrentMasks2011.beta:V):=lt_of_lt_of_le (by simp : (0:V)<15) hb
  exact vector94_equations CurrentMasks2011.beta CurrentKernel2011.K CurrentMasks2011.lowPort
    CurrentMasks2011.highPort v hb0 hl hh hv hz


end DiophantineConsistency.ArithmeticCarrier94Extraction

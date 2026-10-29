import DiophantineConsistency.ArithmeticAdaptiveTransportQuotient2011

/-! The literal adaptive main root is positive; its quotient is oriented. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs
open ArithmeticAdaptiveFactorMagnitude2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveQuotients2011 ArithmeticAdaptiveFirstDivisibility2011
open ArithmeticAdaptiveTransport2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private def plus (p q : Pair V) : Pair V := (p.1+q.1,p.2+q.2)
private def minus (p q : Pair V) : Pair V := (p.1+q.2,p.2+q.1)
private def Rep {σ : Type*} (e : Expr σ) (v : σ → V) (p : Pair V) : Prop :=
  Equivalent (pairEval e v) p
private theorem plus_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (plus p r) (plus q s) := by
  change p.1+q.2=p.2+q.1 at h
  change r.1+s.2=r.2+s.1 at k
  change (p.1+r.1)+(q.2+s.2)=(p.2+r.2)+(q.1+s.1)
  calc
    _=(p.1+q.2)+(r.1+s.2) := by ring
    _=(p.2+q.1)+(r.2+s.1) := by rw [h,k]
    _=_ := by ring
private theorem minus_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (minus p r) (minus q s) :=
  plus_equiv h (show Equivalent (swap r) (swap s) from k.symm)
private theorem rep_nat {σ : Type*} (v : σ → V) (n : ℕ) :
    Rep (.constant (n:ℤ)) v (natural (n:V)) := by
  simp [Rep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural,Equivalent]
private theorem rep_var {σ : Type*} (v : σ → V) (j : σ) :
    Rep (.var j) v (natural (v j)) := equivalent_refl _
private theorem rep_add {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (.add e f) v (plus p q) := plus_equiv h k
private theorem rep_sub {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (.sub e f) v (minus p q) := minus_equiv h k
private theorem rep_mul {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : Rep e v p) (k : Rep f v q) : Rep (.mul e f) v (multiply p q) := equivalent_multiply h k
private theorem rep_add_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) :
    Rep (.add e f) v (natural (a+b)) := by simpa [plus,natural] using rep_add h k
private theorem rep_mul_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) :
    Rep (.mul e f) v (natural (a*b)) := by simpa [multiply,natural] using rep_mul h k
private theorem rep_tsub {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : Rep e v (natural a)) (k : Rep f v (natural b)) (hle : b≤a) :
    Rep (.sub e f) v (natural (a-b)) := by
  apply equivalent_trans (rep_sub h k)
  change (a+0)+0=(0+b)+(a-b)
  simpa only [add_zero,zero_add,add_comm] using (tsub_add_cancel_of_le hle).symm

/-- Exact signed representation of the main root, after the proved q>F gap. -/
theorem main_root_rep (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hq : 1≤1+v 0*(p 0:V)) (hF : v 1≤1+v 0*(p 0:V)) :
    let b : V := v 0*(p 0:V)
    let q : V := 1+b
    let U : V := v 7*(q*q)
    let E : V := v 6*v 7
    let k : V := v 9+v 10
    let c : V := v 9+v 7*k
    let a : V := E+v 7
    let H : V := 3+4*a
    let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
    Equivalent (pairEval (rootTerm (factors (fun j => (p j:ℤ))).2.1) v)
      (U*(v 6+a*c)+H*(U*v 12+E*q+R+1),H*k) := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eU : Expr (Fin 13) := .mul (.var 7) (.mul eQ eQ)
  let eE : Expr (Fin 13) := .mul (.var 6) (.var 7)
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add eE (.var 7)
  let eH : Expr (Fin 13) := .add (.constant 3) (.mul (.constant 4) eA)
  let eR : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eD : Expr (Fin 13) := .add
    (.mul eU (.add (.var 6) (.mul eA eC)))
    (.mul eH (.sub (.add (.mul eU (.var 12)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))))
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let U : V := v 7*(q*q)
  let E : V := v 6*v 7
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := E+v 7
  let H : V := 3+4*a
  let R : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  have hB : Rep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : Rep eQ v (natural q) := rep_add_nat (rep_nat v 1) hB
  have hU : Rep eU v (natural U) := rep_mul_nat (rep_var v 7) (rep_mul_nat hQ hQ)
  have hE : Rep eE v (natural E) := rep_mul_nat (rep_var v 6) (rep_var v 7)
  have hK : Rep eK v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hC : Rep eC v (natural c) := rep_add_nat (rep_var v 9) (rep_mul_nat (rep_var v 7) hK)
  have hA : Rep eA v (natural a) := rep_add_nat hE (rep_var v 7)
  have hH : Rep eH v (natural H) := rep_add_nat (rep_nat v 3) (rep_mul_nat (rep_nat v 4) hA)
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR : Rep eR v (natural R) := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_nat v 1) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hneg : Rep (.sub (.sub eK eR) (.constant 1)) v (k,R+1) := by
    have h := rep_sub (rep_sub hK hR) (rep_nat v 1)
    simpa only [minus,natural,add_zero,zero_add,Nat.cast_one,add_assoc] using h
  have hshift : Rep (.sub (.add (.mul eU (.var 12)) (.mul eE eQ))
      (.sub (.sub eK eR) (.constant 1))) v (U*v 12+E*q+R+1,k) := by
    have h := rep_sub (rep_add_nat (rep_mul_nat hU (rep_var v 12)) (rep_mul_nat hE hQ)) hneg
    simpa only [minus,natural,add_zero,zero_add,add_assoc] using h
  have hD := rep_add (rep_mul_nat hU (rep_add_nat (rep_var v 6) (rep_mul_nat hA hC)))
    (rep_mul hH hshift)
  change Rep (rootTerm (factors (fun j => (p j:ℤ))).2.1) v _
  simpa only [Rep,plus,multiply,natural,add_zero,zero_add,mul_zero,zero_mul] using hD

end DiophantineConsistency.ArithmeticAdaptiveMainOrientation2011

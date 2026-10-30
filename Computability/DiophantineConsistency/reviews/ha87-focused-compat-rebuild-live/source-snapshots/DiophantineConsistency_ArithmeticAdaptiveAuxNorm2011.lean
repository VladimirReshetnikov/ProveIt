import DiophantineConsistency.ArithmeticAdaptiveStrongNorm2011

/-! Literal adaptive auxiliary factor as an internal signed Pell norm. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveFactorUnits2011 ArithmeticAdaptiveScaledNorms2011
open ArithmeticAdaptiveTransport2011 ArithmeticAdaptiveStrongNorm2011
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
private theorem rep_one {σ : Type*} (v : σ → V) : Rep (.constant 1) v (natural (1:V)) := by
  simpa only [Nat.cast_one] using rep_nat v 1
private theorem rep_three {σ : Type*} (v : σ → V) : Rep (.constant 3) v (natural (3:V)) := by
  simpa only [Nat.cast_ofNat] using rep_nat v 3
private theorem rep_four {σ : Type*} (v : σ → V) : Rep (.constant 4) v (natural (4:V)) := by
  simpa only [Nat.cast_ofNat] using rep_nat v 4
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

private theorem represented_unit {p : Pair V} {a b : V}
    (hu : p.1=p.2+1) (hr : Equivalent p (a,b)) : a=b+1 := by
  change p.1+b=p.2+a at hr
  have h : p.2+(1+b)=p.2+a := calc
    _=(p.2+1)+b := by ring
    _=p.1+b := by rw [hu]
    _=p.2+a := hr
  have h' := add_left_cancel h
  simpa only [add_comm] using h'.symm

def AuxNorm (p : Fin 4 → ℕ) (v : Fin 13 → V) : Prop :=
  let q : V := 1+v 0*(p 0:V)
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let I : V := (c*c)*v 4
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let L : V := (v 3*v 3)*v 5*c
  let M : V := (v 3*v 3)*R+c
  let z : V := magnitude (L,M)
  let y : V := magnitude (L+v 11,M)
  I*I*z*z+y*y=1+I*I*y*y

theorem expressionAt_aux_norm (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : InternalZero (expressionAt (fun j => (p j:ℤ))) v) : AuxNorm p v := by
  let eB : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let eQ : Expr (Fin 13) := .add (.constant 1) eB
  let eK : Expr (Fin 13) := .add (.var 9) (.var 10)
  let eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) eK)
  let eA : Expr (Fin 13) := .add (.mul (.var 6) (.var 7)) (.var 7)
  let eD : Expr (Fin 13) := .add (.add (.constant 3) (.mul (.constant 4) eA)) (.mul eA eA)
  let eI : Expr (Fin 13) := .mul (.mul eC eC) (.var 4)
  let eF : Expr (Fin 13) := .var 3
  let eR : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub eQ (.var 1)) eB)) (.sub (.mul eQ eQ) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) eQ)))
  let eV : Expr (Fin 13) := .sub (.mul (.mul eF eF) (.sub (.mul (.var 5) eC) eR)) eC
  let eY : Expr (Fin 13) := .add eV (.var 11)
  let eH : Expr (Fin 13) := .mul eD (.sub (.mul eF eF) (.constant 1))
  let b : V := v 0*(p 0:V)
  let q : V := 1+b
  let k : V := v 9+v 10
  let c : V := v 9+v 7*k
  let a : V := v 6*v 7+v 7
  let D : V := (3+4*a)+a*a
  let I : V := (c*c)*v 4
  let R' : V := (v 2+(q-v 1)*b)*(q*q-1)+v 0*((p 2:V)+(p 3:V)*q)
  let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
  let L : V := (v 3*v 3)*v 5*c
  let M : V := (v 3*v 3)*R+c
  let z : V := magnitude (L,M)
  let y : V := magnitude (L+v 11,M)
  have hq : 1≤q := le_of_lt (scaled_parameters_positive p v hb hv).1
  have hgap : v 1+v 2<q := tsub_pos_iff_lt.mp (expressionAt_transport_positive p v hb hv hz).2
  have hF : v 1≤q := le_trans (by simp : v 1≤v 1+v 2) (le_of_lt hgap)
  have hbq : q-1=b := by dsimp [q]; rw [add_comm]; simp
  have hRank : R'=R := by dsimp [R,R']; rw [hbq]; simp only [pow_two]; ring
  have hB : Rep eB v (natural b) := rep_mul_nat (rep_var v 0) (rep_nat v (p 0))
  have hQ : Rep eQ v (natural q) := rep_add_nat (rep_one v) hB
  have hK : Rep eK v (natural k) := rep_add_nat (rep_var v 9) (rep_var v 10)
  have hC : Rep eC v (natural c) := rep_add_nat (rep_var v 9) (rep_mul_nat (rep_var v 7) hK)
  have hA : Rep eA v (natural a) := rep_add_nat (rep_mul_nat (rep_var v 6) (rep_var v 7)) (rep_var v 7)
  have hD : Rep eD v (natural D) := rep_add_nat
    (rep_add_nat (rep_three v) (rep_mul_nat (rep_four v) hA)) (rep_mul_nat hA hA)
  have hq2 : (1:V)≤q*q := by simpa only [one_mul] using mul_le_mul hq hq (by simp) (by simp)
  have hR' : Rep eR v (natural R') := rep_add_nat
    (rep_mul_nat (rep_add_nat (rep_var v 2) (rep_mul_nat (rep_tsub hQ (rep_var v 1) hF) hB))
      (rep_tsub (rep_mul_nat hQ hQ) (rep_one v) hq2))
    (rep_mul_nat (rep_var v 0) (rep_add_nat (rep_nat v (p 2)) (rep_mul_nat (rep_nat v (p 3)) hQ)))
  have hR : Rep eR v (natural R) := by rw [hRank] at hR'; exact hR'
  have hF2 : Rep (.mul eF eF) v (natural (v 3*v 3)) := rep_mul_nat (rep_var v 3) (rep_var v 3)
  have hn : I*I+D=D*(v 3*v 3) := expressionAt_strong_norm p v hz
  have hH : Rep eH v (natural (I*I)) := by
    have h := rep_mul hD (rep_sub hF2 (rep_one v))
    have h' : Rep eH v (D*(v 3*v 3),D) := by
      simpa only [multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul,mul_one] using h
    apply equivalent_trans h'
    change D*(v 3*v 3)+0=D+I*I
    simpa only [add_zero,zero_add,add_comm] using hn.symm
  have hV : Rep eV v (L,M) := by
    have h := rep_sub (rep_mul hF2 (rep_sub (rep_mul_nat (rep_var v 5) hC) hR)) hC
    simpa only [L,M,multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul,mul_assoc] using h
  have hY : Rep eY v (L+v 11,M) := by
    have h := rep_add hV (rep_var v 11)
    simpa only [plus,natural,add_zero] using h
  have hV2 : Rep (.mul eV eV) v (natural (z*z)) :=
    equivalent_trans (rep_mul hV hV) (square_magnitude (L,M))
  have hY2 : Rep (.mul eY eY) v (natural (y*y)) :=
    equivalent_trans (rep_mul hY hY) (square_magnitude (L+v 11,M))
  have haux : Rep (.sub (.mul eY eY) (.mul eH (.sub (.mul eY eY) (.mul eV eV)))) v
      (y*y+(I*I)*(z*z),(I*I)*(y*y)) := by
    have h := rep_sub hY2 (rep_mul hH (rep_sub hY2 hV2))
    simpa only [multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul] using h
  have hu := (expressionAt_factor_units (fun j => (p j:ℤ)) v hz).2.2.1
  change (pairEval (.sub (.mul eY eY) (.mul eH (.sub (.mul eY eY) (.mul eV eV)))) v).1 =
    (pairEval (.sub (.mul eY eY) (.mul eH (.sub (.mul eY eY) (.mul eV eV)))) v).2+1 at hu
  have he := represented_unit hu haux
  calc
    I*I*z*z+y*y = y*y+(I*I)*(z*z) := by ring
    _=(I*I)*(y*y)+1 := he
    _=1+I*I*y*y := by ring

private theorem beta_positive_nat : 0<CurrentMasks2011.beta := by
  have hr : 1<CurrentMasks2011.radix := by unfold CurrentMasks2011.radix; norm_num
  have hp : 1<CurrentMasks2011.radix^2011 := one_lt_pow₀ hr (by decide)
  unfold CurrentMasks2011.beta
  omega

theorem current_aux_norm (v : Fin 13 → V) (hv : ∀j,0<v j)
    (hz : InternalZero expression v) : AuxNorm currentPorts v := by
  have hb : 0<(CurrentMasks2011.beta:V) := by exact_mod_cast beta_positive_nat
  have hp : 0<(currentPorts 0:V) := by simpa only [currentPorts,Matrix.cons_val_zero] using hb
  apply expressionAt_aux_norm currentPorts v hp hv
  rw [currentPorts_cast]; exact hz

theorem current_natural_aux_norm (v : Fin 13 → V) (hz : InternalZero naturalExpression v) :
    AuxNorm currentPorts (fun j => v j+1) :=
  current_aux_norm _ (fun j => lt_of_le_of_lt (Arithmetic.zero_le (v j)) (lt_add_one _))
    ((internalZero_positiveShift expression v).mp hz)
end DiophantineConsistency.ArithmeticAdaptiveAuxNorm2011

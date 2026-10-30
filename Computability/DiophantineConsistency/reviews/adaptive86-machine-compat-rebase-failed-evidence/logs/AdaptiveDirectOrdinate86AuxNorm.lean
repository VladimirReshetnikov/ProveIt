import DiophantineConsistency.AdaptiveDirectOrdinate86Units

/-! Auxiliary norm directly from actual direct-ordinate factor units. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Factors AdaptiveDirectOrdinate86Units
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

def eC : Expr (Fin 13) := .add (.var 9) (.mul (.var 7) (.add (.var 9) (.var 10)))
def eI : Expr (Fin 13) := .mul (.mul eC eC) (.var 4)
def eQ : Expr (Fin 13) :=
  let a : Expr (Fin 13) := .add (.mul (.var 6) (.var 7)) (.var 7)
  .mul (.add (.add (.constant 3) (.mul (.constant 4) a)) (.mul a a))
    (.sub (.mul (.var 3) (.var 3)) (.constant 1))
def eV (p : Fin 4 → ℤ) : Expr (Fin 13) :=
  let b : Expr (Fin 13) := .mul (.var 0) (.constant (p 0))
  let q : Expr (Fin 13) := .add (.constant 1) b
  let rank : Expr (Fin 13) := .add
    (.mul (.add (.var 2) (.mul (.sub q (.var 1)) b)) (.sub (.mul q q) (.constant 1)))
    (.mul (.var 0) (.add (.constant (p 2)) (.mul (.constant (p 3)) q)))
  .sub (.mul (.mul (.var 3) (.var 3)) (.sub (.mul (.var 5) eC) rank)) eC

def AuxNorm86 (p : Fin 4 → ℤ) (v : Fin 13 → V) : Prop :=
  let c := v 9+v 7*(v 9+v 10)
  let I := (c*c)*v 4
  let z := magnitude (pairEval (eV p) v)
  let y := v 11
  I*I*z*z+y*y=1+I*I*y*y

/-- The two actual units force the direct-ordinate auxiliary norm, with no
    rank orientation, residue, or positivity premises. -/
theorem expressionAt_aux_norm86 (p : Fin 4 → ℤ) (v : Fin 13 → V)
    (hz : InternalZero (expressionAt86 p) v) : AuxNorm86 p v := by
  let c : V := v 9+v 7*(v 9+v 10)
  let I : V := (c*c)*v 4
  let z : V := magnitude (pairEval (eV p) v)
  let y : V := v 11
  have hi : Rep eI v (natural I) := by
    have hc : Rep eC v (natural c) := rep_add_nat (rep_var v 9)
      (rep_mul_nat (rep_var v 7) (rep_add_nat (rep_var v 9) (rep_var v 10)))
    exact rep_mul_nat (rep_mul_nat hc hc) (rep_var v 4)
  have hu := (expressionAt_factor_units86 p v hz).2.2.2
  change (pairEval (.add (.constant 1) (.sub (.mul eI eI) eQ)) v).1 =
    (pairEval (.add (.constant 1) (.sub (.mul eI eI) eQ)) v).2+1 at hu
  have hs : Rep (.add (.constant 1) (.sub (.mul eI eI) eQ)) v
      (1+I*I+(pairEval eQ v).2,(pairEval eQ v).1) := by
    have h := rep_add (rep_one v) (rep_sub (rep_mul_nat hi hi)
      (equivalent_refl (pairEval eQ v)))
    simpa only [plus,minus,natural,add_zero,zero_add,add_assoc] using h
  have he := represented_unit hu hs
  have hqe : (pairEval eQ v).1=(pairEval eQ v).2+I*I := by
    have ht : 1+((pairEval eQ v).2+I*I)=1+(pairEval eQ v).1 := by
      calc
        _=1+I*I+(pairEval eQ v).2 := by ring
        _=(pairEval eQ v).1+1 := he
        _=1+(pairEval eQ v).1 := by ring
    exact (add_left_cancel ht).symm
  have hq : Rep eQ v (natural (I*I)) := by
    change (pairEval eQ v).1+0=(pairEval eQ v).2+I*I
    simpa using hqe
  have hv2 : Rep (.mul (eV p) (eV p)) v (natural (z*z)) :=
    equivalent_trans (rep_mul (equivalent_refl _) (equivalent_refl _))
      (square_magnitude (pairEval (eV p) v))
  have hy2 : Rep (.mul (.var 11) (.var 11)) v (natural (y*y)) :=
    rep_mul_nat (rep_var v 11) (rep_var v 11)
  have haux : Rep (.sub (.mul (.var 11) (.var 11))
      (.mul eQ (.sub (.mul (.var 11) (.var 11)) (.mul (eV p) (eV p))))) v
      (y*y+(I*I)*(z*z),(I*I)*(y*y)) := by
    have h := rep_sub hy2 (rep_mul hq (rep_sub hy2 hv2))
    simpa only [multiply,minus,natural,add_zero,zero_add,mul_zero,zero_mul] using h
  have hunit := (expressionAt_factor_units86 p v hz).2.2.1
  change (pairEval (.sub (.mul (.var 11) (.var 11))
    (.mul eQ (.sub (.mul (.var 11) (.var 11)) (.mul (eV p) (eV p))))) v).1 =
    (pairEval (.sub (.mul (.var 11) (.var 11))
    (.mul eQ (.sub (.mul (.var 11) (.var 11)) (.mul (eV p) (eV p))))) v).2+1 at hunit
  have hh := represented_unit hunit haux
  change I*I*z*z+y*y=1+I*I*y*y
  calc
    _=y*y+(I*I)*(z*z) := by ring
    _=(I*I)*(y*y)+1 := hh
    _=1+I*I*y*y := by ring
end DiophantineConsistency.AdaptiveDirectOrdinate86AuxNorm

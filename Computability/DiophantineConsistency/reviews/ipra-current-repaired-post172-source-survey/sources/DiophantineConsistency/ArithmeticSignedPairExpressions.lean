import DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011

/-! Signed-pair representations of expressions, shared by adaptive proofs. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticSignedPairExpressions
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def plus (p q : Pair V) : Pair V := (p.1+q.1,p.2+q.2)
def minus (p q : Pair V) : Pair V := (p.1+q.2,p.2+q.1)
def SignedRep {σ : Type*} (e : Expr σ) (v : σ → V) (p : Pair V) : Prop :=
  Equivalent (pairEval e v) p
theorem plus_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (plus p r) (plus q s) := by
  change p.1+q.2=p.2+q.1 at h
  change r.1+s.2=r.2+s.1 at k
  change (p.1+r.1)+(q.2+s.2)=(p.2+r.2)+(q.1+s.1)
  calc
    _=(p.1+q.2)+(r.1+s.2) := by ring
    _=(p.2+q.1)+(r.2+s.1) := by rw [h,k]
    _=_ := by ring
theorem minus_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (minus p r) (minus q s) :=
  plus_equiv h (show Equivalent (swap r) (swap s) from k.symm)
theorem rep_nat {σ : Type*} (v : σ → V) (n : ℕ) :
    SignedRep (.constant (n:ℤ)) v (natural (n:V)) := by
  simp [SignedRep,pairEval,Expr.splitNatural,NatExpr.evalSemiring,natural,Equivalent]
theorem rep_one {σ : Type*} (v : σ → V) : SignedRep (.constant 1) v (natural (1:V)) := by
  simpa only [Nat.cast_one] using rep_nat v 1
theorem rep_three {σ : Type*} (v : σ → V) : SignedRep (.constant 3) v (natural (3:V)) := by
  simpa only [Nat.cast_ofNat] using rep_nat v 3
theorem rep_four {σ : Type*} (v : σ → V) : SignedRep (.constant 4) v (natural (4:V)) := by
  simpa only [Nat.cast_ofNat] using rep_nat v 4
theorem rep_var {σ : Type*} (v : σ → V) (j : σ) :
    SignedRep (.var j) v (natural (v j)) := equivalent_refl _
theorem rep_add {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : SignedRep e v p) (k : SignedRep f v q) : SignedRep (.add e f) v (plus p q) := plus_equiv h k
theorem rep_sub {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : SignedRep e v p) (k : SignedRep f v q) : SignedRep (.sub e f) v (minus p q) := minus_equiv h k
theorem rep_mul {σ : Type*} {e f : Expr σ} {v : σ → V} {p q : Pair V}
    (h : SignedRep e v p) (k : SignedRep f v q) : SignedRep (.mul e f) v (multiply p q) := equivalent_multiply h k
theorem rep_add_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : SignedRep e v (natural a)) (k : SignedRep f v (natural b)) :
    SignedRep (.add e f) v (natural (a+b)) := by simpa [plus,natural] using rep_add h k
theorem rep_mul_nat {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : SignedRep e v (natural a)) (k : SignedRep f v (natural b)) :
    SignedRep (.mul e f) v (natural (a*b)) := by simpa [multiply,natural] using rep_mul h k
theorem rep_tsub {σ : Type*} {e f : Expr σ} {v : σ → V} {a b : V}
    (h : SignedRep e v (natural a)) (k : SignedRep f v (natural b)) (hle : b≤a) :
    SignedRep (.sub e f) v (natural (a-b)) := by
  apply equivalent_trans (rep_sub h k)
  change (a+0)+0=(0+b)+(a-b)
  simpa only [add_zero,zero_add,add_comm] using (tsub_add_cancel_of_le hle).symm

theorem square_magnitude (p : Pair V) :
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

theorem represented_unit {p : Pair V} {a b : V}
    (hu : p.1=p.2+1) (hr : Equivalent p (a,b)) : a=b+1 := by
  change p.1+b=p.2+a at hr
  have h : p.2+(1+b)=p.2+a := calc
    _=(p.2+1)+b := by ring
    _=p.1+b := by rw [hu]
    _=p.2+a := hr
  have h' := add_left_cancel h
  simpa only [add_comm] using h'.symm

end DiophantineConsistency.ArithmeticSignedPairExpressions

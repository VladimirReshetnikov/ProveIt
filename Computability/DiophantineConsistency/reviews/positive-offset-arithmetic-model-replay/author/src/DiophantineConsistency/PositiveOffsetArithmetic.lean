import DiophantineConsistency.InternalResidualSquares

/-! Convert nonnegative witness coordinates to strictly positive coordinates
without changing zero existence, uniformly in every IΣ₁ model. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.PositiveOffsetArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context ArithmeticSignedPairs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {σ : Type*}

def decrement (e : Expr σ) : Expr σ := e.subst (fun i => .var i - 1)

private theorem add_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (pairAdd p r) (pairAdd q s) := by
  change p.1+q.2=p.2+q.1 at h
  change r.1+s.2=r.2+s.1 at k
  change (p.1+r.1)+(q.2+s.2)=(p.2+r.2)+(q.1+s.1)
  calc
    _=(p.1+q.2)+(r.1+s.2) := by ring
    _=(p.2+q.1)+(r.2+s.1) := by rw [h,k]
    _=_ := by ring

private theorem sub_equiv {p q r s : Pair V} (h : Equivalent p q) (k : Equivalent r s) :
    Equivalent (pairSub p r) (pairSub q s) := by
  apply add_equiv h
  change r.2+s.1=r.1+s.2
  exact k.symm

theorem decrement_shift_equiv (e : Expr σ) (v : σ → V) :
    Equivalent (splitEval (decrement e) (fun i => v i+1)) (splitEval e v) := by
  induction e with
  | constant c => exact equivalent_refl _
  | var i =>
    change Equivalent (splitEval (.sub (.var i) (.constant 1)) (fun i => v i+1)) (splitEval (.var i) v)
    simp [splitEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, add_comm]
  | add p q hp hq =>
    change Equivalent (splitEval (decrement p + decrement q) (fun i => v i+1)) (splitEval (p+q) v)
    rw [splitEval_add,splitEval_add]
    exact add_equiv hp hq
  | sub p q hp hq =>
    change Equivalent (splitEval (decrement p - decrement q) (fun i => v i+1)) (splitEval (p-q) v)
    rw [splitEval_sub,splitEval_sub]
    exact sub_equiv hp hq
  | mul p q hp hq =>
    change Equivalent (splitEval (decrement p * decrement q) (fun i => v i+1)) (splitEval (p*q) v)
    rw [splitEval_mul,splitEval_mul]
    exact equivalent_multiply hp hq

theorem positiveShift_decrement_zero_iff (e : Expr σ) (v : σ → V) :
    InternalZero (positiveShift (decrement e)) v ↔ InternalZero e v := by
  rw [internalZero_positiveShift]
  exact equivalent_zero_iff (decrement_shift_equiv e v)
end DiophantineConsistency.PositiveOffsetArithmetic

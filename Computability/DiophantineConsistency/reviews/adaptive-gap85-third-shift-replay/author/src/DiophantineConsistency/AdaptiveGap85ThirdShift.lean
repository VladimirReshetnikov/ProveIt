import DiophantineConsistency.AdaptiveGap85BalanceContext
set_option autoImplicit false
set_option maxRecDepth 100000
/-! Corrected third shift over commutative rings; no model positivity is asserted. -/
namespace DiophantineConsistency.AdaptiveGap85ThirdShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveGap85Literal AdaptiveGap85BalanceContext
open AdaptiveGap85ShiftContext AdaptiveGap85ShiftFirstInput AdaptiveGap85ShiftMainShift AdaptiveGap85ShiftAuxInput AdaptiveGap85ShiftRankRep
variable {R : Type*} [CommRing R]
def ringEval {σ : Type*} (v : σ → R) : Expr σ → R
  | .constant z => (z : R)
  | .var i => v i
  | .add a b => ringEval v a + ringEval v b
  | .sub a b => ringEval v a - ringEval v b
  | .mul a b => ringEval v a * ringEval v b

@[simp] theorem eval_add {σ : Type*} (v : σ → R) (x y : Expr σ) :
    ringEval v (x+y)=ringEval v x+ringEval v y := rfl
@[simp] theorem eval_sub {σ : Type*} (v : σ → R) (x y : Expr σ) :
    ringEval v (x-y)=ringEval v x-ringEval v y := rfl
@[simp] theorem eval_mul {σ : Type*} (v : σ → R) (x y : Expr σ) :
    ringEval v (x*y)=ringEval v x*ringEval v y := rfl
@[simp] theorem eval_var {σ : Type*} (v : σ → R) (i : σ) : ringEval v (.var i)=v i := rfl
@[simp] theorem eval_constant {σ : Type*} (v : σ → R) (z : ℤ) : ringEval v (.constant z)=(z:R) := rfl
@[simp] theorem eval_one {σ : Type*} (v : σ → R) : ringEval v (1 : Expr σ)=1 := by
  change ((1:ℤ):R)=1
  exact Int.cast_one

theorem ringEval_subst {σ τ : Type*} (e : Expr σ) (f : σ → Expr τ) (v : τ → R) :
    ringEval v (e.subst f)=ringEval (fun x => ringEval v (f x)) e := by
  induction e <;> simp_all [ringEval,Expr.subst]

theorem rank (b F C A d : R) :
  let q := 1+b
  (q-(F-A*d))*q-(C+(b*A-1)*d) = (q-F)*q-C+(A+1)*d := by dsimp; ring
theorem transport (b F C A d : R) :
  let q := 1+b
  (C+(b*A-1)*d)*A-(F-A*d)*q = C*A-F*q+b*A*(A+1)*d := by dsimp; ring
theorem first (b F C A d k r L Y : R) :
  let q := 1+b
  (q*q*q*b)*(L+(r+A*(A+1)*(b*k+1)*d)-k*((C+(b*A-1)*d)*A-(F-A*d)*q))+Y*b-((C+(b*A-1)*d)*A-(F-A*d)*q)*(q*q*q) =
    (q*q*q*b)*(L+r-k*(C*A-F*q))+Y*b-(C*A-F*q)*(q*q*q) := by dsimp; ring
theorem auxiliary (b A U s c T R0 : R) :
  let q := 1+b
  (T+(q*q-1)*(A+1)*U*s)*c - (R0+(A+1)*c*U*s*(q*q-1)) = T*c-R0 := by dsimp; ring
theorem main (b A U s c gamma R0 : R) :
  let q := 1+b
  U*(gamma-(q*q-1)*(A+1)*c*s)+(R0+(A+1)*c*U*s*(q*q-1))=U*gamma+R0 := by dsimp; ring
def shift (p : Fin 4 → ℤ) (v : Fin 13 → R) (s : R) : Fin 13 → R :=
  let b := v 0*(p 0:R)
  let q := 1+b
  let A := v 6+(p 1:R)*q
  let U := v 7*q*q
  let k := v 9+v 10
  let c := v 9+v 7*k
  let d := c*U*s
  ![v 0,v 1-A*d,v 2+(b*A-1)*d,v 3,v 4,
    v 5+(q*q-1)*(A+1)*U*s,v 6,v 7,
    v 8+A*(A+1)*(b*k+1)*d,v 9,v 10,v 11,
    v 12-(q*q-1)*(A+1)*c*s]

set_option maxHeartbeats 12000000 in
theorem first_invariant (p : Fin 4 → ℤ) (v : Fin 13 → R) (s : R) :
    ringEval (shift p v s) (firstInput p)=ringEval v (firstInput p) := by
  simp [firstInput,shift]
  ring

set_option maxHeartbeats 12000000 in
theorem main_invariant (p : Fin 4 → ℤ) (v : Fin 13 → R) (s : R) :
    ringEval (shift p v s) (mainShift p)=ringEval v (mainShift p) := by
  simp [mainShift,rankExpr,shift]
  ring

set_option maxHeartbeats 12000000 in
theorem auxiliary_invariant (p : Fin 4 → ℤ) (v : Fin 13 → R) (s : R) :
    ringEval (shift p v s) (auxiliaryInput p)=ringEval v (auxiliaryInput p) := by
  simp [auxiliaryInput,rankExpr,shift]
  ring

theorem literal_eval_shift (p : Fin 4 → ℤ) (v : Fin 13 → R) (s : R) :
    ringEval (shift p v s) (expressionAt85 p)=ringEval v (expressionAt85 p) := by
  have hfill : (fun i => ringEval (shift p v s) (balanceFill p i)) =
      (fun i => ringEval v (balanceFill p i)) := by
    funext i
    cases i with
    | none => exact first_invariant p v s
    | some i =>
      cases i with
      | none => exact main_invariant p v s
      | some i =>
        cases i with
        | none => exact auxiliary_invariant p v s
        | some i =>
          by_cases hi : i=1 ∨ i=2 ∨ i=5 ∨ i=8 ∨ i=12
          · simp [balanceFill,hi]
          · simp only [balanceFill,hi,ite_false,eval_var]
            fin_cases i <;> simp_all [shift]
  calc
    ringEval (shift p v s) (expressionAt85 p) =
        ringEval (shift p v s) ((AdaptiveGap85ShiftContext.contextAt p).subst (balanceFill p)) := by
          rw [literal_as_balance_context]
    _ = ringEval (fun i => ringEval (shift p v s) (balanceFill p i)) (AdaptiveGap85ShiftContext.contextAt p) := ringEval_subst _ _ _
    _ = ringEval (fun i => ringEval v (balanceFill p i)) (AdaptiveGap85ShiftContext.contextAt p) := by rw [hfill]
    _ = ringEval v ((AdaptiveGap85ShiftContext.contextAt p).subst (balanceFill p)) := (ringEval_subst _ _ _).symm
    _ = ringEval v (expressionAt85 p) := by rw [literal_as_balance_context]
end DiophantineConsistency.AdaptiveGap85ThirdShift

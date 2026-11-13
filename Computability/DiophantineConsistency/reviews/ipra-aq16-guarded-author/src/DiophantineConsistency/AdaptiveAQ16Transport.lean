import DiophantineConsistency.AdaptiveAQ16Maps
import DiophantineConsistency.AdaptiveAQ17Transport
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ16Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveAQ40Transport
open AdaptiveAQ16Maps AdaptiveAQ17Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fill (p : Fin 4 → ℕ) : Fin 17 → Expr (Fin 16) :=
  let q : Expr (Fin 16) := 1 + .var 0 * .constant (p 0)
  let U : Expr (Fin 16) := .var 7 * (q*q)
  let E : Expr (Fin 16) := .var 6 * .var 7
  let k : Expr (Fin 16) := .var 9 + .var 10
  let c : Expr (Fin 16) := .var 9 + .var 7*k
  let a : Expr (Fin 16) := E + .var 7
  let H : Expr (Fin 16) := 3 + 4*a
  let D : Expr (Fin 16) := U*(.var 6+a*c)+H*((U*.var 12+E*q)-((k-.var 13)-1))
  ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7,.var 8,.var 9,.var 10,.var 11,.var 12,.var 13,.var 14,D,.var 15]

theorem extend_inputs (p : Fin 4 → ℕ) (hp : 2 ≤ p 0) (v : Fin 16 → V)
    (hv : ∀ i, 0 < v i) :
    ∀ i, Equivalent (splitEval (.var i) (extend p v)) (splitEval (fill p i) v) := by
  have hpos := parts_pos p hp v hv
  have hcancel : positivePart p v = negativePart p v + (positivePart p v - negativePart p v) := by
    rw [add_comm,tsub_add_cancel_of_le (le_of_lt hpos)]
  intro i
  fin_cases i <;> try exact equivalent_refl _
  simp [extend,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub]
  dsimp [positivePart,negativePart] at hcancel ⊢
  simp only [HSub.hSub,Sub.sub] at hcancel
  ring_nf at hcancel ⊢
  exact hcancel.symm

theorem project_inputs (p : Fin 4 → ℕ) (v : Fin 17 → V)
    (hz : InternalZero (AdaptiveAQ17Literal.literal (fun j => (p j : ℤ))) v) :
    ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) (project v)) := by
  have hall := (AdaptiveAQ17Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  have hd := hall 6
  simp [InternalZero,AdaptiveAQ17Zeros.residuals,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at hd
  intro i
  fin_cases i <;> try exact equivalent_refl _
  simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hd

theorem residual_equiv (p : Fin 4 → ℕ) (v : Fin 17 → V) (w : Fin 16 → V)
    (hinputs : ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) w)) (i : Fin 8) :
    InternalZero (AdaptiveAQ17Zeros.residuals (fun j => (p j : ℤ)) i) v ↔
    InternalZero ((AdaptiveAQ17Zeros.residuals (fun j => (p j : ℤ)) i).subst (fill p)) w := by
  have h := subst_equiv_hetero (AdaptiveAQ17Zeros.residuals (fun j => (p j : ℤ)) i) (fun i => .var i) (fill p) v w hinputs
  simpa only [DiophantineConsistency.AdaptiveAQ30Transport.subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem extend_zero (p : Fin 4 → ℕ) (hp : 2 ≤ p 0) (v : Fin 16 → V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (AdaptiveAQ16Literal.literal (fun j => (p j : ℤ))) v) :
    InternalZero (AdaptiveAQ17Literal.literal (fun j => (p j : ℤ))) (extend p v) := by
  have hall := (AdaptiveAQ16Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  apply (AdaptiveAQ17Zeros.sum_zero (fun j => (p j : ℤ)) (extend p v)).mpr
  intro i
  apply (residual_equiv p (extend p v) v (extend_inputs p hp v hv) i).mpr
  fin_cases i
  all_goals first
    | exact hall 0 | exact hall 1 | exact hall 2 | exact hall 3
    | exact hall 4 | exact hall 5 | exact hall 6
    | (simp only [InternalZero]; exact add_comm _ _)

theorem project_zero (p : Fin 4 → ℕ) (v : Fin 17 → V)
    (hz : InternalZero (AdaptiveAQ17Literal.literal (fun j => (p j : ℤ))) v) :
    InternalZero (AdaptiveAQ16Literal.literal (fun j => (p j : ℤ))) (project v) := by
  have hall := (AdaptiveAQ17Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  apply (AdaptiveAQ16Zeros.sum_zero (fun j => (p j : ℤ)) (project v)).mpr
  intro i
  fin_cases i
  all_goals first
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 0).mp (hall 0)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 1).mp (hall 1)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 2).mp (hall 2)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 3).mp (hall 3)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 4).mp (hall 4)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 5).mp (hall 5)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 7).mp (hall 7)
#print axioms extend_inputs
#print axioms project_inputs
#print axioms extend_zero
#print axioms project_zero
end DiophantineConsistency.AdaptiveAQ16Transport

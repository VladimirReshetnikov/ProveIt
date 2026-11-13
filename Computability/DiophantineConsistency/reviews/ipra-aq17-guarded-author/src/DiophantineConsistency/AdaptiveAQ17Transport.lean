import DiophantineConsistency.AdaptiveAQ17Maps
import DiophantineConsistency.AdaptiveAQ22Transport
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ17Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveAQ40Transport
open AdaptiveAQ17Maps AdaptiveAQ22Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fill (p : Fin 4 → ℕ) : Fin 22 → Expr (Fin 17) :=
  let qm : Expr (Fin 17) := .var 0 * .constant (p 0)
  let q : Expr (Fin 17) := 1 + qm
  let e : Expr (Fin 17) := .var 6 * .var 7
  let ky : Expr (Fin 17) := .var 7 * (.var 9 + .var 10)
  let c : Expr (Fin 17) := .var 9 + ky
  let a : Expr (Fin 17) := e + .var 7
  ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7,.var 8,.var 9,.var 10,.var 11,.var 12,
    (q*(q*q))*qm,.var 7*(q*q),.var 13,e*ky,c*c,.var 14,.var 15,.var 16,3+4*a+a*a]

theorem extend_inputs (p : Fin 4 → ℕ) (v : Fin 17 → V) :
    ∀ i, Equivalent (splitEval (.var i) (extend p v)) (splitEval (fill p i) v) := by
  intro i
  fin_cases i <;> try exact equivalent_refl _
  all_goals simp [extend,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub]

theorem project_inputs (p : Fin 4 → ℕ) (v : Fin 22 → V)
    (hz : InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j : ℤ))) v) :
    ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) (project v)) := by
  have hall := (AdaptiveAQ22Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  have hs := hall 4
  have hm := hall 5
  have he := hall 7
  have hc := hall 8
  have hd := hall 12
  simp [InternalZero,AdaptiveAQ22Zeros.residuals,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at hs hm he hc hd
  intro i
  fin_cases i <;> try exact equivalent_refl _
  all_goals first
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hs
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hm
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using he
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hc
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hd

theorem residual_equiv (p : Fin 4 → ℕ) (v : Fin 22 → V) (w : Fin 17 → V)
    (hinputs : ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) w)) (i : Fin 13) :
    InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) i) v ↔
    InternalZero ((AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) i).subst (fill p)) w := by
  have h := subst_equiv_hetero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) i) (fun i => .var i) (fill p) v w hinputs
  simpa only [DiophantineConsistency.AdaptiveAQ30Transport.subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem extend_zero (p : Fin 4 → ℕ) (v : Fin 17 → V)
    (hz : InternalZero (AdaptiveAQ17Literal.literal (fun j => (p j : ℤ))) v) :
    InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j : ℤ))) (extend p v) := by
  have hall := (AdaptiveAQ17Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  apply (AdaptiveAQ22Zeros.sum_zero (fun j => (p j : ℤ)) (extend p v)).mpr
  intro i
  apply (residual_equiv p (extend p v) v (extend_inputs p v) i).mpr
  fin_cases i
  all_goals first
    | exact hall 0 | exact hall 1 | exact hall 2 | exact hall 3
    | exact hall 4 | exact hall 5 | exact hall 6 | exact hall 7
    | (simp only [InternalZero]; exact add_comm _ _)

theorem project_zero (p : Fin 4 → ℕ) (v : Fin 22 → V)
    (hz : InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j : ℤ))) v) :
    InternalZero (AdaptiveAQ17Literal.literal (fun j => (p j : ℤ))) (project v) := by
  have hall := (AdaptiveAQ22Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  apply (AdaptiveAQ17Zeros.sum_zero (fun j => (p j : ℤ)) (project v)).mpr
  intro i
  fin_cases i
  all_goals first
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 0).mp (hall 0)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 1).mp (hall 1)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 2).mp (hall 2)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 3).mp (hall 3)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 6).mp (hall 6)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 9).mp (hall 9)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 10).mp (hall 10)
    | exact (residual_equiv p v (project v) (project_inputs p v hz) 11).mp (hall 11)
#print axioms extend_inputs
#print axioms project_inputs
#print axioms extend_zero
#print axioms project_zero
end DiophantineConsistency.AdaptiveAQ17Transport

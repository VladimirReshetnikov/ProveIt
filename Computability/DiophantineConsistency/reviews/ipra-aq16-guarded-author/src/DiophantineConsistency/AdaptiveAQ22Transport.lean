import DiophantineConsistency.AdaptiveAQ22Maps
import DiophantineConsistency.AdaptiveAQ26Transport
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ22Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveAQ40Transport
open AdaptiveAQ22Maps AdaptiveAQ26Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def fill (p : Fin 4 → ℕ) : Fin 26 → Expr (Fin 22) :=
  let q : Expr (Fin 22) := 1 + .var 0 * .constant (p 0)
  ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7,.var 8,.var 9,.var 10,.var 11,.var 12,.var 13,.var 14,.var 15,.var 9 + .var 7 * (.var 9 + .var 10),.var 16,.var 17,.var 18,.var 19,.var 20,.var 21,q*q,.var 6*.var 7,.var 21 * (.var 3*.var 3 - 1)]

theorem extend_inputs (p : Fin 4 → ℕ) (v : Fin 22 → V)
    (hz : InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j : ℤ))) v) :
    ∀ i, Equivalent (splitEval (.var i) (extend p v)) (splitEval (fill p i) v) := by
  have hall := (AdaptiveAQ22Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  have hq := hall 3
  change InternalZero ((.var 17 * .var 4) * (.var 17 * .var 4) - .var 21 * (.var 3 * .var 3 - 1)) v at hq
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at hq
  intro i
  fin_cases i <;> try exact equivalent_refl _
  all_goals try simp [extend,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub]
  all_goals simpa [extend,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hq

theorem project_inputs (p : Fin 4 → ℕ) (v : Fin 26 → V)
    (hz : InternalZero (AdaptiveAQ26Literal.literal (fun j => (p j : ℤ))) v) :
    ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) (project v)) := by
  have hall := (AdaptiveAQ26Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  have hc := hall 7
  change InternalZero (.var 16 - (.var 9 + .var 7 * (.var 9 + .var 10))) v at hc
  have hq := hall 14
  change InternalZero (.var 23 - ((1 + .var 0 * .constant ((p 0 : ℕ) : ℤ)) * (1 + .var 0 * .constant ((p 0 : ℕ) : ℤ)))) v at hq
  have he := hall 15
  change InternalZero (.var 24 - .var 6 * .var 7) v at he
  have hs := hall 16
  change InternalZero (.var 25 - .var 22 * (.var 3 * .var 3 - 1)) v at hs
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at hc hq he hs
  intro i
  fin_cases i <;> try exact equivalent_refl _
  all_goals first
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hc
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hq
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using he
    | simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,HSub.hSub,Sub.sub] using hs

theorem residual_equiv (p : Fin 4 → ℕ) (v : Fin 26 → V) (w : Fin 22 → V)
    (hinputs : ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill p i) w)) (i : Fin 17) :
    InternalZero (AdaptiveAQ26Zeros.residuals (fun j => (p j : ℤ)) i) v ↔
    InternalZero ((AdaptiveAQ26Zeros.residuals (fun j => (p j : ℤ)) i).subst (fill p)) w := by
  have h := subst_equiv_hetero (AdaptiveAQ26Zeros.residuals (fun j => (p j : ℤ)) i) (fun i => .var i) (fill p) v w hinputs
  simpa only [DiophantineConsistency.AdaptiveAQ30Transport.subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem extend_zero (p : Fin 4 → ℕ) (v : Fin 22 → V)
    (hz : InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j : ℤ))) v) :
    InternalZero (AdaptiveAQ26Literal.literal (fun j => (p j : ℤ))) (extend p v) := by
  have hall := (AdaptiveAQ22Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  apply (AdaptiveAQ26Zeros.sum_zero (fun j => (p j : ℤ)) (extend p v)).mpr
  intro i
  apply (residual_equiv p (extend p v) v (extend_inputs p v hz) i).mpr
  fin_cases i
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 0) v
    exact hall 0
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 1) v
    exact hall 1
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 2) v
    exact hall 2
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 3) v
    exact hall 3
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 4) v
    exact hall 4
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 5) v
    exact hall 5
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 6) v
    exact hall 6
  · change InternalZero ((.var 9 + .var 7 * (.var 9 + .var 10)) - (.var 9 + .var 7 * (.var 9 + .var 10))) v
    simp only [InternalZero]
    exact add_comm _ _
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 7) v
    exact hall 7
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 8) v
    exact hall 8
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 9) v
    exact hall 9
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 10) v
    exact hall 10
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 11) v
    exact hall 11
  · change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 12) v
    exact hall 12
  · change InternalZero (((1 + .var 0 * .constant ((p 0 : ℕ) : ℤ)) * (1 + .var 0 * .constant ((p 0 : ℕ) : ℤ))) - ((1 + .var 0 * .constant ((p 0 : ℕ) : ℤ)) * (1 + .var 0 * .constant ((p 0 : ℕ) : ℤ)))) v
    simp only [InternalZero]
    exact add_comm _ _
  · change InternalZero ((.var 6 * .var 7) - (.var 6 * .var 7)) v
    simp only [InternalZero]
    exact add_comm _ _
  · change InternalZero ((.var 21 * (.var 3 * .var 3 - 1)) - (.var 21 * (.var 3 * .var 3 - 1))) v
    simp only [InternalZero]
    exact add_comm _ _

theorem project_zero (p : Fin 4 → ℕ) (v : Fin 26 → V)
    (hz : InternalZero (AdaptiveAQ26Literal.literal (fun j => (p j : ℤ))) v) :
    InternalZero (AdaptiveAQ22Literal.literal (fun j => (p j : ℤ))) (project v) := by
  have hall := (AdaptiveAQ26Zeros.sum_zero (fun j => (p j : ℤ)) v).mp hz
  apply (AdaptiveAQ22Zeros.sum_zero (fun j => (p j : ℤ)) (project v)).mpr
  intro i
  fin_cases i
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 0).mp (hall 0)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 0) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 1).mp (hall 1)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 1) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 2).mp (hall 2)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 2) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 3).mp (hall 3)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 3) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 4).mp (hall 4)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 4) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 5).mp (hall 5)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 5) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 6).mp (hall 6)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 6) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 8).mp (hall 8)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 7) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 9).mp (hall 9)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 8) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 10).mp (hall 10)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 9) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 11).mp (hall 11)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 10) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 12).mp (hall 12)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 11) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 13).mp (hall 13)
    change InternalZero (AdaptiveAQ22Zeros.residuals (fun j => (p j : ℤ)) 12) (project v) at h
    exact h
#print axioms extend_inputs
#print axioms project_inputs
#print axioms extend_zero
#print axioms project_zero
end DiophantineConsistency.AdaptiveAQ22Transport

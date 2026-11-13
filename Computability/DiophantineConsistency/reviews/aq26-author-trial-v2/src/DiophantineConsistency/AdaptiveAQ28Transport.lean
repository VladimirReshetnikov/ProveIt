import DiophantineConsistency.AdaptiveAQ28Maps
import DiophantineConsistency.AdaptiveAQ29Transport
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ28Transport
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveAQ40Transport
open AdaptiveAQ28Maps AdaptiveAQ29Transport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def fill : Fin 29 → Expr (Fin 28) := ![.var 0,.var 1,.var 2,.var 3,.var 4,.var 5,.var 6,.var 7,.var 8,.var 9,.var 10,.var 11,.var 12,.var 13,.var 14,.var 15,.var 16,.var 17,.var 18,.var 19,.var 20,.var 21,.var 22,.var 23,.var 24,.var 25,.var 14 * .var 14,.var 26,.var 27]
theorem extend_inputs (v : Fin 28 → V) :
    ∀ i, Equivalent (splitEval (.var i) (extend v)) (splitEval (fill i) v) := by
  intro i
  fin_cases i <;> try exact equivalent_refl _
  simp [extend,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent]

theorem project_inputs (p : Fin 4 → ℤ) (v : Fin 29 → V)
    (hz : InternalZero (AdaptiveAQ29Literal.literal p) v) :
    ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill i) (project v)) := by
  have hall := (AdaptiveAQ29Zeros.sum_zero p v).mp hz
  have h9 := hall 17
  change InternalZero (.var 26 - (.var 14 * .var 14)) v at h9
  simp [InternalZero,Expr.splitNatural,NatExpr.evalSemiring,HSub.hSub,Sub.sub] at h9
  intro i
  fin_cases i <;> try exact equivalent_refl _
  simpa [project,fill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent] using h9
#print axioms extend_inputs
#print axioms project_inputs
theorem residual_equiv (p : Fin 4 → ℤ) (v : Fin 29 → V) (w : Fin 28 → V)
    (hinputs : ∀ i, Equivalent (splitEval (.var i) v) (splitEval (fill i) w)) (i : Fin 20) :
    InternalZero (AdaptiveAQ29Zeros.residuals p i) v ↔
    InternalZero ((AdaptiveAQ29Zeros.residuals p i).subst fill) w := by
  have h := subst_equiv_hetero (AdaptiveAQ29Zeros.residuals p i) (fun i => .var i) fill v w hinputs
  simpa only [DiophantineConsistency.AdaptiveAQ30Transport.subst_id,InternalZero,splitEval] using equivalent_zero_iff h

theorem extend_zero (p : Fin 4 → ℤ) (v : Fin 28 → V)
    (hz : InternalZero (AdaptiveAQ28Literal.literal p) v) :
    InternalZero (AdaptiveAQ29Literal.literal p) (extend v) := by
  have hall := (AdaptiveAQ28Zeros.sum_zero p v).mp hz
  apply (AdaptiveAQ29Zeros.sum_zero p (extend v)).mpr
  intro i
  apply (residual_equiv p (extend v) v (extend_inputs v) i).mpr
  fin_cases i
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 0) v
    exact hall 0
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 1) v
    exact hall 1
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 2) v
    exact hall 2
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 3) v
    exact hall 3
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 4) v
    exact hall 4
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 5) v
    exact hall 5
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 6) v
    exact hall 6
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 7) v
    exact hall 7
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 8) v
    exact hall 8
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 9) v
    exact hall 9
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 10) v
    exact hall 10
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 11) v
    exact hall 11
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 12) v
    exact hall 12
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 13) v
    exact hall 13
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 14) v
    exact hall 14
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 15) v
    exact hall 15
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 16) v
    exact hall 16
  · change InternalZero ((.var 14 * .var 14) - (.var 14 * .var 14)) v
    simp only [InternalZero]
    exact add_comm _ _
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 17) v
    exact hall 17
  · change InternalZero (AdaptiveAQ28Zeros.residuals p 18) v
    exact hall 18

theorem project_zero (p : Fin 4 → ℤ) (v : Fin 29 → V)
    (hz : InternalZero (AdaptiveAQ29Literal.literal p) v) :
    InternalZero (AdaptiveAQ28Literal.literal p) (project v) := by
  have hall := (AdaptiveAQ29Zeros.sum_zero p v).mp hz
  apply (AdaptiveAQ28Zeros.sum_zero p (project v)).mpr
  intro i
  fin_cases i
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 0).mp (hall 0)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 0) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 1).mp (hall 1)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 1) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 2).mp (hall 2)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 2) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 3).mp (hall 3)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 3) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 4).mp (hall 4)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 4) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 5).mp (hall 5)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 5) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 6).mp (hall 6)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 6) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 7).mp (hall 7)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 7) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 8).mp (hall 8)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 8) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 9).mp (hall 9)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 9) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 10).mp (hall 10)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 10) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 11).mp (hall 11)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 11) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 12).mp (hall 12)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 12) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 13).mp (hall 13)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 13) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 14).mp (hall 14)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 14) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 15).mp (hall 15)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 15) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 16).mp (hall 16)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 16) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 18).mp (hall 18)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 17) (project v) at h
    exact h
  · have h := (residual_equiv p v (project v) (project_inputs p v hz) 19).mp (hall 19)
    change InternalZero (AdaptiveAQ28Zeros.residuals p 18) (project v) at h
    exact h
#print axioms extend_zero
#print axioms project_zero
end DiophantineConsistency.AdaptiveAQ28Transport

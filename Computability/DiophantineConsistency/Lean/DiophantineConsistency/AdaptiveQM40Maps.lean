import DiophantineConsistency.AdaptiveQM40Zeros
import DiophantineConsistency.AdaptiveZ46Rest
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace DiophantineConsistency.AdaptiveQM40Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveZ46Rest AdaptiveQM40Context AdaptiveQM40Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 41 → V) (t : V) (i : Fin 40) : V :=
 if i.val = 24 then t else if h : i.val < 30 then v ⟨i.val,by omega⟩ else v ⟨i.val+1,by omega⟩
def extend (v : Fin 40 → V) (i : Fin 41) : V :=
 if i.val = 24 then v 15*v 24 else if i.val = 30 then v 15*v 15
 else if h : i.val < 30 then v ⟨i.val,by omega⟩ else v ⟨i.val-1,by omega⟩

theorem project_rest (v : Fin 41 → V) (t : V) (i : Fin 39) :
    project v t (newRest i) = v (oldRest i) := by fin_cases i <;> rfl

theorem extend_rest (v : Fin 40 → V) (i : Fin 39) :
    extend v (oldRest i) = v (newRest i) := by fin_cases i <;> rfl

theorem project_pos (v : Fin 41 → V) (t : V) (hv : ∀ i, 0<v i) (ht : 0<t) :
    ∀ i,0<project v t i := by
  intro i
  unfold project
  split
  · exact ht
  · split <;> exact hv _

theorem extend_pos (v : Fin 40 → V) (hv : ∀ i, 0<v i) : ∀ i,0<extend v i := by
  intro i
  unfold extend
  split
  · exact mul_pos (hv 15) (hv 24)
  · split
    · exact mul_pos (hv 15) (hv 15)
    · split <;> exact hv _

theorem project_inputs (v : Fin 41 → V) (t : V) (h : v 24=v 15*t) :
    ∀ i, Equivalent (splitEval (oldFill i) v) (splitEval (newFill i) (project v t)) := by
  intro i
  cases i with
  | inl i =>
    fin_cases i
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,project,h]
  | inr i =>
    change Equivalent (natural (v (oldRest i))) (natural (project v t (newRest i)))
    rw [project_rest]
    exact equivalent_refl _

theorem extend_inputs (v : Fin 40 → V) :
    ∀ i, Equivalent (splitEval (oldFill i) (extend v)) (splitEval (newFill i) v) := by
  intro i
  cases i with
  | inl i =>
    fin_cases i
    simp [oldFill,newFill,splitEval,Expr.splitNatural,NatExpr.evalSemiring,Equivalent,extend]
  | inr i =>
    change Equivalent (natural (extend v (oldRest i))) (natural (v (newRest i)))
    rw [extend_rest]
    exact equivalent_refl _

theorem project_common (p : Fin 4 → ℤ) (v : Fin 41 → V) (t : V) (h : v 24=v 15*t) (i : Fin 30) :
    InternalZero (AdaptiveQF41Context.residuals p (oldIndex i)) v ↔
      InternalZero (residuals p (newIndex i)) (project v t) := by
  have he := subst_equiv_hetero (common p i) oldFill newFill v (project v t) (project_inputs v t h)
  rw [common_old,common_new] at he
  exact equivalent_zero_iff he

theorem extend_common (p : Fin 4 → ℤ) (v : Fin 40 → V) (i : Fin 30) :
    InternalZero (AdaptiveQF41Context.residuals p (oldIndex i)) (extend v) ↔
      InternalZero (residuals p (newIndex i)) v := by
  have he := subst_equiv_hetero (common p i) oldFill newFill (extend v) v (extend_inputs v)
  rw [common_old,common_new] at he
  exact equivalent_zero_iff he
#print axioms project_common
#print axioms extend_common
end DiophantineConsistency.AdaptiveQM40Maps

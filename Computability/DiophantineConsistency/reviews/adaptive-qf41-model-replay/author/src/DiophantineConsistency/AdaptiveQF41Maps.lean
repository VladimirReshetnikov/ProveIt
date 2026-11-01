import DiophantineConsistency.AdaptiveQF41Zeros
import DiophantineConsistency.AdaptiveZ46Rest
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section
namespace DiophantineConsistency.AdaptiveQF41Maps
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveZ46Rest AdaptiveQF41Context AdaptiveQF41Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def project (v : Fin 42 → V) (t : V) (i : Fin 41) : V :=
 if i.val = 23 then t else if h : i.val < 29 then v ⟨i.val,by omega⟩ else v ⟨i.val+1,by omega⟩
def extend (v : Fin 41 → V) (i : Fin 42) : V :=
 if i.val = 23 then v 14*v 23 else if i.val = 29 then v 14*v 14
 else if h : i.val < 29 then v ⟨i.val,by omega⟩ else v ⟨i.val-1,by omega⟩

theorem project_rest (v : Fin 42 → V) (t : V) (i : Fin 40) :
    project v t (newRest i) = v (oldRest i) := by fin_cases i <;> rfl

theorem extend_rest (v : Fin 41 → V) (i : Fin 40) :
    extend v (oldRest i) = v (newRest i) := by fin_cases i <;> rfl

theorem project_pos (v : Fin 42 → V) (t : V) (hv : ∀ i, 0<v i) (ht : 0<t) :
    ∀ i,0<project v t i := by
  intro i
  unfold project
  split
  · exact ht
  · split <;> exact hv _

theorem extend_pos (v : Fin 41 → V) (hv : ∀ i, 0<v i) : ∀ i,0<extend v i := by
  intro i
  unfold extend
  split
  · exact mul_pos (hv 14) (hv 23)
  · split
    · exact mul_pos (hv 14) (hv 14)
    · split <;> exact hv _

theorem project_inputs (v : Fin 42 → V) (t : V) (h : v 23=v 14*t) :
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

theorem extend_inputs (v : Fin 41 → V) :
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

theorem project_common (p : Fin 4 → ℤ) (v : Fin 42 → V) (t : V) (h : v 23=v 14*t) (i : Fin 31) :
    InternalZero ((AdaptiveQV42Context.residuals p (oldIndex i)).subst AdaptiveQV42Context.newFill) v ↔
      InternalZero (residuals p (newIndex i)) (project v t) := by
  have he := subst_equiv_hetero (common p i) oldFill newFill v (project v t) (project_inputs v t h)
  rw [common_old,common_new] at he
  exact equivalent_zero_iff he

theorem extend_common (p : Fin 4 → ℤ) (v : Fin 41 → V) (i : Fin 31) :
    InternalZero ((AdaptiveQV42Context.residuals p (oldIndex i)).subst AdaptiveQV42Context.newFill) (extend v) ↔
      InternalZero (residuals p (newIndex i)) v := by
  have he := subst_equiv_hetero (common p i) oldFill newFill (extend v) v (extend_inputs v)
  rw [common_old,common_new] at he
  exact equivalent_zero_iff he
#print axioms project_common
#print axioms extend_common
end DiophantineConsistency.AdaptiveQF41Maps

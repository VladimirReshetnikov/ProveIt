import DiophantineConsistency.ModelArithmetic
import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.QuarticSemiring
import DiophantineConsistency.QuarticSyntaxCore

/-! Every IΣ₁ model satisfies the exact zero-set correspondence for the literal
quartic gate syntax. Concrete circuit selection, positive-coordinate encoding,
and native proof transfer are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.NineLightQuartic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open QuarticCompiler QuarticSyntax AdaptiveEquationSyntax2011 ModelDifferenceRing ModelArithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def squareSum {σ : Type*} : List (Expr σ) → Expr σ
  | [] => 0
  | e :: es => e * e + squareSum es

private theorem squareSum_nonneg {σ : Type*} (es : List (Expr σ)) (v : σ → V) :
    0 ≤ (squareSum es).evalRing (fun i => ι (v i)) := by
  induction es with
  | nil => simp [squareSum, Expr.evalRing_ofNat]
  | cons e es ih =>
    simp only [squareSum, Expr.evalRing_add, Expr.evalRing_mul]
    exact add_nonneg (mul_self_nonneg _) ih

private theorem squareSum_zero_iff {σ : Type*} (es : List (Expr σ)) (v : σ → V) :
    InternalZero (squareSum es) v ↔ ∀ e ∈ es, InternalZero e v := by
  induction es with
  | nil => simp [squareSum, internalZero_iff, Expr.evalRing_ofNat]
  | cons e es ih =>
    rw [internalZero_iff]
    simp only [squareSum, Expr.evalRing_add, Expr.evalRing_mul]
    rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (squareSum_nonneg es v), mul_self_eq_zero]
    rw [← internalZero_iff, ← internalZero_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

private theorem square_syntax {σ : Type*} (es : List (Expr σ)) :
    squareSum es = sumExpressions (es.map fun e => e * e) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [squareSum, List.map_cons, sumExpressions, ih]

private def residualList {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    List (Expr (Option (Witness p q))) :=
  List.ofFn (fun i => residualSyntax p q ((equationIndex p q).symm i))

theorem expression_eq {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    expression p q = (squareSum (residualList p q)).rename (coordinate p q) := by
  rw [square_syntax]
  simp only [QuarticSyntax.expression, residualList, List.map_ofFn, Function.comp_def]

theorem zero_iff_residuals {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m))
    (v : Fin (witnessCount p q + 1) → V) :
    InternalZero (expression p q) v ↔
      ∀ i, (residualSyntax p q i).SemiringZero (v ∘ coordinate p q) := by
  rw [expression_eq]
  change ((squareSum (residualList p q)).rename (coordinate p q)).SemiringZero v ↔ _
  rw [Expr.semiringZero_rename]
  change InternalZero (squareSum (residualList p q)) (v ∘ coordinate p q) ↔ _
  rw [squareSum_zero_iff]
  simp only [residualList, List.mem_ofFn, forall_exists_index]
  constructor
  · intro h i
    exact h _ ((equationIndex p q) i) (by simp)
  · intro h _ i hi
    subst_vars
    exact h _

theorem exists_quartic_iff {m : ℕ} (p q : NatExpr (Empty ⊕ Fin m)) :
    (∃ v : Fin (witnessCount p q + 1) → V, InternalZero (expression p q) v) ↔
    ∃ v : Fin m → V, p.evalSemiring (Sum.elim Empty.elim v) =
      q.evalSemiring (Sum.elim Empty.elim v) := by
  constructor
  · rintro ⟨v,hv⟩
    have h := (zero_iff_residuals p q v).mp hv
    let x := v (coordinate p q none)
    let w : Witness p q → V := fun i => v (coordinate p q (some i))
    have heq : v ∘ coordinate p q = semiringAssignment x w := by
      funext i; cases i <;> rfl
    rw [heq] at h
    exact (exists_residuals_iff p q x).mp ⟨w,h⟩
  · intro h
    obtain ⟨w,hw⟩ := (exists_residuals_iff p q (0 : V)).mpr h
    refine ⟨fun i => semiringAssignment (0 : V) w ((coordinate p q).symm i), ?_⟩
    apply (zero_iff_residuals p q _).mpr
    simpa only [Function.comp_def, Equiv.symm_apply_apply] using hw

#print axioms exists_quartic_iff
end DiophantineConsistency.NineLightQuartic

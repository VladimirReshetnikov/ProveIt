import DiophantineConsistency.InternalResidualSquares
import DiophantineConsistency.QuarticSemiring
import DiophantineConsistency.QuarticSyntaxCore

/-! Every IΣ₁ model satisfies the exact zero-set correspondence for the literal
quartic gate syntax. Concrete circuit selection, positive-coordinate encoding,
and native proof transfer are separate obligations. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.IPRAQuarticModelBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open QuarticCompiler QuarticSyntax InternalResidualSquares AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

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
end DiophantineConsistency.IPRAQuarticModelBridge

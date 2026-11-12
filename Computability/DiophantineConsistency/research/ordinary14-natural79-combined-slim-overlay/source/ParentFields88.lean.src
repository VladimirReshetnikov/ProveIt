import Guard88
import Ring88ToParent

/-! Source-only 88 own-zero to projected parent nonfirst fields. No parent
first-root construction, Lean elaboration or endpoint is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ParentFields88Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft Guard88Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The three nonfirst 88 residuals vanish from its own zero. -/
theorem fields_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    eval (P88QuotientGuarded.graph p).A1 v=0 ∧
    eval (P88QuotientGuarded.graph p).aux v-1=0 ∧
    eval (P88QuotientGuarded.graph p).gap v=0 := by
  rw [internalZero_iff,P88QuotientGuarded.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,Expr.evalRing_var,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P88QuotientGuarded.graph p).A0 v)
      (eval (P88QuotientGuarded.graph p).A1 v) (eval (P88QuotientGuarded.graph p).aux v-1)
      (eval (P88QuotientGuarded.graph p).gap v)
      (eval (P88QuotientGuarded.graph p).Bt v-eval (P88QuotientGuarded.graph p).b v*ι (v 13))=0 := by
    simpa only [fiveSquares,eval] using hz
  have h := (fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive
  exact ⟨h.2.1,h.2.2.1,h.2.2.2.1⟩

/-- For any chosen parent root, the projected parent nonfirst residuals
vanish; the first residual is deliberately not asserted. -/
theorem projected_fields (p : Fin 4 → ℤ) (v : Fin 14 → V) (r : DiffRing V)
    (hz : InternalZero (P88QuotientGuarded.graph p).output v) :
    let w := Ring88ToParentDraft.project (fun j => ι (v j)) r
    (P88FourSquare.graph p).A1.evalRing w=0 ∧
    (P88FourSquare.graph p).aux.evalRing w-1=0 ∧
    (P88FourSquare.graph p).gap.evalRing w=0 := by
  have hf := fields_of_zero p v hz
  refine ⟨?_,?_,?_⟩
  · rw [Ring88ToParentDraft.main_eval]; exact hf.1
  · rw [Ring88ToParentDraft.aux_eval]; exact hf.2.1
  · rw [Ring88ToParentDraft.strong_eval]; exact hf.2.2

end DiophantineConsistency.ParentFields88Draft

#print axioms DiophantineConsistency.ParentFields88Draft.projected_fields

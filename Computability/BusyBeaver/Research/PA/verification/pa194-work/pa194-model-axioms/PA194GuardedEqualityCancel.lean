import PA194UniqueVariableOpen
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

/-- The equality-cancellation sequent follows from symmetry and transitivity sequents. -/
theorem guarded_equality_cancel_of_symm_trans
    (hs : ∀ y z : V, GDerivable T
      (insert (neg SourceL (tr (peq (^&y) (^&z)))) ({tr (peq (^&z) (^&y))} : V)))
    (ht : ∀ x y z : V, GDerivable T
      (insert (neg SourceL (tr (peq (^&x) (^&z))))
        (insert (neg SourceL (tr (peq (^&z) (^&y)))) ({tr (peq (^&x) (^&y))} : V)))) :
    ∀ x y z : V, GDerivable T
      (insert (neg SourceL (tr (peq (^&x) (^&z))))
        (insert (neg SourceL (tr (peq (^&y) (^&z)))) ({tr (peq (^&x) (^&y))} : V))) := by
  intro x y z
  let A : V := tr (peq (^&x) (^&z))
  let B : V := tr (peq (^&y) (^&z))
  let C : V := tr (peq (^&x) (^&y))
  let D : V := tr (peq (^&z) (^&y))
  have hA : IsFormula SourceL A := tr_valid (peq_valid (by simp) (by simp))
  have hB : IsFormula SourceL B := tr_valid (peq_valid (by simp) (by simp))
  have hC : IsFormula SourceL C := tr_valid (peq_valid (by simp) (by simp))
  have hD : IsFormula SourceL D := tr_valid (peq_valid (by simp) (by simp))
  let Δ : V := insert (neg SourceL A) (insert (neg SourceL B) ({C} : V))
  have hΔ : IsFormulaSet SourceL Δ := fs_cons (IsSemiformula.neg_iff.mpr hA)
    (fs_cons (IsSemiformula.neg_iff.mpr hB) (by rw [singleton_eq_insert]; exact fs_cons hC fs_nil))
  change GDerivable T Δ
  apply GDerivable.cut_wk hΔ hD (hs y z) (ht x y z)
  · dsimp [Δ, A, B, C, D]; set_tac
  · dsimp [Δ, A, B, C, D]; set_tac

/-- The variable-name uniqueness field follows from pointwise symmetry and transitivity. -/
theorem guarded_uVar_of_symm_trans
    (hs : ∀ y z : V, GDerivable T
      (insert (neg SourceL (tr (peq (^&y) (^&z)))) ({tr (peq (^&z) (^&y))} : V)))
    (ht : ∀ x y z : V, GDerivable T
      (insert (neg SourceL (tr (peq (^&x) (^&z))))
        (insert (neg SourceL (tr (peq (^&z) (^&y)))) ({tr (peq (^&x) (^&y))} : V)))) :
    ∀ i : V, GDerivable T ({tr (uniq (^&i))} : V) :=
  guarded_uVar_of_equality_cancellation (guarded_equality_cancel_of_symm_trans hs ht)

#print axioms guarded_uVar_of_symm_trans
#print axioms guarded_equality_cancel_of_symm_trans
end generic
end PA194GuardedCompiler

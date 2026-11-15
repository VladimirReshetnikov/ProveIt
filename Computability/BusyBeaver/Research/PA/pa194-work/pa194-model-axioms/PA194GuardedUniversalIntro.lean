import PA194TermNames
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

/-- Introduce an arithmetic universal from a guarded proof of its eigenvariable opening. -/
theorem guarded_tr_all_intro {p : V} (hp : IsSemiformula PA194PAeq.language 1 p)
    (h : GDerivable T ({tr (free PA194PAeq.language p)} : V)) :
    GDerivable T ({tr (^∀ p)} : V) := by
  have hq : IsFormula SourceL (tr (^∀ p)) := tr_valid (IsSemiformula.all.mpr (by simpa using hp))
  have hf : IsFormula SourceL (free SourceL (trBody p)) := (trBody_valid hp).free
  have hs : IsFormulaSet SourceL ({tr (^∀ p)} : V) := by rw [singleton_eq_insert]; exact fs_cons hq fs_nil
  have hprem : GDerivable T (insert (free SourceL (trBody p)) (setShift SourceL ({tr (^∀ p)} : V))) := by
    apply GDerivable.wk (fs_cons hf hs.setShift) _ h
    rw [tr_free hp]
    intro x hx
    exact mem_bitInsert_iff.mpr (Or.inl (by simpa using hx))
  have hout := GDerivable.all_rel (trBody_valid hp) (Δ := ({tr (^∀ p)} : V)) (by rw [← tr_all hp]; simp) hprem
  exact hout

/-- Body remaining after opening the outer binder of two consecutive universals. -/
noncomputable def openedDoubleBody (p : V) : V :=
  subst PA194PAeq.language (qVec PA194PAeq.language (?[^&(0 : V)] : V)) (shift PA194PAeq.language p)

theorem free_double_all {p : V} (hp : IsSemiformula PA194PAeq.language 2 p) :
    free PA194PAeq.language (^∀ p) = ^∀ (openedDoubleBody p) := by
  show substs1 PA194PAeq.language (^&(0 : V)) (shift PA194PAeq.language (^∀ p)) = _
  rw [shift_all hp.isUFormula, substs1_all hp.shift]
  rfl

theorem openedDoubleBody_valid {p : V} (hp : IsSemiformula PA194PAeq.language 2 p) :
    IsSemiformula PA194PAeq.language 1 (openedDoubleBody p) := by
  have h : IsSemiformula PA194PAeq.language 0 (free PA194PAeq.language (^∀ p)) :=
    (IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using hp)).free
  rw [free_double_all hp] at h
  simpa using IsSemiformula.all.mp h

theorem guarded_tr_double_all_intro {p : V} (hp : IsSemiformula PA194PAeq.language 2 p)
    (h : GDerivable T ({tr (free PA194PAeq.language (openedDoubleBody p))} : V)) :
    GDerivable T ({tr (^∀ (^∀ p))} : V) := by
  apply guarded_tr_all_intro (IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using hp))
  rw [free_double_all hp]
  exact guarded_tr_all_intro (openedDoubleBody_valid hp) h

/-- The open matrix of uniqueness for one model-valued free variable. -/
noncomputable def uniqueVariableBody (i : V) : V :=
  neg PA194PAeq.language (peq (^#(1 : V)) (^&i)) ^⋎
    (neg PA194PAeq.language (peq (^#(0 : V)) (^&i)) ^⋎ peq (^#(1 : V)) (^#(0 : V)))

theorem uniqueVariableBody_valid (i : V) : IsSemiformula PA194PAeq.language 2 (uniqueVariableBody i) := by
  unfold uniqueVariableBody
  apply IsSemiformula.or.mpr
  refine ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)), ?_⟩
  exact IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr (peq_valid (by simp) (by simp)), peq_valid (by simp) (by simp)⟩

theorem uniq_variable_eq (i : V) : uniq (^&i) = ^∀ (^∀ (uniqueVariableBody i)) := by
  simp [uniq,uniqueVariableBody,termBShift_fvar]

theorem guarded_uVar_of_open
    (h : ∀ i : V, GDerivable T ({tr (free PA194PAeq.language (openedDoubleBody (uniqueVariableBody i)))} : V)) :
    ∀ i : V, GDerivable T ({tr (uniq (^&i))} : V) := by
  intro i
  rw [uniq_variable_eq]
  exact guarded_tr_double_all_intro (uniqueVariableBody_valid i) (h i)

#print axioms guarded_tr_all_intro
#print axioms free_double_all
#print axioms openedDoubleBody_valid
#print axioms guarded_tr_double_all_intro
#print axioms uniqueVariableBody_valid
#print axioms uniq_variable_eq
#print axioms guarded_uVar_of_open
end generic
end PA194GuardedCompiler

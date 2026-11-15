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

/-- Variable naming follows from guarded reflexivity and the already checked variable witness rule. -/
theorem eVar_of_guarded_reflexivity
    (href : ∀ i : V, GDerivable T ({tr (peq (^&i) (^&i))} : V)) :
    ∀ i : V, GDerivable T ({tr (exName (^&i))} : V) := by
  intro i
  let q : V := peq (^#(0 : V)) (termBShift PA194PAeq.language (^&i))
  have hv : IsSemiterm PA194PAeq.language 0 (^&i : V) := by simp
  have h0 : IsSemiterm PA194PAeq.language 1 (^#(0 : V)) := by simp
  have hq : IsSemiformula PA194PAeq.language 1 q := peq_valid h0 (bShift_valid hv)
  have hsubst : substs1 PA194PAeq.language (^&i) q = peq (^&i) (^&i) := by
    dsimp [q]
    rw [substs1_peq h0 (bShift_valid hv),termSubst_bvar,termBShift_fvar,termSubst_fvar]
    simp
  have htr : substs1 SourceL (^&i) (trBody q) = tr (peq (^&i) (^&i)) := by
    rw [← tr_substs1_fvar hq,hsubst]
  have hr : IsFormula SourceL (tr (peq (^&i) (^&i))) := tr_valid (peq_valid hv hv)
  have hex : IsFormula SourceL (tr (^∃ q)) := tr_valid (IsSemiformula.exs.mpr (by simpa using hq))
  have hset : IsFormulaSet SourceL (insert (tr (peq (^&i) (^&i))) ({tr (^∃ q)} : V)) := by
    rw [singleton_eq_insert]
    exact fs_cons hr (fs_cons hex fs_nil)
  have hw : GDerivable T (insert (tr (peq (^&i) (^&i))) ({tr (^∃ q)} : V)) :=
    GDerivable.wk hset (by set_tac) (href i)
  have h := GDerivable.ex_rel (trBody_valid hq) (Δ := ({^∃ (domainCode (^#(0 : V)) ^⋏ trBody q)} : V)) (by simp) i (by
    rw [← tr_exs hq,htr]
    exact hw)
  change GDerivable T ({tr (^∃ q)} : V)
  rw [tr_exs hq]
  exact h

#print axioms eVar_of_guarded_reflexivity
end generic
end PA194GuardedCompiler

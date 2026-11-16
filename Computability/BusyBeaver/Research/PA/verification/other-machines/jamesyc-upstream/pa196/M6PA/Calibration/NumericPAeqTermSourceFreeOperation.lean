module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermLanguage
@[expose] public section

/-! Generalized last-bound-variable opening, using the pinned TermRec on the
existing PAeq syntax. The pinned termFreeAt sketch is commented out; active
arity-one Semiterm.free is calibrated separately below. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
namespace SourceFree
noncomputable def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z m. (z<m ∧ !qqBvarDef y z) ∨ (m≤z ∧ !qqFvarDef y 0)”
  fvar := .mkSigma “y x m. !qqFvarDef y (x+1)”
  func := .mkSigma “y k f v v' m. !qqFuncDef y k f v'”
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar param z := if z<param 0 then qqBvar z else qqFvar 0
  fvar _ x := qqFvar (x+1)
  func _ k f _ v' := qqFunc k f v'
  bvar_defined := .mk fun v => by
    by_cases h : v 1<v 2 <;> simp [blueprint,h,not_lt.mp,not_le.mpr]
  fvar_defined := .mk fun v => by simp [blueprint]
  func_defined := .mk fun v => by simp [blueprint]
end SourceFree
noncomputable def sourceFree (s t : V) : V := SourceFree.construction.result Presentation.language ![s] t
noncomputable def sourceFreeVec (s k ts : V) : V := SourceFree.construction.resultVec Presentation.language ![s] k ts
noncomputable def sourceFreeGraph : 𝚺ᴬ₁.Semisentence 3 :=
  (SourceFree.blueprint.result Presentation.language).rew <| Rew.subst ![#0,#2,#1]
instance sourceFree_defined : 𝚺ᴬ₁-Function₂ (sourceFree : V→V→V) via sourceFreeGraph :=
  .mk fun v => by
    simpa [sourceFreeGraph,sourceFree,Matrix.constant_eq_singleton,Matrix.comp_vecCons']
      using SourceFree.construction.result_defined.defined ![v 0,v 2,v 1]
instance sourceFree_definable : 𝚺ᴬ₁-Function₂ (sourceFree : V→V→V) := sourceFree_defined.to_definable
instance sourceFree_definable' (Γ m) : Γᴬ_[m+1]-Function₂ (sourceFree : V→V→V) := sourceFree_definable.of_sigmaOne
@[simp] theorem sourceFree_bvar (s i : V) : sourceFree s (qqBvar i)=if i<s then qqBvar i else qqFvar 0 := by
  simp [sourceFree,SourceFree.construction]
@[simp] theorem sourceFree_fvar (s i : V) : sourceFree s (qqFvar i)=qqFvar (i+1) := by
  simp [sourceFree,SourceFree.construction]
theorem sourceFree_func {s k f ts : V} (hf : Presentation.language.IsFunc k f)
    (hv : IsUTermVec Presentation.language k ts) :
    sourceFree s (qqFunc k f ts)=qqFunc k f (sourceFreeVec s k ts) := by
  simp [sourceFree,SourceFree.construction,hf,hv]; rfl
@[simp] theorem sourceFreeVec_nil (s : V) : sourceFreeVec s 0 0=0 :=
  SourceFree.construction.resultVec_nil Presentation.language ![s]
theorem sourceFreeVec_cons {s k t ts : V} (ht : IsUTerm Presentation.language t)
    (hv : IsUTermVec Presentation.language k ts) :
    sourceFreeVec s (k+1) (t∷ts)=sourceFree s t ∷ sourceFreeVec s k ts :=
  SourceFree.construction.resultVec_cons Presentation.language ![s] hv ht
@[simp] theorem sourceFreeVec_one {s t : V} (ht : IsUTerm Presentation.language t) :
    sourceFreeVec s 1 (t∷0)=sourceFree s t ∷ 0 := by
  rw [show (1:V)=0+1 by simp,sourceFreeVec_cons ht (by simp),sourceFreeVec_nil]
@[simp] theorem sourceFreeVec_two {s t u : V} (ht : IsUTerm Presentation.language t) (hu : IsUTerm Presentation.language u) :
    sourceFreeVec s 2 (t∷u∷0)=sourceFree s t ∷ sourceFree s u ∷ 0 := by
  rw [show (2:V)=1+1 from one_add_one_eq_two.symm,sourceFreeVec_cons ht (by simp [hu]),sourceFreeVec_one hu]

theorem sourceFree_bvar_last {s i : V} (hi : i<s+1) (hn : ¬i<s) :
    i=s ∧ sourceFree s (qqBvar i)=qqFvar 0 := by
  exact ⟨le_antisymm (lt_succ_iff_le.mp hi) (not_lt.mp hn),by simp [hn]⟩

theorem sourceFreeVec_length {s k ts : V} (hv : IsUTermVec Presentation.language k ts) :
    len (sourceFreeVec s k ts)=k := SourceFree.construction.resultVec_lh Presentation.language _ hv
theorem sourceFreeVec_nth {s k ts i : V} (hv : IsUTermVec Presentation.language k ts) (hi : i<k) :
    nth (sourceFreeVec s k ts) i=sourceFree s (nth ts i) :=
  SourceFree.construction.nth_resultVec Presentation.language _ hv hi

theorem sourceFree_isSemiterm {s t : V} (ht : IsSemiterm Presentation.language (s+1) t) :
    IsSemiterm Presentation.language s (sourceFree s t) := by
  apply IsSemiterm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro i hi
    by_cases hh : i<s <;> simp [sourceFree_bvar,hh]
  · intro i; simp
  · intro k f ts hf hv ih
    rw [sourceFree_func hf hv.isUTerm]
    apply IsSemiterm.func.mpr
    refine ⟨hf,IsSemitermVec.iff.mpr ⟨sourceFreeVec_length hv.isUTerm,?_⟩⟩
    intro i hi
    rw [sourceFreeVec_nth hv.isUTerm hi]
    exact ih i hi

#print axioms sourceFree_defined
#print axioms sourceFree_bvar
#print axioms sourceFree_fvar
#print axioms sourceFree_func
#print axioms sourceFreeVec_one
#print axioms sourceFreeVec_two
#print axioms sourceFree_bvar_last
#print axioms sourceFree_isSemiterm
end M6.PA.NumericPAeqTerm


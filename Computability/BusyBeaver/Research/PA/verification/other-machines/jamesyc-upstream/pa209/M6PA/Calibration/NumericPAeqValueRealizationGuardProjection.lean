module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueRealizationGuardValidity
public import M6PA.Calibration.FoundationRelationalSequentPropositional
public import M6PA.Calibration.FoundationRelationalSequentFold
@[expose] public section
namespace M6.PA.NumericPAeqValueRealizationGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric
open ActualCertificateConstructors.Dominated ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] guardGraph entryGraph translateGraph acceptedArrowGraph
noncomputable def projectionGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “code param b f w a k i. ∃ g e left right, !guardGraph g b f w a k ∧ !entryGraph e b f w a i ∧
    !translateGraph left param g ∧ !translateGraph right param e ∧ !acceptedArrowGraph code left right”
theorem projection_graph (code param b f w a k i:V):projectionGraph.val.Evalb ![code,param,b,f,w,a,k,i] ↔
    verifyValue code=wim (translate param (guard b f w a k)) (translate param (entry b f w a i))+1 := by
  simp [projectionGraph,guard_graph,entry_graph,translate_graph,acceptedArrow_graph,Matrix.comp_vecCons'']
attribute [local irreducible] projectionGraph
noncomputable def projectionInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ param b f w a n i, i<k →
    (∀ j<k, ∃ e, !entryGraph e b f w a j ∧ !((isSemiformula language).sigma) n e) →
    ∃ code, !projectionGraph code param b f w a k i”
theorem projection_invariant (k:V):projectionInvariant.Evalb ![k] ↔
    ∀param b f w a n i:V,i<k→(∀j<k,IsSemiformula language n (entry b f w a j))→
      ∃code,verifyValue code=wim (translate param (guard b f w a k)) (translate param (entry b f w a i))+1 := by
  simp [projectionInvariant,entry_graph,projection_graph,Matrix.comp_vecCons'']
attribute [local irreducible] projectionInvariant guard translate
theorem guard_projection_certificate (param b f w a k n i:V) (hi:i<k)
    (h:∀j<k,IsSemiformula language n (entry b f w a j)):
    ∃code,verifyValue code=wim (translate param (guard b f w a k)) (translate param (entry b f w a i))+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀param b f w a n i:V,i<k→(∀j<k,IsSemiformula language n (entry b f w a j))→
      ∃code,verifyValue code=wim (translate param (guard b f w a k)) (translate param (entry b f w a i))+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀param b f w a n i:V,
      i<k→(∀j<k,IsSemiformula language n (entry b f w a j))→
      ∃code,verifyValue code=wim (translate param (guard b f w a k)) (translate param (entry b f w a i))+1) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb projectionInvariant,by trivial,?_⟩
      intro k; simpa using (projection_invariant (V:=V) k).symm
    · intro param b f w a n i hi _; exact False.elim (not_lt_zero hi)
    · intro k ih param b f w a n i hi h
      have old : ∀j<k,IsSemiformula language n (entry b f w a j) := fun j hj=>h j (lt_trans hj (lt_add_one k))
      have hg := (guard_isSemiformula b f w a k n old).isUFormula
      have hd := (h k (lt_add_one k)).isUFormula
      rw [guard_succ,translate_and _ _ _ hg hd,translationAnd_eq]
      let left := translate param (guard b f w a k)
      let right := translate param (entry b f w a k)
      let assumption : Context [wa left right] (wa left right) := .assumption (by simp)
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hi) with he|hlt
      · subst i
        let out := assumption.andRight.deduction.empty
        exact ⟨out.code,out.accepted⟩
      · obtain ⟨code,hcode⟩ := ih param b f w a n i hlt old
        let out := implicationCompose assumption.andLeft.deduction.empty (⟨code,hcode⟩)
        exact ⟨out.code,out.accepted⟩
  exact hall k param b f w a n i hi h
#print axioms projection_graph
#print axioms projection_invariant
#print axioms guard_projection_certificate
end M6.PA.NumericPAeqValueRealizationGuard


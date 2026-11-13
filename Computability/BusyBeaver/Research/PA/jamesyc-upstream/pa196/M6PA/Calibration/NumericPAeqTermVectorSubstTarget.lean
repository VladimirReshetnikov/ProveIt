module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermVectorSubstValidity
public import M6PA.Calibration.NumericPAeqTermTargetSubst
@[expose] public section
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def vectorSubstTargetGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “v param w t. ∃ out, !(termSubstGraph Presentation.language) out w t ∧ !targetSubstAgreementGraph v param out”
theorem vectorSubstTarget_graph (v param w t : V) : vectorSubstTargetGraph.val.Evalb ![v,param,w,t] ↔
    subst language v (valueSyntax param (termSubst Presentation.language w t))=
      valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t) := by
  simp [vectorSubstTargetGraph,targetSubstAgreement_graph,Matrix.comp_vecCons'']
noncomputable def vectorSubstTargetInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s r n m v param w, !substitutionCoverageGraph s r n param w t → !((isSemitermVec language).sigma) n m v → !vectorSubstTargetGraph v param w t”
theorem vectorSubstTarget_invariant (k : V) : vectorSubstTargetInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s r n m v param w, SubstitutionCovered s r n param w t → IsSemitermVec language n m v →
      subst language v (valueSyntax param (termSubst Presentation.language w t))=valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t) := by
  simp [vectorSubstTargetInvariant,substitutionCoverage_graph,vectorSubstTarget_graph,Matrix.comp_vecCons'']

private theorem vectorSubstTarget_step (t : V)
    (ih : ∀ a<t, ∀ s r n m v param w, SubstitutionCovered s r n param w a → IsSemitermVec language n m v →
      subst language v (valueSyntax param (termSubst Presentation.language w a))=valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w a)) :
    ∀ s r n m v param w, SubstitutionCovered s r n param w t → IsSemitermVec language n m v →
      subst language v (valueSyntax param (termSubst Presentation.language w t))=valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t) := by
  intro s r n m v param w h hw
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · rw [termSubst_bvar]
    exact valueSyntax_targetSubst (substitution_covered_nth h (IsSemiterm.bvar.mp h.2.1)) hw
  · have hi := lt_of_lt_of_le (var_lt_qqFvar i) h.2.2.1
    rw [termSubst_fvar,valueSyntax_fvar,variableValue_targetSubst hw h.1.2.2 (h.1.2.1.nth hi),valueSyntax_fvar]
    simp only [targetSubstParameters,parameters_result,parameters_free,RelationalPredicateTemplate.substTerms_nth h.1.2.1 hi]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    rw [termSubst_func hf hv]
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts
      rw [termSubstVec_nil,valueSyntax_zero,zeroValue_targetSubst hw h.1.2.2,valueSyntax_zero]
      simp [targetSubstParameters]
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := substitution_covered_child h hu (unary_child_rank a)
      rw [termSubstVec_cons₁ hu.isUTerm,valueSyntax_successor _ _ (h.2.2.2.1.termSubst hu).isUTerm,
        successorValue_targetSubst hw h.1.2.2 (valueSyntax_vectorSubst_isSemiformula hc),
        ih a (unary_child_rank a) s r (n+1) (m+1) (qVec language v) _ w hc hw.qVec,targetSubstParameters_child h.1 hw,
        valueSyntax_successor _ _ (h.2.2.2.1.termSubst hu).isUTerm]
      simp [targetSubstParameters]
    · obtain ⟨a,b,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := substitution_covered_binary h huv.1 (binary_left_rank f a b) (show (1:V)<2 by simp)
      have hb := substitution_covered_binary h huv.2 (binary_right_rank f a b) (show (0:V)<2 by simp)
      have ia := ih a (binary_left_rank f a b) s r ((n+1)+1) ((m+1)+1) (qVec language (qVec language v)) _ w ha hw.qVec.qVec
      have ib := ih b (binary_right_rank f a b) s r ((n+1)+1) ((m+1)+1) (qVec language (qVec language v)) _ w hb hw.qVec.qVec
      rw [termSubstVec_cons₂ huv.1.isUTerm huv.2.isUTerm]
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ (h.2.2.2.1.termSubst huv.1).isUTerm (h.2.2.2.1.termSubst huv.2).isUTerm,
          additionValue,binaryValue_targetSubst additionTemplate hw h.1.2.2
            (valueSyntax_vectorSubst_isSemiformula ha) (valueSyntax_vectorSubst_isSemiformula hb),ia,ib,
          targetSubstParameters_binary h.1 hw (by simp),targetSubstParameters_binary h.1 hw (by simp),
          valueSyntax_addition _ _ _ (h.2.2.2.1.termSubst huv.1).isUTerm (h.2.2.2.1.termSubst huv.2).isUTerm]
        simp [additionValue,targetSubstParameters]
      · rw [valueSyntax_multiplication _ _ _ (h.2.2.2.1.termSubst huv.1).isUTerm (h.2.2.2.1.termSubst huv.2).isUTerm,
          multiplicationValue,binaryValue_targetSubst multiplicationTemplate hw h.1.2.2
            (valueSyntax_vectorSubst_isSemiformula ha) (valueSyntax_vectorSubst_isSemiformula hb),ia,ib,
          targetSubstParameters_binary h.1 hw (by simp),targetSubstParameters_binary h.1 hw (by simp),
          valueSyntax_multiplication _ _ _ (h.2.2.2.1.termSubst huv.1).isUTerm (h.2.2.2.1.termSubst huv.2).isUTerm]
        simp [multiplicationValue,targetSubstParameters]

attribute [local irreducible] vectorSubstTargetInvariant
theorem valueSyntax_vectorSubst_targetSubst {s r n m v param w t : V} (h : SubstitutionCovered s r n param w t)
    (hw : IsSemitermVec language n m v) :
    subst language v (valueSyntax param (termSubst Presentation.language w t))=valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s r n m v param w, SubstitutionCovered s r n param w t → IsSemitermVec language n m v →
      subst language v (valueSyntax param (termSubst Presentation.language w t))=valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s r n m v param w, SubstitutionCovered s r n param w t → IsSemitermVec language n m v →
        subst language v (valueSyntax param (termSubst Presentation.language w t))=valueSyntax (targetSubstParameters v param) (termSubst Presentation.language w t)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb vectorSubstTargetInvariant,by trivial,?_⟩
      intro k; simpa using (vectorSubstTarget_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s r n m v param w h hw
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact vectorSubstTarget_step k ih s r n m v param w h hw
      · exact ih t hlt s r n m v param w h hw
  exact hall (t+1) t (lt_add_one t) s r n m v param w h hw

#print axioms vectorSubstTarget_graph
#print axioms vectorSubstTarget_invariant
#print axioms vectorSubstTarget_step
#print axioms valueSyntax_vectorSubst_targetSubst
end M6.PA.NumericPAeqTerm


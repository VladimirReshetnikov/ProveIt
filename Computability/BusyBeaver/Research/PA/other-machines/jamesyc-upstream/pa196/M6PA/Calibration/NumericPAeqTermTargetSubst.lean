module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetSubstConstructors
public import M6PA.Calibration.NumericPAeqTermValidity
@[expose] public section

/-! Exact target bound-variable substitution naturality in every model of PA.
All source ranks, arities and environment vectors may be nonstandard. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem targetSubst_covered {s n m w param t : V} (h : TermCovered s n param t)
    (hw : IsSemitermVec language n m w) : TermCovered s m (targetSubstParameters w param) t := by
  refine ⟨targetSubstParameters_valid h.1 hw,h.2.1,?_⟩
  simpa only [targetSubstParameters,parameters_free,RelationalPredicateTemplate.substTerms_length h.1.2.1] using h.2.2

noncomputable def targetSubstAgreementGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “w param t. ∃ out shifted shiftedParam,
    !valueSyntaxGraph out param t ∧ !(substsGraph language) shifted w out ∧
    !targetSubstParametersGraph shiftedParam w param ∧ !valueSyntaxGraph shifted shiftedParam t”
theorem targetSubstAgreement_graph (w param t : V) :
    targetSubstAgreementGraph.val.Evalb ![w,param,t] ↔
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  simp [targetSubstAgreementGraph,valueSyntax_graph,targetSubstParameters_graph,Matrix.comp_vecCons'']

noncomputable def targetSubstInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n m w param, !coverageGraph s n param t → !((isSemitermVec language).sigma) n m w → !targetSubstAgreementGraph w param t”
theorem targetSubst_invariant (k : V) : targetSubstInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n m w param, TermCovered s n param t → IsSemitermVec language n m w →
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  simp [targetSubstInvariant,coverage_graph,targetSubstAgreement_graph,Matrix.comp_vecCons'']

private theorem targetSubst_step (t : V)
    (ih : ∀ u<t, ∀ s n m w param, TermCovered s n param u → IsSemitermVec language n m w →
      subst language w (valueSyntax param u)=valueSyntax (targetSubstParameters w param) u) :
    ∀ s n m w param, TermCovered s n param t → IsSemitermVec language n m w →
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  intro s n m w param h hw
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · have hi := IsSemiterm.bvar.mp h.2.1
    rw [valueSyntax_bvar,variableValue_targetSubst hw h.1.2.2 (h.1.1.nth hi),valueSyntax_bvar]
    simp only [targetSubstParameters,parameters_result,parameters_bound,RelationalPredicateTemplate.substTerms_nth h.1.1 hi]
  · have hi := lt_of_lt_of_le (var_lt_qqFvar i) h.2.2
    rw [valueSyntax_fvar,variableValue_targetSubst hw h.1.2.2 (h.1.2.1.nth hi),valueSyntax_fvar]
    simp only [targetSubstParameters,parameters_result,parameters_free,RelationalPredicateTemplate.substTerms_nth h.1.2.1 hi]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts
      rw [valueSyntax_zero,zeroValue_targetSubst hw h.1.2.2,valueSyntax_zero]
      simp [targetSubstParameters]
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := coverage_child h hu (unary_child_rank u)
      rw [valueSyntax_successor _ _ hu.isUTerm,
        successorValue_targetSubst hw h.1.2.2 (valueSyntax_isSemiformula hc),
        ih u (unary_child_rank u) s (n+1) (m+1) (qVec language w) _ hc hw.qVec,targetSubstParameters_child h.1 hw,
        valueSyntax_successor _ _ hu.isUTerm]
      simp [targetSubstParameters]
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := coverage_binary_child h huv.1 (binary_left_rank f u v) (show (1:V)<2 by simp)
      have hb := coverage_binary_child h huv.2 (binary_right_rank f u v) (show (0:V)<2 by simp)
      have ia := ih u (binary_left_rank f u v) s ((n+1)+1) ((m+1)+1) (qVec language (qVec language w)) _ ha hw.qVec.qVec
      have ib := ih v (binary_right_rank f u v) s ((n+1)+1) ((m+1)+1) (qVec language (qVec language w)) _ hb hw.qVec.qVec
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm,
          additionValue,binaryValue_targetSubst additionTemplate hw h.1.2.2
            (valueSyntax_isSemiformula ha) (valueSyntax_isSemiformula hb),ia,ib,
          targetSubstParameters_binary h.1 hw (by simp),targetSubstParameters_binary h.1 hw (by simp),
          valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [additionValue,targetSubstParameters]
      · rw [valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm,
          multiplicationValue,binaryValue_targetSubst multiplicationTemplate hw h.1.2.2
            (valueSyntax_isSemiformula ha) (valueSyntax_isSemiformula hb),ia,ib,
          targetSubstParameters_binary h.1 hw (by simp),targetSubstParameters_binary h.1 hw (by simp),
          valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [multiplicationValue,targetSubstParameters]

attribute [local irreducible] targetSubstInvariant
theorem valueSyntax_targetSubst {s n m w param t : V} (h : TermCovered s n param t)
    (hw : IsSemitermVec language n m w) :
    subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n m w param, TermCovered s n param t → IsSemitermVec language n m w →
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n m w param, TermCovered s n param t → IsSemitermVec language n m w →
        subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb targetSubstInvariant,by trivial,?_⟩
      intro k; simpa using (targetSubst_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n m w param h hw
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact targetSubst_step k ih s n m w param h hw
      · exact ih t hlt s n m w param h hw
  exact hall (t+1) t (lt_add_one t) s n m w param h hw

#print axioms targetSubst_covered
#print axioms targetSubstAgreement_graph
#print axioms targetSubst_invariant
#print axioms targetSubst_step
#print axioms valueSyntax_targetSubst
end M6.PA.NumericPAeqTerm


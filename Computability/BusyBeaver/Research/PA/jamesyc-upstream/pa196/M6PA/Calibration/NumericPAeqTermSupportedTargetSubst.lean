module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetSubstConstructors
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Exact target bound-variable substitution naturality in every model of PA.
All source ranks, arities and environment vectors may be nonstandard. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem targetSubst_supported_covered {s n m w param t : V} (h : SupportedTermCovered s n param t)
    (hw : IsSemitermVec language n m w) : SupportedTermCovered s m (targetSubstParameters w param) t := by
  refine ⟨targetSubstParameters_valid h.1 hw,h.2.1,?_⟩
  simpa only [targetSubstParameters,parameters_free,RelationalPredicateTemplate.substTerms_length h.1.2.1] using h.2.2

noncomputable def supportedTargetSubstAgreementGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “w param t. ∃ out shifted shiftedParam,
    !valueSyntaxGraph out param t ∧ !(substsGraph language) shifted w out ∧
    !targetSubstParametersGraph shiftedParam w param ∧ !valueSyntaxGraph shifted shiftedParam t”
theorem supportedTargetSubstAgreement_graph (w param t : V) :
    supportedTargetSubstAgreementGraph.val.Evalb ![w,param,t] ↔
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  simp [supportedTargetSubstAgreementGraph,valueSyntax_graph,targetSubstParameters_graph,Matrix.comp_vecCons'']

noncomputable def supportedTargetSubstInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n m w param, !supportedCoverageGraph s n param t → !((isSemitermVec language).sigma) n m w → !supportedTargetSubstAgreementGraph w param t”
theorem supportedTargetSubst_invariant (k : V) : supportedTargetSubstInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n m w param, SupportedTermCovered s n param t → IsSemitermVec language n m w →
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  simp [supportedTargetSubstInvariant,supportedCoverage_graph,supportedTargetSubstAgreement_graph,Matrix.comp_vecCons'']

private theorem supportedTargetSubst_step (t : V)
    (ih : ∀ u<t, ∀ s n m w param, SupportedTermCovered s n param u → IsSemitermVec language n m w →
      subst language w (valueSyntax param u)=valueSyntax (targetSubstParameters w param) u) :
    ∀ s n m w param, SupportedTermCovered s n param t → IsSemitermVec language n m w →
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  intro s n m w param h hw
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · have hi := IsSemiterm.bvar.mp h.2.1
    rw [valueSyntax_bvar,variableValue_targetSubst hw h.1.2.2 (h.1.1.nth hi),valueSyntax_bvar]
    simp only [targetSubstParameters,parameters_result,parameters_bound,RelationalPredicateTemplate.substTerms_nth h.1.1 hi]
  · have hi := (freeSupported_fvar _ _).mp h.2.2
    rw [valueSyntax_fvar,variableValue_targetSubst hw h.1.2.2 (h.1.2.1.nth hi),valueSyntax_fvar]
    simp only [targetSubstParameters,parameters_result,parameters_free,RelationalPredicateTemplate.substTerms_nth h.1.2.1 hi]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    have hs := (freeSupported_func hf hv).mp h.2.2
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts
      rw [valueSyntax_zero,zeroValue_targetSubst hw h.1.2.2,valueSyntax_zero]
      simp [targetSubstParameters]
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := supported_coverage_child h hu (by simpa using hs 0 (by simp))
      rw [valueSyntax_successor _ _ hu.isUTerm,
        successorValue_targetSubst hw h.1.2.2 (valueSyntax_supported_isSemiformula hc),
        ih u (unary_child_rank u) s (n+1) (m+1) (qVec language w) _ hc hw.qVec,targetSubstParameters_child h.1 hw,
        valueSyntax_successor _ _ hu.isUTerm]
      simp [targetSubstParameters]
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := supported_coverage_binary_child h huv.1 (by simpa using hs 0 (by simp)) (show (1:V)<2 by simp)
      have hb := supported_coverage_binary_child h huv.2 (by simpa using hs 1 (by simp)) (show (0:V)<2 by simp)
      have ia := ih u (binary_left_rank f u v) s ((n+1)+1) ((m+1)+1) (qVec language (qVec language w)) _ ha hw.qVec.qVec
      have ib := ih v (binary_right_rank f u v) s ((n+1)+1) ((m+1)+1) (qVec language (qVec language w)) _ hb hw.qVec.qVec
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm,
          additionValue,binaryValue_targetSubst additionTemplate hw h.1.2.2
            (valueSyntax_supported_isSemiformula ha) (valueSyntax_supported_isSemiformula hb),ia,ib,
          targetSubstParameters_binary h.1 hw (by simp),targetSubstParameters_binary h.1 hw (by simp),
          valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [additionValue,targetSubstParameters]
      · rw [valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm,
          multiplicationValue,binaryValue_targetSubst multiplicationTemplate hw h.1.2.2
            (valueSyntax_supported_isSemiformula ha) (valueSyntax_supported_isSemiformula hb),ia,ib,
          targetSubstParameters_binary h.1 hw (by simp),targetSubstParameters_binary h.1 hw (by simp),
          valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [multiplicationValue,targetSubstParameters]

attribute [local irreducible] supportedTargetSubstInvariant
theorem valueSyntax_supported_targetSubst {s n m w param t : V} (h : SupportedTermCovered s n param t)
    (hw : IsSemitermVec language n m w) :
    subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n m w param, SupportedTermCovered s n param t → IsSemitermVec language n m w →
      subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n m w param, SupportedTermCovered s n param t → IsSemitermVec language n m w →
        subst language w (valueSyntax param t)=valueSyntax (targetSubstParameters w param) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedTargetSubstInvariant,by trivial,?_⟩
      intro k; simpa using (supportedTargetSubst_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n m w param h hw
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact supportedTargetSubst_step k ih s n m w param h hw
      · exact ih t hlt s n m w param h hw
  exact hall (t+1) t (lt_add_one t) s n m w param h hw

#print axioms targetSubst_supported_covered
#print axioms supportedTargetSubstAgreement_graph
#print axioms supportedTargetSubst_invariant
#print axioms supportedTargetSubst_step
#print axioms valueSyntax_supported_targetSubst
end M6.PA.NumericPAeqTerm


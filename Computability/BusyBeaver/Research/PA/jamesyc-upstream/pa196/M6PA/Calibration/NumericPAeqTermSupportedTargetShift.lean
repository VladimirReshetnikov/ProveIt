module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermTargetShiftConstructors
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Exact target free-variable shift naturality in every model of PA.
All source ranks, arities and environment vectors may be nonstandard. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def supportedTargetShiftAgreementGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “param t. ∃ out shifted shiftedParam,
    !valueSyntaxGraph out param t ∧ !(shiftGraph language) shifted out ∧
    !targetShiftParametersGraph shiftedParam param ∧ !valueSyntaxGraph shifted shiftedParam t”
theorem supportedTargetShiftAgreement_graph (param t : V) :
    supportedTargetShiftAgreementGraph.val.Evalb ![param,t] ↔
      shift language (valueSyntax param t)=valueSyntax (targetShiftParameters param) t := by
  simp [supportedTargetShiftAgreementGraph,valueSyntax_graph,targetShiftParameters_graph,Matrix.comp_vecCons'']

noncomputable def supportedTargetShiftInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n param, !supportedCoverageGraph s n param t → !supportedTargetShiftAgreementGraph param t”
theorem supportedTargetShift_invariant (k : V) : supportedTargetShiftInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n param, SupportedTermCovered s n param t →
      shift language (valueSyntax param t)=valueSyntax (targetShiftParameters param) t := by
  simp [supportedTargetShiftInvariant,supportedCoverage_graph,supportedTargetShiftAgreement_graph,Matrix.comp_vecCons'']

private theorem supportedTargetShift_step (t : V)
    (ih : ∀ u<t, ∀ s n param, SupportedTermCovered s n param u →
      shift language (valueSyntax param u)=valueSyntax (targetShiftParameters param) u) :
    ∀ s n param, SupportedTermCovered s n param t →
      shift language (valueSyntax param t)=valueSyntax (targetShiftParameters param) t := by
  intro s n param h
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · have hi := IsSemiterm.bvar.mp h.2.1
    rw [valueSyntax_bvar,variableValue_targetShift h.1.2.2 (h.1.1.nth hi),valueSyntax_bvar]
    simp only [targetShiftParameters,parameters_result,parameters_bound,targetShiftTerms_nth h.1.1 hi]
  · have hi := (freeSupported_fvar _ _).mp h.2.2
    rw [valueSyntax_fvar,variableValue_targetShift h.1.2.2 (h.1.2.1.nth hi),valueSyntax_fvar]
    simp only [targetShiftParameters,parameters_result,parameters_free,targetShiftTerms_nth h.1.2.1 hi]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    have hs := (freeSupported_func hf hv).mp h.2.2
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts
      rw [valueSyntax_zero,zeroValue_targetShift h.1.2.2,valueSyntax_zero]
      simp [targetShiftParameters]
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := supported_coverage_child h hu (by simpa using hs 0 (by simp))
      rw [valueSyntax_successor _ _ hu.isUTerm,
        successorValue_targetShift h.1.2.2 (valueSyntax_supported_isSemiformula hc),
        ih u (unary_child_rank u) s (n+1) _ hc,targetShiftParameters_child h.1,
        valueSyntax_successor _ _ hu.isUTerm]
      simp [targetShiftParameters]
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := supported_coverage_binary_child h huv.1 (by simpa using hs 0 (by simp)) (show (1:V)<2 by simp)
      have hb := supported_coverage_binary_child h huv.2 (by simpa using hs 1 (by simp)) (show (0:V)<2 by simp)
      have ia := ih u (binary_left_rank f u v) s ((n+1)+1) _ ha
      have ib := ih v (binary_right_rank f u v) s ((n+1)+1) _ hb
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm,
          additionValue,binaryValue_targetShift additionTemplate additionTemplate_targetShift h.1.2.2
            (valueSyntax_supported_isSemiformula ha) (valueSyntax_supported_isSemiformula hb),ia,ib,
          targetShiftParameters_binary h.1,targetShiftParameters_binary h.1,
          valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [additionValue,targetShiftParameters]
      · rw [valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm,
          multiplicationValue,binaryValue_targetShift multiplicationTemplate multiplicationTemplate_targetShift h.1.2.2
            (valueSyntax_supported_isSemiformula ha) (valueSyntax_supported_isSemiformula hb),ia,ib,
          targetShiftParameters_binary h.1,targetShiftParameters_binary h.1,
          valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [multiplicationValue,targetShiftParameters]

attribute [local irreducible] supportedTargetShiftInvariant
theorem valueSyntax_supported_targetShift {s n param t : V} (h : SupportedTermCovered s n param t) :
    shift language (valueSyntax param t)=valueSyntax (targetShiftParameters param) t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n param, SupportedTermCovered s n param t →
      shift language (valueSyntax param t)=valueSyntax (targetShiftParameters param) t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n param, SupportedTermCovered s n param t →
        shift language (valueSyntax param t)=valueSyntax (targetShiftParameters param) t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedTargetShiftInvariant,by trivial,?_⟩
      intro k; simpa using (supportedTargetShift_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact supportedTargetShift_step k ih s n param h
      · exact ih t hlt s n param h
  exact hall (t+1) t (lt_add_one t) s n param h

#print axioms supportedTargetShiftAgreement_graph
#print axioms supportedTargetShift_invariant
#print axioms supportedTargetShift_step
#print axioms valueSyntax_supported_targetShift
end M6.PA.NumericPAeqTerm


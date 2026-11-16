module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceFreeParameters
public import M6PA.Calibration.NumericPAeqTermSourceFreeCalibration
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Exact last-bound opening interpretation in all PA models. Original source coverage only; opened code coverage is not assumed. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def supportedSourceFreeAgreementGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “s param t. ∃ out opened prep,
    !valueSyntaxGraph out param t ∧ !sourceFreeGraph opened s t ∧
    !sourceFreeParametersGraph prep s param ∧ !valueSyntaxGraph out prep opened”
theorem supportedSourceFreeAgreement_graph (s param t : V) :
    supportedSourceFreeAgreementGraph.val.Evalb ![s,param,t] ↔
      valueSyntax (sourceFreeParameters s param) (sourceFree s t)=valueSyntax param t := by
  simp [supportedSourceFreeAgreementGraph,valueSyntax_graph,sourceFreeParameters_graph,Matrix.comp_vecCons'',eq_comm]
noncomputable def supportedSourceFreeInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n param, !supportedCoverageGraph (s+1) n param t → !supportedSourceFreeAgreementGraph s param t”
theorem supportedSourceFree_invariant (k : V) : supportedSourceFreeInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n param, SupportedTermCovered (s+1) n param t →
      valueSyntax (sourceFreeParameters s param) (sourceFree s t)=valueSyntax param t := by
  simp [supportedSourceFreeInvariant,supportedCoverage_graph,supportedSourceFreeAgreement_graph,Matrix.comp_vecCons'']

private theorem supportedSourceFree_step (t : V)
    (ih : ∀ u<t, ∀ s n param, SupportedTermCovered (s+1) n param u →
      valueSyntax (sourceFreeParameters s param) (sourceFree s u)=valueSyntax param u) :
    ∀ s n param, SupportedTermCovered (s+1) n param t →
      valueSyntax (sourceFreeParameters s param) (sourceFree s t)=valueSyntax param t := by
  intro s n param h
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · have hi := IsSemiterm.bvar.mp h.2.1
    by_cases hh : i<s
    · simp only [sourceFree_bvar,hh,ite_true,valueSyntax_bvar,sourceFreeParameters,parameters_bound,parameters_result]
      rw [dropLast_nth h.1.1.lh hh]
    · have he := (sourceFree_bvar_last hi hh).1
      subst i
      simp [sourceFreeParameters]
  · simp [sourceFreeParameters]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    rw [sourceFree_func hf hv]
    have hs := (freeSupported_func hf hv).mp h.2.2
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; simp [sourceFreeParameters]
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := supported_coverage_child h hu (by simpa using hs 0 (by simp))
      rw [sourceFreeVec_one hu.isUTerm,valueSyntax_successor _ _ (sourceFree_isSemiterm hu).isUTerm,
        sourceFreeParameters_child h.1,
        ih u (unary_child_rank u) s (n+1) _ hc,
        valueSyntax_successor _ _ hu.isUTerm]
      simp [sourceFreeParameters]
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := supported_coverage_binary_child h huv.1 (by simpa using hs 0 (by simp)) (show (1:V)<2 by simp)
      have hb := supported_coverage_binary_child h huv.2 (by simpa using hs 1 (by simp)) (show (0:V)<2 by simp)
      have ia := ih u (binary_left_rank f u v) s ((n+1)+1) _ ha
      have ib := ih v (binary_right_rank f u v) s ((n+1)+1) _ hb
      rw [sourceFreeVec_two huv.1.isUTerm huv.2.isUTerm]
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ (sourceFree_isSemiterm huv.1).isUTerm (sourceFree_isSemiterm huv.2).isUTerm,
          sourceFreeParameters_binary h.1,sourceFreeParameters_binary h.1,ia,ib,
          valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [sourceFreeParameters]
      · rw [valueSyntax_multiplication _ _ _ (sourceFree_isSemiterm huv.1).isUTerm (sourceFree_isSemiterm huv.2).isUTerm,
          sourceFreeParameters_binary h.1,sourceFreeParameters_binary h.1,ia,ib,
          valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [sourceFreeParameters]

attribute [local irreducible] supportedSourceFreeInvariant
theorem valueSyntax_supported_sourceFree {s n param t : V} (h : SupportedTermCovered (s+1) n param t) :
    valueSyntax (sourceFreeParameters s param) (sourceFree s t)=valueSyntax param t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n param, SupportedTermCovered (s+1) n param t →
      valueSyntax (sourceFreeParameters s param) (sourceFree s t)=valueSyntax param t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n param, SupportedTermCovered (s+1) n param t →
        valueSyntax (sourceFreeParameters s param) (sourceFree s t)=valueSyntax param t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedSourceFreeInvariant,by trivial,?_⟩
      intro k; simpa using (supportedSourceFree_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact supportedSourceFree_step k ih s n param h
      · exact ih t hlt s n param h
  exact hall (t+1) t (lt_add_one t) s n param h

theorem valueSyntax_supported_sourceFree_isSemiformula {s n param t : V}
    (h : SupportedTermCovered (s+1) n param t) :
    IsSemiformula language n (valueSyntax (sourceFreeParameters s param) (sourceFree s t)) := by
  rw [valueSyntax_supported_sourceFree h]
  exact valueSyntax_supported_isSemiformula h

#print axioms supportedSourceFreeAgreement_graph
#print axioms supportedSourceFree_invariant
#print axioms supportedSourceFree_step
#print axioms valueSyntax_supported_sourceFree
#print axioms valueSyntax_supported_sourceFree_isSemiformula
end M6.PA.NumericPAeqTerm


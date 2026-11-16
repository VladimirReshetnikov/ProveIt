module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceSubstVectorCoverage
@[expose] public section

/-! Actual target semiformula validity in arbitrary PA models, under explicit
finite source/target environment coverage. This is not semantic value existence. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] valueSyntaxGraph coverageGraph
noncomputable def vectorSubstOutputGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “n param w t. ∃ v, !(termSubstGraph Presentation.language) v w t ∧ !outputValidGraph n param v”
theorem vectorSubstOutput_graph (n param w t : V) : vectorSubstOutputGraph.val.Evalb ![n,param,w,t] ↔
    IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t)) := by
  simp [vectorSubstOutputGraph,outputValid_graph,Matrix.comp_vecCons'']
noncomputable def vectorSubstValidityInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s r n param w, !substitutionCoverageGraph s r n param w t → !vectorSubstOutputGraph n param w t”
theorem vectorSubstValidity_invariant (k : V) : vectorSubstValidityInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s r n param w, SubstitutionCovered s r n param w t → IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t)) := by
  simp [vectorSubstValidityInvariant,substitutionCoverage_graph,vectorSubstOutput_graph,Matrix.comp_vecCons'']

private theorem vectorSubstValidity_step (t : V)
    (ih : ∀ u<t, ∀ s r n param w, SubstitutionCovered s r n param w u → IsSemiformula language n (valueSyntax param (termSubst Presentation.language w u))) :
    ∀ s r n param w, SubstitutionCovered s r n param w t → IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t)) := by
  intro s r n param w h
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · rw [termSubst_bvar]
    exact valueSyntax_isSemiformula (substitution_covered_nth h (IsSemiterm.bvar.mp h.2.1))
  · rw [termSubst_fvar,valueSyntax_fvar]
    exact variableValue_isSemiformula h.1.2.2 (h.1.2.1.nth (lt_of_lt_of_le (var_lt_qqFvar i) h.2.2.1))
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    rw [termSubst_func hf hv]
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; rw [termSubstVec_nil,valueSyntax_zero]; exact zeroValue_isSemiformula h.1.2.2
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      rw [termSubstVec_cons₁ hu.isUTerm,valueSyntax_successor _ _ (h.2.2.2.1.termSubst hu).isUTerm]
      exact successorValue_isSemiformula h.1.2.2
        (ih u (unary_child_rank u) s r (n+1) _ w (substitution_covered_child h hu (unary_child_rank u)))
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := ih u (binary_left_rank f u v) s r ((n+1)+1) (binaryParameters param 1) w
        (substitution_covered_binary h huv.1 (binary_left_rank f u v) (by simp))
      have hb := ih v (binary_right_rank f u v) s r ((n+1)+1) (binaryParameters param 0) w
        (substitution_covered_binary h huv.2 (binary_right_rank f u v) (by simp))
      rw [termSubstVec_cons₂ huv.1.isUTerm huv.2.isUTerm]
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ (h.2.2.2.1.termSubst huv.1).isUTerm (h.2.2.2.1.termSubst huv.2).isUTerm]
        exact binaryValue_isSemiformula additionTemplate h.1.2.2 ha hb
      · rw [valueSyntax_multiplication _ _ _ (h.2.2.2.1.termSubst huv.1).isUTerm (h.2.2.2.1.termSubst huv.2).isUTerm]
        exact binaryValue_isSemiformula multiplicationTemplate h.1.2.2 ha hb

attribute [local irreducible] vectorSubstValidityInvariant
theorem valueSyntax_vectorSubst_isSemiformula {s r n param w t : V} (h : SubstitutionCovered s r n param w t) :
    IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t)) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s r n param w,
      SubstitutionCovered s r n param w t → IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t)) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s r n param w, SubstitutionCovered s r n param w t → IsSemiformula language n (valueSyntax param (termSubst Presentation.language w t))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb vectorSubstValidityInvariant,by trivial,?_⟩
      intro k; simpa using (vectorSubstValidity_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s r n param w h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact vectorSubstValidity_step k ih s r n param w h
      · exact ih t hlt s r n param w h
  exact hall (t+1) t (lt_add_one t) s r n param w h

#print axioms vectorSubstOutput_graph
#print axioms vectorSubstValidity_invariant
#print axioms vectorSubstValidity_step
#print axioms valueSyntax_vectorSubst_isSemiformula
end M6.PA.NumericPAeqTerm

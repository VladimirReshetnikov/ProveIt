module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermValidity
@[expose] public section

/-! Source singleton substitution arity from original source-code coverage only.
The substituted code is not assumed bounded by the finite free environment. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def sourceSubstValidGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “n param t u. ∃ w v, !adjoinDef w u 0 ∧
    !(termSubstGraph Presentation.language) v w t ∧ !outputValidGraph n param v”
theorem sourceSubstValid_graph (n param t u : V) :
    sourceSubstValidGraph.val.Evalb ![n,param,t,u] ↔
      IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] t)) := by
  simp [sourceSubstValidGraph,outputValid_graph,Matrix.comp_vecCons'']
noncomputable def sourceSubstValidityInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ n param u, !coverageGraph 0 n param u →
    !((isSemiterm Presentation.language).sigma) 1 t →
    ∀ f l, !nthDef f param 1 → !lenDef l f → t≤l → !sourceSubstValidGraph n param t u”
theorem sourceSubstValidity_invariant (k : V) : sourceSubstValidityInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ n param u, TermCovered 0 n param u → IsSemiterm Presentation.language 1 t →
      t≤len (nth param 1) →
      IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] t)) := by
  simp [sourceSubstValidityInvariant,coverage_graph,sourceSubstValid_graph,Matrix.comp_vecCons'']

private theorem sourceSubstValidity_step (t : V)
    (ih : ∀ v<t, ∀ n param u, TermCovered 0 n param u → IsSemiterm Presentation.language 1 v →
      v≤len (nth param 1) →
      IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] v))) :
    ∀ n param u, TermCovered 0 n param u → IsSemiterm Presentation.language 1 t →
      t≤len (nth param 1) →
      IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] t)) := by
  intro n param u h ht hb
  have hw : IsSemitermVec Presentation.language (1 : V) 0 ?[u] := IsSemitermVec.singleton.mpr h.2.1
  rcases IsUTerm.case_iff.mp ht.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · have hi : i=0 := by simpa using IsSemiterm.bvar.mp ht
    subst i
    simpa using valueSyntax_isSemiformula h
  · simp only [termSubst_fvar,valueSyntax_fvar]
    exact variableValue_isSemiformula h.1.2.2 (h.1.2.1.nth (lt_of_lt_of_le (var_lt_qqFvar i) hb))
  · have hsv := (IsSemiterm.func.mp ht).2
    rw [termSubst_func hf hv]
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; rw [termSubstVec_nil,valueSyntax_zero]; exact zeroValue_isSemiformula h.1.2.2
    · obtain ⟨v,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hv := IsSemitermVec.singleton.mp hsv
      have hc : TermCovered 0 (n+1) (childParameters param) u := by
        refine ⟨childParameters_valid h.1,h.2.1,?_⟩
        simpa only [childParameters,parameters_free,shiftTerms_length h.1.2.1] using h.2.2
      have hh := ih v (unary_child_rank v) (n+1) _ u hc hv
        (by simpa only [childParameters,parameters_free,shiftTerms_length h.1.2.1] using le_trans (unary_child_rank v).le hb)
      rw [termSubstVec_cons₁ hv.isUTerm,valueSyntax_successor _ _ (hw.termSubst hv).isUTerm]
      exact successorValue_isSemiformula h.1.2.2 hh
    · obtain ⟨v,w,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have hvw := IsSemitermVec.doubleton.mp hsv
      have hc (i:V) (hi:i<2) : TermCovered 0 ((n+1)+1) (binaryParameters param i) u := by
        refine ⟨binaryParameters_valid h.1 hi,h.2.1,?_⟩
        simpa only [binaryParameters,parameters_free,shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)] using h.2.2
      have ha := ih v (binary_left_rank f v w) ((n+1)+1) _ u (hc 1 (by simp)) hvw.1
        (by simpa only [binaryParameters,parameters_free,shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)] using le_trans (binary_left_rank f v w).le hb)
      have hb' := ih w (binary_right_rank f v w) ((n+1)+1) _ u (hc 0 (by simp)) hvw.2
        (by simpa only [binaryParameters,parameters_free,shiftTerms_length (shiftTerms_isSemitermVec h.1.2.1)] using le_trans (binary_right_rank f v w).le hb)
      rw [termSubstVec_cons₂ hvw.1.isUTerm hvw.2.isUTerm]
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ (hw.termSubst hvw.1).isUTerm (hw.termSubst hvw.2).isUTerm]
        exact binaryValue_isSemiformula additionTemplate h.1.2.2 ha hb'
      · rw [valueSyntax_multiplication _ _ _ (hw.termSubst hvw.1).isUTerm (hw.termSubst hvw.2).isUTerm]
        exact binaryValue_isSemiformula multiplicationTemplate h.1.2.2 ha hb'

attribute [local irreducible] sourceSubstValidityInvariant
theorem valueSyntax_sourceSubst_isSemiformula {n param t u : V}
    (h : TermCovered 0 n param u) (ht : IsSemiterm Presentation.language 1 t)
    (hb : t≤len (nth param 1)) :
    IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] t)) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ n param u, TermCovered 0 n param u → IsSemiterm Presentation.language 1 t →
      t≤len (nth param 1) →
      IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] t)) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ n param u, TermCovered 0 n param u → IsSemiterm Presentation.language 1 t →
        t≤len (nth param 1) →
        IsSemiformula language n (valueSyntax param (termSubst Presentation.language ?[u] t))) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb sourceSubstValidityInvariant,by trivial,?_⟩
      intro k; simpa using (sourceSubstValidity_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht n param u h hs hb
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact sourceSubstValidity_step k ih n param u h hs hb
      · exact ih t hlt n param u h hs hb
  exact hall (t+1) t (lt_add_one t) n param u h ht hb
theorem valueSyntax_singletonSubst_isSemiformula {n f t u z : V}
    (hf : IsSemitermVec language (len f) n f)
    (ht : IsSemiterm Presentation.language 1 t) (hu : IsSemiterm Presentation.language 0 u)
    (htBound : t≤len f) (huBound : u≤len f) (hz : IsSemiterm language n z) :
    IsSemiformula language n (valueSyntax (parameters 0 f z)
      (termSubst Presentation.language (u ∷ 0) t)) := by
  apply valueSyntax_sourceSubst_isSemiformula (u:=u)
  · exact ⟨by simpa [ParametersValid] using And.intro (show IsSemitermVec language 0 n (0:V) by simp) (And.intro hf hz), hu, by simpa using huBound⟩
  · exact ht
  · simpa using htBound
#print axioms valueSyntax_singletonSubst_isSemiformula
#print axioms sourceSubstValid_graph
#print axioms sourceSubstValidity_invariant
#print axioms valueSyntax_sourceSubst_isSemiformula
end M6.PA.NumericPAeqTerm

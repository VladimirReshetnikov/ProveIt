module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermCoverage
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
noncomputable def outputValidGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “n param t. ∃ out, !valueSyntaxGraph out param t ∧ !((isSemiformula language).sigma) n out”
theorem outputValid_graph (n param t : V) : outputValidGraph.val.Evalb ![n,param,t] ↔
    IsSemiformula language n (valueSyntax param t) := by
  simp [outputValidGraph,valueSyntax_graph,Matrix.comp_vecCons'']
noncomputable def validityInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n param, !coverageGraph s n param t → !outputValidGraph n param t”
theorem validity_invariant (k : V) : validityInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n param, TermCovered s n param t → IsSemiformula language n (valueSyntax param t) := by
  simp [validityInvariant,coverage_graph,outputValid_graph,Matrix.comp_vecCons'']

private theorem validity_step (t : V)
    (ih : ∀ u<t, ∀ s n param, TermCovered s n param u → IsSemiformula language n (valueSyntax param u)) :
    ∀ s n param, TermCovered s n param t → IsSemiformula language n (valueSyntax param t) := by
  intro s n param h
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · rw [valueSyntax_bvar]
    exact variableValue_isSemiformula h.1.2.2 (h.1.1.nth (IsSemiterm.bvar.mp h.2.1))
  · rw [valueSyntax_fvar]
    exact variableValue_isSemiformula h.1.2.2 (h.1.2.1.nth (lt_of_lt_of_le (var_lt_qqFvar i) h.2.2))
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; rw [valueSyntax_zero]; exact zeroValue_isSemiformula h.1.2.2
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      rw [valueSyntax_successor _ _ hu.isUTerm]
      exact successorValue_isSemiformula h.1.2.2
        (ih u (unary_child_rank u) s (n+1) _ (coverage_child h hu (unary_child_rank u)))
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := ih u (binary_left_rank f u v) s ((n+1)+1) (binaryParameters param 1)
        (coverage_binary_child h huv.1 (binary_left_rank f u v) (by simp))
      have hb := ih v (binary_right_rank f u v) s ((n+1)+1) (binaryParameters param 0)
        (coverage_binary_child h huv.2 (binary_right_rank f u v) (by simp))
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        exact binaryValue_isSemiformula additionTemplate h.1.2.2 ha hb
      · rw [valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        exact binaryValue_isSemiformula multiplicationTemplate h.1.2.2 ha hb

attribute [local irreducible] validityInvariant
theorem valueSyntax_isSemiformula {s n param t : V} (h : TermCovered s n param t) :
    IsSemiformula language n (valueSyntax param t) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n param,
      TermCovered s n param t → IsSemiformula language n (valueSyntax param t) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n param, TermCovered s n param t → IsSemiformula language n (valueSyntax param t)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb validityInvariant,by trivial,?_⟩
      intro k; simpa using (validity_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact validity_step k ih s n param h
      · exact ih t hlt s n param h
  exact hall (t+1) t (lt_add_one t) s n param h

#print axioms outputValid_graph
#print axioms validity_invariant
#print axioms validity_step
#print axioms valueSyntax_isSemiformula
end M6.PA.NumericPAeqTerm


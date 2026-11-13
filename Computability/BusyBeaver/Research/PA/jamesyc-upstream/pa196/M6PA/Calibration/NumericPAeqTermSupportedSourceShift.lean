module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceShiftParameters
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Source free shift compensated by a prepended target environment entry.
Only original source coverage is assumed; shifted code coverage is not assumed. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def supportedSourceShiftAgreementGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param x t. ∃ out shifted prep,
    !valueSyntaxGraph out param t ∧ !(termShiftGraph Presentation.language) shifted t ∧
    !prependFreeParametersGraph prep param x ∧ !valueSyntaxGraph out prep shifted”
theorem supportedSourceShiftAgreement_graph (param x t : V) :
    supportedSourceShiftAgreementGraph.val.Evalb ![param,x,t] ↔
      valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)=valueSyntax param t := by
  simp [supportedSourceShiftAgreementGraph,valueSyntax_graph,prependFreeParameters_graph,Matrix.comp_vecCons'',eq_comm]
noncomputable def supportedSourceShiftInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n param x, !supportedCoverageGraph s n param t →
    !((isSemiterm language).sigma) n x → !supportedSourceShiftAgreementGraph param x t”
theorem supportedSourceShift_invariant (k : V) : supportedSourceShiftInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
      valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)=valueSyntax param t := by
  simp [supportedSourceShiftInvariant,supportedCoverage_graph,supportedSourceShiftAgreement_graph,Matrix.comp_vecCons'']

private theorem supportedSourceShift_step (t : V)
    (ih : ∀ u<t, ∀ s n param x, SupportedTermCovered s n param u → IsSemiterm language n x →
      valueSyntax (prependFreeParameters param x) (termShift Presentation.language u)=valueSyntax param u) :
    ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
      valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)=valueSyntax param t := by
  intro s n param x h hx
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · simp [prependFreeParameters]
  · simp [prependFreeParameters]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    have hs := (freeSupported_func hf hv).mp h.2.2
    rw [termShift_func hf hv]
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; simp [prependFreeParameters]
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := supported_coverage_child h hu (by simpa using hs 0 (by simp))
      rw [termShiftVec_cons₁ hu.isUTerm,valueSyntax_successor _ _ hu.isUTerm.termShift,
        childParameters_prependFree h.1 hx,
        ih u (unary_child_rank u) s (n+1) _ _ hc hx.termBShift,
        valueSyntax_successor _ _ hu.isUTerm]
      simp [prependFreeParameters]
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := supported_coverage_binary_child h huv.1 (by simpa using hs 0 (by simp)) (show (1:V)<2 by simp)
      have hb := supported_coverage_binary_child h huv.2 (by simpa using hs 1 (by simp)) (show (0:V)<2 by simp)
      have ia := ih u (binary_left_rank f u v) s ((n+1)+1) _ _ ha hx.termBShift.termBShift
      have ib := ih v (binary_right_rank f u v) s ((n+1)+1) _ _ hb hx.termBShift.termBShift
      rw [termShiftVec_cons₂ huv.1.isUTerm huv.2.isUTerm]
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ huv.1.isUTerm.termShift huv.2.isUTerm.termShift,
          binaryParameters_prependFree h.1 hx,binaryParameters_prependFree h.1 hx,ia,ib,
          valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [prependFreeParameters]
      · rw [valueSyntax_multiplication _ _ _ huv.1.isUTerm.termShift huv.2.isUTerm.termShift,
          binaryParameters_prependFree h.1 hx,binaryParameters_prependFree h.1 hx,ia,ib,
          valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [prependFreeParameters]

attribute [local irreducible] supportedSourceShiftInvariant
theorem valueSyntax_supported_sourceShift {s n param t x : V} (h : SupportedTermCovered s n param t)
    (hx : IsSemiterm language n x) :
    valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)=valueSyntax param t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
      valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)=valueSyntax param t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
        valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)=valueSyntax param t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedSourceShiftInvariant,by trivial,?_⟩
      intro k; simpa using (supportedSourceShift_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n param x h hx
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact supportedSourceShift_step k ih s n param x h hx
      · exact ih t hlt s n param x h hx
  exact hall (t+1) t (lt_add_one t) s n param x h hx

theorem valueSyntax_supported_sourceShift_isSemiformula {s n param t x : V}
    (h : SupportedTermCovered s n param t) (hx : IsSemiterm language n x) :
    IsSemiformula language n (valueSyntax (prependFreeParameters param x) (termShift Presentation.language t)) := by
  rw [valueSyntax_supported_sourceShift h hx]
  exact valueSyntax_supported_isSemiformula h

#print axioms supportedSourceShiftAgreement_graph
#print axioms supportedSourceShift_invariant
#print axioms supportedSourceShift_step
#print axioms valueSyntax_supported_sourceShift
#print axioms valueSyntax_supported_sourceShift_isSemiformula
end M6.PA.NumericPAeqTerm


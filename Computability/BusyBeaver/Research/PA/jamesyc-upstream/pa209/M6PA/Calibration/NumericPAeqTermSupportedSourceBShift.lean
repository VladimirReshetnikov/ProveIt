module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermSourceBShiftParameters
public import M6PA.Calibration.NumericPAeqTermSupportedValidity
@[expose] public section

/-! Source bound shift compensated by a prepended target bound environment entry.
Only original source coverage is assumed; bound-shifted code coverage is not assumed. -/
namespace M6.PA.NumericPAeqTerm
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def supportedSourceBShiftAgreementGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “param x t. ∃ out shifted prep,
    !valueSyntaxGraph out param t ∧ !(termBShiftGraph Presentation.language) shifted t ∧
    !prependBoundParametersGraph prep param x ∧ !valueSyntaxGraph out prep shifted”
theorem supportedSourceBShiftAgreement_graph (param x t : V) :
    supportedSourceBShiftAgreementGraph.val.Evalb ![param,x,t] ↔
      valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)=valueSyntax param t := by
  simp [supportedSourceBShiftAgreementGraph,valueSyntax_graph,prependBoundParameters_graph,Matrix.comp_vecCons'',eq_comm]
noncomputable def supportedSourceBShiftInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ t<k, ∀ s n param x, !supportedCoverageGraph s n param t →
    !((isSemiterm language).sigma) n x → !supportedSourceBShiftAgreementGraph param x t”
theorem supportedSourceBShift_invariant (k : V) : supportedSourceBShiftInvariant.Evalb ![k] ↔
    ∀ t<k, ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
      valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)=valueSyntax param t := by
  simp [supportedSourceBShiftInvariant,supportedCoverage_graph,supportedSourceBShiftAgreement_graph,Matrix.comp_vecCons'']

private theorem supportedSourceBShift_step (t : V)
    (ih : ∀ u<t, ∀ s n param x, SupportedTermCovered s n param u → IsSemiterm language n x →
      valueSyntax (prependBoundParameters param x) (termBShift Presentation.language u)=valueSyntax param u) :
    ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
      valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)=valueSyntax param t := by
  intro s n param x h hx
  rcases IsUTerm.case_iff.mp h.2.1.isUTerm with ⟨i,rfl⟩|⟨i,rfl⟩|⟨k,f,ts,hf,hv,rfl⟩
  · simp [prependBoundParameters]
  · simp [prependBoundParameters]
  · have hsv := (IsSemiterm.func.mp h.2.1).2
    have hs := (freeSupported_func hf hv).mp h.2.2
    rw [termBShift_func hf hv]
    rcases (Presentation.source_functions k f).mp hf with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,htag⟩
    · have hz : ts=0 := IsUTermVec.empty_iff.mp hv
      subst ts; simp [prependBoundParameters]
    · obtain ⟨u,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have hu := IsSemitermVec.singleton.mp hsv
      have hc := supported_coverage_child h hu (by simpa using hs 0 (by simp))
      rw [termBShiftVec_cons₁ hu.isUTerm,valueSyntax_successor _ _ hu.isUTerm.termBShift,
        childParameters_prependBound h.1 hx,
        ih u (unary_child_rank u) s (n+1) _ _ hc hx.termBShift,
        valueSyntax_successor _ _ hu.isUTerm]
      simp [prependBoundParameters]
    · obtain ⟨u,v,_,_,rfl⟩ := IsUTermVec.two_iff.mp hv
      have huv := IsSemitermVec.doubleton.mp hsv
      have ha := supported_coverage_binary_child h huv.1 (by simpa using hs 0 (by simp)) (show (1:V)<2 by simp)
      have hb := supported_coverage_binary_child h huv.2 (by simpa using hs 1 (by simp)) (show (0:V)<2 by simp)
      have ia := ih u (binary_left_rank f u v) s ((n+1)+1) _ _ ha hx.termBShift.termBShift
      have ib := ih v (binary_right_rank f u v) s ((n+1)+1) _ _ hb hx.termBShift.termBShift
      rw [termBShiftVec_cons₂ huv.1.isUTerm huv.2.isUTerm]
      rcases htag with rfl|rfl
      · rw [valueSyntax_addition _ _ _ huv.1.isUTerm.termBShift huv.2.isUTerm.termBShift,
          binaryParameters_prependBound h.1 hx,binaryParameters_prependBound h.1 hx,ia,ib,
          valueSyntax_addition _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [prependBoundParameters]
      · rw [valueSyntax_multiplication _ _ _ huv.1.isUTerm.termBShift huv.2.isUTerm.termBShift,
          binaryParameters_prependBound h.1 hx,binaryParameters_prependBound h.1 hx,ia,ib,
          valueSyntax_multiplication _ _ _ huv.1.isUTerm huv.2.isUTerm]
        simp [prependBoundParameters]

attribute [local irreducible] supportedSourceBShiftInvariant
theorem valueSyntax_supported_sourceBShift {s n param t x : V} (h : SupportedTermCovered s n param t)
    (hx : IsSemiterm language n x) :
    valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)=valueSyntax param t := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ t<k, ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
      valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)=valueSyntax param t := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ t<k, ∀ s n param x, SupportedTermCovered s n param t → IsSemiterm language n x →
        valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)=valueSyntax param t) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedSourceBShiftInvariant,by trivial,?_⟩
      intro k; simpa using (supportedSourceBShift_invariant (V:=V) k).symm
    · intro t ht; exact False.elim (by simpa using ht)
    · intro k ih t ht s n param x h hx
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp ht) with he|hlt
      · subst t; exact supportedSourceBShift_step k ih s n param x h hx
      · exact ih t hlt s n param x h hx
  exact hall (t+1) t (lt_add_one t) s n param x h hx

theorem valueSyntax_supported_sourceBShift_isSemiformula {s n param t x : V}
    (h : SupportedTermCovered s n param t) (hx : IsSemiterm language n x) :
    IsSemiformula language n (valueSyntax (prependBoundParameters param x) (termBShift Presentation.language t)) := by
  rw [valueSyntax_supported_sourceBShift h hx]
  exact valueSyntax_supported_isSemiformula h

theorem valueSyntax_supported_sourceBShift_parameters {s n b f t x z : V}
    (hb : IsSemitermVec language s n b) (hf : IsSemitermVec language (len f) n f)
    (ht : IsSemiterm Presentation.language s t) (hsupport : FreeSupported (len f) t)
    (hx : IsSemiterm language n x) (hz : IsSemiterm language n z) :
    valueSyntax (parameters (x∷b) f z) (termBShift Presentation.language t)=valueSyntax (parameters b f z) t := by
  have h : SupportedTermCovered s n (parameters b f z) t :=
    ⟨by simpa [ParametersValid] using And.intro hb (And.intro hf hz),ht,by simpa using hsupport⟩
  simpa [prependBoundParameters] using valueSyntax_supported_sourceBShift h hx
#print axioms valueSyntax_supported_sourceBShift_parameters
#print axioms supportedSourceBShiftAgreement_graph
#print axioms supportedSourceBShift_invariant
#print axioms supportedSourceBShift_step
#print axioms valueSyntax_supported_sourceBShift
#print axioms valueSyntax_supported_sourceBShift_isSemiformula
end M6.PA.NumericPAeqTerm

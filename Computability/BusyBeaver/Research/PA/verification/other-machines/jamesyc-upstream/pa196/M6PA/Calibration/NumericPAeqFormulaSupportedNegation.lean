module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaNegationRules
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
@[expose] public section

/-! Exact NNF negation compatibility of the arithmetic-to-relational syntax
map in arbitrary PA models. This stage uses Foundation NNF on both sides;
the downstream relational-to-native stage separately needs certificate Bi. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph supportedCoverageGraph
noncomputable def supportedNegationGraph : 𝚺ᴬ₁.Semisentence 2 := .mkSigma
  “param p. ∃ np q nq targetNeg, !(negGraph Presentation.language) np p ∧
    !formulaSyntaxGraph q param p ∧ !formulaSyntaxGraph nq param np ∧
    !(negGraph language) targetNeg q ∧ nq=targetNeg”
theorem supportedNegation_graph (param p : V) : supportedNegationGraph.val.Evalb ![param,p] ↔
    formulaSyntax param (neg Presentation.language p)=neg language (formulaSyntax param p) := by
  simp [supportedNegationGraph,formulaSyntax_graph,Matrix.comp_vecCons'']
noncomputable def supportedNegationInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n param, !supportedCoverageGraph s n param p → !supportedNegationGraph param p”
theorem supportedNegation_invariant (bound : V) : supportedNegationInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p →
      formulaSyntax param (neg Presentation.language p)=neg language (formulaSyntax param p) := by
  simp [supportedNegationInvariant,supportedCoverage_graph,supportedNegation_graph,Matrix.comp_vecCons'']

private theorem supportedNegation_step (p : V)
    (ih : ∀ q<p, ∀ s n param, SupportedFormulaCovered s n param q →
      formulaSyntax param (neg Presentation.language q)=neg language (formulaSyntax param q)) :
    ∀ s n param, SupportedFormulaCovered s n param p →
      formulaSyntax param (neg Presentation.language p)=neg language (formulaSyntax param p) := by
  intro s n param h
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · rw [neg_rel hr ht.isUTerm,formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,
      formulaSyntax_rel _ _ _ _ hr ht.isUTerm]
  · have ha := supported_coverage_nrel h
    have hv := (atomCode_supported_isSemiformula (k := k) (r := r) h.1 ha.2.2.1 ha.2.2.2).isUFormula
    rw [neg_nrel hr ht.isUTerm,formulaSyntax_rel _ _ _ _ hr ht.isUTerm,
      formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,hv.neg_neg]
  · simp only [neg_verum,formulaSyntax_falsum,formulaSyntax_verum]
  · simp only [neg_falsum,formulaSyntax_falsum,formulaSyntax_verum]
  · have hc := supported_coverage_and h
    rw [neg_and hp.isUFormula hq.isUFormula,
      formulaSyntax_or _ _ _ hp.isUFormula.neg hq.isUFormula.neg,
      formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      neg_and (formulaSyntax_supported_isSemiformula hc.1).isUFormula (formulaSyntax_supported_isSemiformula hc.2).isUFormula,
      ih p (lt_K!_left p q) s n param hc.1,ih q (lt_K!_right p q) s n param hc.2]
  · have hc := supported_coverage_or h
    rw [neg_or hp.isUFormula hq.isUFormula,
      formulaSyntax_and _ _ _ hp.isUFormula.neg hq.isUFormula.neg,
      formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      neg_or (formulaSyntax_supported_isSemiformula hc.1).isUFormula (formulaSyntax_supported_isSemiformula hc.2).isUFormula,
      ih p (lt_or_left p q) s n param hc.1,ih q (lt_or_right p q) s n param hc.2]
  · have hc := supported_coverage_all h
    rw [neg_all hp.isUFormula,formulaSyntax_exs _ _ hp.isUFormula.neg,
      formulaSyntax_all _ _ hp.isUFormula,neg_guardedAllCode (formulaSyntax_supported_isSemiformula hc).isUFormula,
      ih p (lt_forall p) (s+1) (n+1) _ hc]
  · have hc := supported_coverage_exs h
    rw [neg_ex hp.isUFormula,formulaSyntax_all _ _ hp.isUFormula.neg,
      formulaSyntax_exs _ _ hp.isUFormula,neg_guardedExsCode (formulaSyntax_supported_isSemiformula hc).isUFormula,
      ih p (lt_exists p) (s+1) (n+1) _ hc]

attribute [local irreducible] supportedNegationInvariant
theorem formulaSyntax_supported_neg {s n param p : V} (h : SupportedFormulaCovered s n param p) :
    formulaSyntax param (neg Presentation.language p)=neg language (formulaSyntax param p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p →
      formulaSyntax param (neg Presentation.language p)=neg language (formulaSyntax param p) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p →
        formulaSyntax param (neg Presentation.language p)=neg language (formulaSyntax param p)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedNegationInvariant,by trivial,?_⟩
      intro bound; simpa using (supportedNegation_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact supportedNegation_step bound ih s n param h
      · exact ih p hlt s n param h
  exact hall (p+1) p (lt_add_one p) s n param h

theorem formulaSyntax_supported_imp {s n param p q : V}
    (hp : SupportedFormulaCovered s n param p) (hq : SupportedFormulaCovered s n param q) :
    formulaSyntax param (imp Presentation.language p q)=
      imp language (formulaSyntax param p) (formulaSyntax param q) := by
  change formulaSyntax param (qqOr (neg Presentation.language p) q)=
    qqOr (neg language (formulaSyntax param p)) (formulaSyntax param q)
  rw [formulaSyntax_or _ _ _ hp.2.1.isUFormula.neg hq.2.1.isUFormula,formulaSyntax_supported_neg hp]

#print axioms formulaSyntax_supported_imp
#print axioms supportedNegation_graph
#print axioms supportedNegation_invariant
#print axioms supportedNegation_step
#print axioms formulaSyntax_supported_neg
end M6.PA.NumericPAeqFormula


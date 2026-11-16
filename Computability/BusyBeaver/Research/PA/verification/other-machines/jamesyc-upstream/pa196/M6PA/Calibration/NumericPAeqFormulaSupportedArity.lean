module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSupportedAtomValidity
@[expose] public section

/-! Guarded arity preservation for arbitrary model-valued PAeq formulas,
proved by an explicit full-PA course-of-values invariant, not Nat induction. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph supportedCoverageGraph
noncomputable def supportedOutputValidGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “n param p. ∃ out, !formulaSyntaxGraph out param p ∧ !((isSemiformula language).sigma) n out”
theorem supportedOutputValid_graph (n param p : V) : supportedOutputValidGraph.val.Evalb ![n,param,p] ↔
    IsSemiformula language n (formulaSyntax param p) := by
  simp [supportedOutputValidGraph,formulaSyntax_graph,Matrix.comp_vecCons'']
noncomputable def supportedValidityInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n param, !supportedCoverageGraph s n param p → !supportedOutputValidGraph n param p”
theorem supportedValidity_invariant (bound : V) : supportedValidityInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p) := by
  simp [supportedValidityInvariant,supportedCoverage_graph,supportedOutputValid_graph,Matrix.comp_vecCons'']

private theorem supportedValidity_step (p : V)
    (ih : ∀ q<p, ∀ s n param, SupportedFormulaCovered s n param q → IsSemiformula language n (formulaSyntax param q)) :
    ∀ s n param, SupportedFormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p) := by
  intro s n param h
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · rw [formulaSyntax_rel _ _ _ _ hr ht.isUTerm]
    have ha := supported_coverage_rel h
    exact atomCode_supported_isSemiformula h.1 ha.2.2.1 ha.2.2.2
  · rw [formulaSyntax_nrel _ _ _ _ hr ht.isUTerm]
    have ha := supported_coverage_nrel h
    exact (atomCode_supported_isSemiformula h.1 ha.2.2.1 ha.2.2.2).neg
  · rw [formulaSyntax_verum]; simp
  · rw [formulaSyntax_falsum]; simp
  · rw [formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula]
    exact IsSemiformula.and.mpr ⟨ih p (lt_K!_left p q) s n param (supported_coverage_and h).1,
      ih q (lt_K!_right p q) s n param (supported_coverage_and h).2⟩
  · rw [formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula]
    exact IsSemiformula.or.mpr ⟨ih p (lt_or_left p q) s n param (supported_coverage_or h).1,
      ih q (lt_or_right p q) s n param (supported_coverage_or h).2⟩
  · rw [formulaSyntax_all _ _ hp.isUFormula]
    exact guardedAllCode_isSemiformula (ih p (lt_forall p) (s+1) (n+1) _ (supported_coverage_all h))
  · rw [formulaSyntax_exs _ _ hp.isUFormula]
    exact guardedExsCode_isSemiformula (ih p (lt_exists p) (s+1) (n+1) _ (supported_coverage_exs h))

attribute [local irreducible] supportedValidityInvariant
theorem formulaSyntax_supported_isSemiformula {s n param p : V} (h : SupportedFormulaCovered s n param p) :
    IsSemiformula language n (formulaSyntax param p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n param,
      SupportedFormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n param, SupportedFormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb supportedValidityInvariant,by trivial,?_⟩
      intro bound; simpa using (supportedValidity_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact supportedValidity_step bound ih s n param h
      · exact ih p hlt s n param h
  exact hall (p+1) p (lt_add_one p) s n param h

#print axioms supportedOutputValid_graph
#print axioms supportedValidity_invariant
#print axioms supportedValidity_step
#print axioms formulaSyntax_supported_isSemiformula
end M6.PA.NumericPAeqFormula


module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaAtomValidity
@[expose] public section

/-! Guarded arity preservation for arbitrary model-valued PAeq formulas,
proved by an explicit full-PA course-of-values invariant, not Nat induction. -/
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph coverageGraph
noncomputable def outputValidGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “n param p. ∃ out, !formulaSyntaxGraph out param p ∧ !((isSemiformula language).sigma) n out”
theorem outputValid_graph (n param p : V) : outputValidGraph.val.Evalb ![n,param,p] ↔
    IsSemiformula language n (formulaSyntax param p) := by
  simp [outputValidGraph,formulaSyntax_graph,Matrix.comp_vecCons'']
noncomputable def validityInvariant : ArithmeticSemisentence 1 :=
  “bound. ∀ p<bound, ∀ s n param, !coverageGraph s n param p → !outputValidGraph n param p”
theorem validity_invariant (bound : V) : validityInvariant.Evalb ![bound] ↔
    ∀ p<bound, ∀ s n param, FormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p) := by
  simp [validityInvariant,coverage_graph,outputValid_graph,Matrix.comp_vecCons'']

private theorem validity_step (p : V)
    (ih : ∀ q<p, ∀ s n param, FormulaCovered s n param q → IsSemiformula language n (formulaSyntax param q)) :
    ∀ s n param, FormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p) := by
  intro s n param h
  rcases IsSemiformula.case_iff.mp h.2.1 with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · rw [formulaSyntax_rel _ _ _ _ hr ht.isUTerm]
    have ha := coverage_rel h
    exact atomCode_isSemiformula h.1 ha.2.2.1 ha.2.2.2
  · rw [formulaSyntax_nrel _ _ _ _ hr ht.isUTerm]
    have ha := coverage_nrel h
    exact (atomCode_isSemiformula h.1 ha.2.2.1 ha.2.2.2).neg
  · rw [formulaSyntax_verum]; simp
  · rw [formulaSyntax_falsum]; simp
  · rw [formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula]
    exact IsSemiformula.and.mpr ⟨ih p (lt_K!_left p q) s n param (coverage_and h).1,
      ih q (lt_K!_right p q) s n param (coverage_and h).2⟩
  · rw [formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula]
    exact IsSemiformula.or.mpr ⟨ih p (lt_or_left p q) s n param (coverage_or h).1,
      ih q (lt_or_right p q) s n param (coverage_or h).2⟩
  · rw [formulaSyntax_all _ _ hp.isUFormula]
    exact guardedAllCode_isSemiformula (ih p (lt_forall p) (s+1) (n+1) _ (coverage_all h))
  · rw [formulaSyntax_exs _ _ hp.isUFormula]
    exact guardedExsCode_isSemiformula (ih p (lt_exists p) (s+1) (n+1) _ (coverage_exs h))

attribute [local irreducible] validityInvariant
theorem formulaSyntax_isSemiformula {s n param p : V} (h : FormulaCovered s n param p) :
    IsSemiformula language n (formulaSyntax param p) := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ bound : V, ∀ p<bound, ∀ s n param,
      FormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p) := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun bound : V =>
      ∀ p<bound, ∀ s n param, FormulaCovered s n param p → IsSemiformula language n (formulaSyntax param p)) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb validityInvariant,by trivial,?_⟩
      intro bound; simpa using (validity_invariant (V:=V) bound).symm
    · intro p hp; exact False.elim (by simpa using hp)
    · intro bound ih p hp s n param h
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p; exact validity_step bound ih s n param h
      · exact ih p hlt s n param h
  exact hall (p+1) p (lt_add_one p) s n param h

#print axioms outputValid_graph
#print axioms validity_invariant
#print axioms validity_step
#print axioms formulaSyntax_isSemiformula
end M6.PA.NumericPAeqFormula


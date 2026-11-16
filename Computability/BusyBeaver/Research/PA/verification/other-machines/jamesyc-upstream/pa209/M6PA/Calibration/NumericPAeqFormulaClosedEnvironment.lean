module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqTermClosedEnvironment
public import M6PA.Calibration.NumericPAeqFormulaSupportedArity
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] formulaSyntaxGraph parametersGraph freeSupportedGraph
noncomputable def closedEnvironmentGraph : 𝚺ᴬ₁.Semisentence 4 := .mkSigma
  “p b f g. ∃ x y out, !parametersGraph x b f ∧ !parametersGraph y b g ∧
    !formulaSyntaxGraph out x p ∧ !formulaSyntaxGraph out y p”
theorem closedEnvironment_graph (p b f g:V):closedEnvironmentGraph.val.Evalb ![p,b,f,g] ↔
    formulaSyntax (parameters b f) p=formulaSyntax (parameters b g) p := by
  simp [closedEnvironmentGraph,parameters_graph,formulaSyntax_graph,Matrix.comp_vecCons'']
attribute [local irreducible] closedEnvironmentGraph
noncomputable def closedEnvironmentInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ p<k, !freeSupportedGraph 0 p → ∀ b f g, !closedEnvironmentGraph p b f g”
theorem closedEnvironment_invariant (k:V):closedEnvironmentInvariant.Evalb ![k] ↔
    ∀p<k,FreeSupported 0 p→∀b f g,formulaSyntax (parameters b f) p=formulaSyntax (parameters b g) p := by
  simp [closedEnvironmentInvariant,freeSupported_graph,closedEnvironment_graph,Matrix.comp_vecCons'']
private theorem atom_closed_environment {k r ts:V} (hr:Presentation.language.IsRel k r)
    (ht:IsUTermVec Presentation.language k ts) (hs:∀i<k,NumericPAeqTerm.FreeSupported 0 (nth ts i)) (b f g:V):
    atomCode (parameters b f) k r ts=atomCode (parameters b g) k r ts := by
  obtain ⟨rfl,rfl⟩ :=(Presentation.source_relations k r).mp hr
  have h0 :=NumericPAeqTerm.valueSyntax_closed_environment (hs 0 (by simp))
    (NumericPAeqTerm.shiftTerms (NumericPAeqTerm.shiftTerms b)) (NumericPAeqTerm.shiftTerms (NumericPAeqTerm.shiftTerms f)) (NumericPAeqTerm.shiftTerms (NumericPAeqTerm.shiftTerms g)) (qqBvar 1)
  have h1 :=NumericPAeqTerm.valueSyntax_closed_environment (hs 1 (by simp))
    (NumericPAeqTerm.shiftTerms (NumericPAeqTerm.shiftTerms b)) (NumericPAeqTerm.shiftTerms (NumericPAeqTerm.shiftTerms f)) (NumericPAeqTerm.shiftTerms (NumericPAeqTerm.shiftTerms g)) (qqBvar 0)
  simpa [atomCode,equalityTermParameters,parameters] using congrArg₂ equalityCode h0 h1
private theorem closedEnvironment_step (p:V)
    (ih:∀q<p,FreeSupported 0 q→∀b f g,formulaSyntax (parameters b f) q=formulaSyntax (parameters b g) q)
    (h:FreeSupported 0 p):∀b f g,formulaSyntax (parameters b f) p=formulaSyntax (parameters b g) p := by
  intro b f g
  rcases IsSemiformula.case_iff.mp h.1.isSemiformula with
    ⟨k,r,ts,hr,ht,rfl⟩|⟨k,r,ts,hr,ht,rfl⟩|rfl|rfl|
    ⟨p,q,hp,hq,rfl⟩|⟨p,q,hp,hq,rfl⟩|⟨p,hp,rfl⟩|⟨p,hp,rfl⟩
  · rw [formulaSyntax_rel _ _ _ _ hr ht.isUTerm,formulaSyntax_rel _ _ _ _ hr ht.isUTerm,
      atom_closed_environment hr ht.isUTerm ((freeSupported_rel hr ht.isUTerm).mp h)]
  · rw [formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,formulaSyntax_nrel _ _ _ _ hr ht.isUTerm,
      atom_closed_environment hr ht.isUTerm ((freeSupported_nrel hr ht.isUTerm).mp h)]
  · simp only [formulaSyntax_verum]
  · simp only [formulaSyntax_falsum]
  · have hs :=(freeSupported_and hp.isUFormula hq.isUFormula).mp h
    rw [formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,formulaSyntax_and _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_K!_left p q) hs.1 b f g,ih q (lt_K!_right p q) hs.2 b f g]
  · have hs :=(freeSupported_or hp.isUFormula hq.isUFormula).mp h
    rw [formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,formulaSyntax_or _ _ _ hp.isUFormula hq.isUFormula,
      ih p (lt_or_left p q) hs.1 b f g,ih q (lt_or_right p q) hs.2 b f g]
  · rw [formulaSyntax_all _ _ hp.isUFormula,formulaSyntax_all _ _ hp.isUFormula]
    simpa [binderParameters,parameters] using congrArg guardedAllCode
      (ih p (lt_forall p) ((freeSupported_all hp.isUFormula).mp h)
        (qqBvar 0∷NumericPAeqTerm.shiftTerms b) (NumericPAeqTerm.shiftTerms f) (NumericPAeqTerm.shiftTerms g))
  · rw [formulaSyntax_exs _ _ hp.isUFormula,formulaSyntax_exs _ _ hp.isUFormula]
    simpa [binderParameters,parameters] using congrArg guardedExsCode
      (ih p (lt_exists p) ((freeSupported_exs hp.isUFormula).mp h)
        (qqBvar 0∷NumericPAeqTerm.shiftTerms b) (NumericPAeqTerm.shiftTerms f) (NumericPAeqTerm.shiftTerms g))
attribute [local irreducible] closedEnvironmentInvariant
theorem formulaSyntax_closed_environment {p:V} (h:FreeSupported 0 p) (b f g:V):
    formulaSyntax (parameters b f) p=formulaSyntax (parameters b g) p := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall :∀k:V,∀p<k,FreeSupported 0 p→∀b f g,formulaSyntax (parameters b f) p=formulaSyntax (parameters b g) p := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀p<k,FreeSupported 0 p→∀b f g,formulaSyntax (parameters b f) p=formulaSyntax (parameters b g) p) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb closedEnvironmentInvariant,by trivial,?_⟩
      intro k;simpa using (closedEnvironment_invariant (V:=V) k).symm
    · intro p hp;exact False.elim (by simpa using hp)
    · intro k ih p hp hs
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he|hlt
      · subst p;exact closedEnvironment_step k ih hs
      · exact ih p hlt hs
  exact hall (p+1) p (lt_add_one p) h b f g
#print axioms closedEnvironment_graph
#print axioms closedEnvironment_invariant
#print axioms formulaSyntax_closed_environment
end M6.PA.NumericPAeqFormula

